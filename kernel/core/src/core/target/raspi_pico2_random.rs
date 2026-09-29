// Adapted from Raspberry Pi pico-sdk 2.2.0, pico_rand/rand.c:
// https://github.com/raspberrypi/pico-sdk/blob/2.2.0/src/rp2_common/pico_rand/rand.c
// Copyright (c) 2022 Raspberry Pi (Trading) Ltd.
// SPDX-License-Identifier: BSD-3-Clause
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
// 1. Redistributions of source code must retain the above copyright notice,
//    this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright notice,
//    this list of conditions and the following disclaimer in the documentation
//    and/or other materials provided with the distribution.
// 3. Neither the name of the copyright holder nor the names of its contributors
//    may be used to endorse or promote products derived from this software
//    without specific prior written permission.
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.

//! Checked RP2350 TRNG feeding HMAC-DRBG/SHA-256, owned only by the kernel.
//!
//! Fresh entropy is required before every nonempty call and every 1024 output
//! bytes. Exhausted health-check retries or timeouts latch a failure until boot.
//! No clock, SRAM, public identifier, stale state, or raw-output fallback exists.
//! Hardware checks and a DRBG do not establish a measured min-entropy bound.

use crate::core::crypto::hmac_drbg::HmacDrbg;
use crate::core::crypto::{CryptoError, CryptoResult};
use crate::core::secure_zero;
use crate::core::target::MmioRegister32;
use ::core::sync::atomic::{AtomicBool, Ordering};

const BASE: usize = 0x400f_0000;
const IMR: usize = 0x100;
const ISR: usize = 0x104;
const ICR: usize = 0x108;
const CONFIG: usize = 0x10c;
const VALID: usize = 0x110;
const EHR: usize = 0x114;
const ENABLE: usize = 0x12c;
const SAMPLE_COUNT: usize = 0x130;
const DEBUG: usize = 0x138;
const RESET: usize = 0x140;
const HEALTH_ERRORS: u32 = 0x0e;
const RESET_POLLS: usize = 1000;
const COLLECTION_POLLS: usize = 1_000_000;
const HEALTH_ATTEMPTS: usize = 8;
const GENERATE_BYTES: usize = 1024;

// Register semantics: RP2350 datasheet sections 12.12.2--12.12.5.
// https://datasheets.raspberrypi.com/rp2350/rp2350-datasheet.pdf
// Use chain 1, sampling interval 200 rng_clk cycles, all three tests enabled.
// The datasheet's 20--25 cycles are starting points, not an entropy guarantee.
// Embassy reports failures with a sleeping CPU at 25 and uses 200:
// https://github.com/embassy-rs/embassy/blob/main/embassy-rp/src/trng.rs
// This driver uses bounded polling, never WFE, and never bypasses health tests
// to recover. Eight rejected attempts cap recovery work; a timeout fails at
// once. Poll counts also bound failure when a hardware timebase stops.
const SAMPLE_CYCLES: u32 = 200;
const CHAIN: u32 = 1;

static LOCKED: AtomicBool = AtomicBool::new(false);
static mut STATE: RandomState = RandomState::new();

struct Guard {
    state: &'static mut RandomState,
}
impl Guard {
    fn acquire() -> CryptoResult<Self> {
        LOCKED
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .map(|_| {
                // SAFETY: a successful acquire is the only route to STATE.
                // The exclusive reference cannot outlive the guard's lock.
                Self {
                    state: unsafe { &mut *::core::ptr::addr_of_mut!(STATE) },
                }
            })
            .map_err(|_| CryptoError::EntropyUnavailable)
    }
}
impl Drop for Guard {
    fn drop(&mut self) {
        LOCKED.store(false, Ordering::Release);
    }
}

// Static dispatch lets host tests inject register behavior without introducing
// a diagnostic APDU, a raw-entropy syscall, or dynamic dispatch in production.
trait Registers {
    fn read(&mut self, offset: usize) -> u32;
    fn write(&mut self, offset: usize, value: u32);
}
/// Restricts testable driver offsets to the RP2350 TRNG register block.
fn register(offset: usize) -> MmioRegister32 {
    assert!(
        matches!(
            offset,
            IMR | ISR | ICR | CONFIG | VALID | ENABLE | SAMPLE_COUNT | DEBUG | RESET
        ) || (EHR..EHR + 24).contains(&offset) && offset.is_multiple_of(4)
    );
    // SAFETY: the checked offsets select aligned TRNG MMIO registers only.
    unsafe { MmioRegister32::new(BASE + offset) }
}
struct Hardware;
impl Registers for Hardware {
    fn read(&mut self, offset: usize) -> u32 {
        register(offset).read()
    }
    fn write(&mut self, offset: usize, value: u32) {
        register(offset).write(value);
    }
}

struct EntropySource {
    previous: [u8; 24],
    has_previous: bool,
}
impl EntropySource {
    const fn new() -> Self {
        Self {
            previous: [0; 24],
            has_previous: false,
        }
    }

    fn clear(&mut self) {
        secure_zero(&mut self.previous);
        self.has_previous = false;
    }

    fn configure(io: &mut impl Registers) -> CryptoResult<()> {
        io.write(ENABLE, 0);
        // AUTOCORR_ERR cannot be cleared by ICR: a reset is required.
        io.write(RESET, 1);
        // A soft reset is asynchronous. As in the Arm/Embassy initialization
        // sequence, wait for SAMPLE_CNT1 to accept writes, with a hard bound.
        for _ in 0..RESET_POLLS {
            io.write(SAMPLE_COUNT, SAMPLE_CYCLES);
            if io.read(SAMPLE_COUNT) == SAMPLE_CYCLES {
                io.write(CONFIG, CHAIN);
                io.write(DEBUG, 0);
                io.write(IMR, 0x0f); // mask interrupts; status is polled
                io.write(ICR, 0x0f);
                return Self::check_configuration(io);
            }
        }
        Err(CryptoError::EntropyUnavailable)
    }

    fn check_configuration(io: &mut impl Registers) -> CryptoResult<()> {
        if io.read(DEBUG) & 0x0e != 0
            || io.read(CONFIG) & 3 != CHAIN
            || io.read(SAMPLE_COUNT) != SAMPLE_CYCLES
        {
            return Err(CryptoError::EntropyUnavailable);
        }
        Ok(())
    }

    fn block(&mut self, io: &mut impl Registers, out: &mut [u8]) -> CryptoResult<()> {
        debug_assert_eq!(out.len(), 24);
        for _ in 0..HEALTH_ATTEMPTS {
            Self::configure(io)?;
            io.write(ENABLE, 1);
            let mut rejected = false;
            for _ in 0..COLLECTION_POLLS {
                let status = io.read(ISR);
                // An error always wins over VALID, even if both are set.
                // Discard the whole attempt, rather than crediting rejected bits.
                if status & HEALTH_ERRORS != 0 {
                    rejected = true;
                    break;
                }
                if status & 1 != 0 && io.read(VALID) & 1 != 0 {
                    Self::check_configuration(io)?;
                    if io.read(ISR) & HEALTH_ERRORS != 0 {
                        rejected = true;
                        break;
                    }
                    for (i, word) in out.chunks_exact_mut(4).enumerate() {
                        word.copy_from_slice(&io.read(EHR + i * 4).to_le_bytes());
                    }
                    // Read DATA5 last (it consumes the EHR and restarts sampling),
                    // then stop the source. The next acquisition starts afresh.
                    io.write(ENABLE, 0);
                    // Supplemental catastrophic-failure checks, not an entropy
                    // estimator or a replacement for the hardware raw-bit tests.
                    if out.iter().all(|b| *b == 0)
                        || out.iter().all(|b| *b == 0xff)
                        || (self.has_previous && out == self.previous)
                    {
                        return Err(CryptoError::EntropyUnavailable);
                    }
                    self.previous.copy_from_slice(out);
                    self.has_previous = true;
                    return Ok(());
                }
                ::core::hint::spin_loop();
            }
            io.write(ENABLE, 0);
            if !rejected {
                return Err(CryptoError::EntropyUnavailable);
            }
        }
        Err(CryptoError::EntropyUnavailable)
    }
}

struct RandomState {
    initialized: bool,
    ready: bool,
    seeded: bool,
    source: EntropySource,
    drbg: HmacDrbg,
}
impl RandomState {
    const fn new() -> Self {
        Self {
            initialized: false,
            ready: false,
            seeded: false,
            source: EntropySource::new(),
            drbg: HmacDrbg::new(),
        }
    }

    fn invalidate(&mut self, io: &mut impl Registers) {
        self.ready = false;
        self.seeded = false;
        self.drbg.clear();
        self.source.clear();
        io.write(ENABLE, 0);
    }

    fn generate(&mut self, io: &mut impl Registers, out: &mut [u8]) -> CryptoResult<()> {
        if !self.ready {
            return Err(CryptoError::EntropyUnavailable);
        }
        // 48 bytes from two accepted EHR blocks feed each reseed. Initial
        // instantiation additionally consumes a separate 24-byte nonce block.
        // For a 256-bit security claim these must provide >=256 and >=128 bits
        // of entropy respectively. Their byte lengths alone do NOT prove this;
        // RP2350 source characterization remains a separate qualification task.
        // HMAC-DRBG Update performs cryptographic mixing; it cannot create entropy.
        let mut seed = [0u8; 72];
        let result = (|| {
            for chunk in out.chunks_mut(GENERATE_BYTES) {
                let seed_len = if self.seeded { 48 } else { 72 };
                for block in seed[..seed_len].chunks_mut(24) {
                    self.source.block(io, block)?;
                }
                if self.seeded {
                    self.drbg.reseed(&seed[..48])?;
                } else {
                    self.drbg.instantiate(&seed[..48], &seed[48..])?;
                    self.seeded = true;
                }
                secure_zero(&mut seed);
                self.drbg.generate(chunk)?;
            }
            Ok(())
        })();
        secure_zero(&mut seed);
        result
    }

    fn fill(&mut self, io: &mut impl Registers, out: &mut [u8]) -> CryptoResult<()> {
        if out.is_empty() {
            return Ok(());
        }
        let result = self.generate(io, out);
        if result.is_err() {
            secure_zero(out); // also erase earlier chunks of a long request
            self.invalidate(io);
        }
        result
    }
}

pub(super) fn initialize() {
    let Ok(mut guard) = Guard::acquire() else {
        return;
    };
    let state = &mut guard.state;
    if state.initialized {
        return;
    } // never recover/reseed through reinitialization
    state.initialized = true;
    // SAFETY: RP2350 reset set/clear aliases and status register for the TRNG.
    unsafe { MmioRegister32::new(0x4002_2000) }.write(1 << 25);
    unsafe { MmioRegister32::new(0x4002_3000) }.write(1 << 25);
    for _ in 0..RESET_POLLS {
        if unsafe { MmioRegister32::new(0x4002_0008) }.read() & (1 << 25) != 0 {
            state.ready = EntropySource::configure(&mut Hardware).is_ok();
            return;
        }
        ::core::hint::spin_loop();
    }
}

pub(super) fn fill(out: &mut [u8]) -> CryptoResult<()> {
    if out.is_empty() {
        return Ok(());
    }
    let mut guard = Guard::acquire().inspect_err(|_| secure_zero(out))?;
    let state = &mut guard.state;
    state.fill(&mut Hardware, out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Default)]
    struct Fake {
        sample_count: u32,
        config: u32,
        debug: u32,
        enabled: bool,
        attempts: usize,
        blocks: usize,
        failed_attempts: usize,
        fail_after: Option<usize>,
        never_valid: bool,
        reset_stuck: bool,
        corrupt_config: bool,
        repeated: bool,
        zero: bool,
        health_bit: u32,
        reads: usize,
    }
    impl Registers for Fake {
        fn read(&mut self, offset: usize) -> u32 {
            // Exercise the hardware address boundary without dereferencing MMIO.
            let _ = register(offset);
            self.reads += 1;
            match offset {
                SAMPLE_COUNT => self.sample_count,
                CONFIG => self.config,
                DEBUG => {
                    if self.corrupt_config {
                        0x0e
                    } else {
                        self.debug
                    }
                }
                ISR => {
                    if self.attempts <= self.failed_attempts
                        || self.fail_after.is_some_and(|n| self.blocks >= n)
                    {
                        1 | self.health_bit.max(2) // deliberately simultaneous VALID
                    } else if self.never_valid {
                        0
                    } else {
                        1
                    }
                }
                VALID => u32::from(!self.never_valid),
                EHR..=0x128 => {
                    assert!(self.enabled);
                    assert!(self.attempts > self.failed_attempts);
                    let word = if self.zero {
                        0
                    } else {
                        0x1234_5678
                            ^ (offset as u32)
                            ^ if self.repeated {
                                0
                            } else {
                                (self.blocks as u32) << 8
                            }
                    };
                    if offset == 0x128 {
                        self.blocks += 1;
                    }
                    word
                }
                _ => panic!("unexpected read {offset:x}"),
            }
        }
        fn write(&mut self, offset: usize, value: u32) {
            let _ = register(offset);
            match offset {
                ENABLE => self.enabled = value != 0,
                RESET => self.attempts += 1,
                SAMPLE_COUNT => {
                    if !self.reset_stuck {
                        self.sample_count = value
                    }
                }
                CONFIG => self.config = value,
                DEBUG => self.debug = value,
                ICR | IMR => {}
                _ => panic!("unexpected write {offset:x}"),
            }
        }
    }
    fn ready() -> RandomState {
        let mut state = RandomState::new();
        state.initialized = true;
        state.ready = true;
        state
    }

    #[test]
    fn first_request_uses_nonce_and_every_request_reseeds() {
        let mut state = ready();
        let mut io = Fake::default();
        let mut first = [0; 33];
        let mut second = [0; 33];
        state.fill(&mut io, &mut first).unwrap();
        assert_eq!(io.blocks, 3);
        state.fill(&mut io, &mut second).unwrap();
        assert_eq!(io.blocks, 5);
        assert_ne!(first, second);
        state.fill(&mut io, &mut [0; GENERATE_BYTES + 1]).unwrap();
        assert_eq!(io.blocks, 9);
        assert!(!io.enabled);
    }

    #[test]
    fn failed_later_chunk_erases_the_entire_request_and_latches_failure() {
        let mut state = ready();
        let mut io = Fake {
            fail_after: Some(3),
            ..Fake::default()
        };
        let mut out = [0xff; GENERATE_BYTES + 1];
        assert_eq!(
            state.fill(&mut io, &mut out),
            Err(CryptoError::EntropyUnavailable)
        );
        assert_eq!(out, [0; GENERATE_BYTES + 1]);
        assert!(!state.ready);
        assert!(!state.seeded);
        assert!(!io.enabled);
        assert_eq!(state.source.previous, [0; 24]);
        let reads = io.reads;
        assert!(state.fill(&mut io, &mut out).is_err());
        assert_eq!(io.reads, reads); // no new entropy attempt after latched failure
    }

    #[test]
    fn each_health_error_wins_over_valid_and_retry_is_bounded() {
        for health_bit in [2, 4, 8] {
            let mut state = ready();
            let mut io = Fake {
                failed_attempts: 2,
                health_bit,
                ..Fake::default()
            };
            state.fill(&mut io, &mut [0; 1]).unwrap();
            assert_eq!(io.attempts, 5);
            assert_eq!(io.blocks, 3);
            let mut state = ready();
            let mut io = Fake {
                failed_attempts: usize::MAX,
                health_bit,
                ..Fake::default()
            };
            assert!(state.fill(&mut io, &mut [0; 1]).is_err());
            assert_eq!(io.attempts, HEALTH_ATTEMPTS);
            assert_eq!(io.blocks, 0);
        }
    }

    #[test]
    fn timeout_reset_failure_and_bypass_fail_closed() {
        for mut io in [
            Fake {
                never_valid: true,
                ..Fake::default()
            },
            Fake {
                reset_stuck: true,
                ..Fake::default()
            },
            Fake {
                corrupt_config: true,
                ..Fake::default()
            },
            Fake {
                repeated: true,
                ..Fake::default()
            },
            Fake {
                zero: true,
                ..Fake::default()
            },
        ] {
            let mut state = ready();
            let mut out = [0xff; 32];
            assert_eq!(
                state.fill(&mut io, &mut out),
                Err(CryptoError::EntropyUnavailable)
            );
            assert_eq!(out, [0; 32]);
            assert!(!state.ready);
            assert!(!io.enabled);
            assert!(io.reads < COLLECTION_POLLS + RESET_POLLS + 100);
        }
    }

    #[test]
    fn empty_call_does_not_consume_entropy_or_change_state() {
        let mut state = RandomState::new();
        let mut io = Fake::default();
        state.fill(&mut io, &mut []).unwrap();
        assert_eq!(io.reads, 0);
        assert!(!state.ready);
        assert!(state.fill(&mut io, &mut [0; 1]).is_err());
    }

    #[test]
    fn reentry_refuses_without_touching_owner_state() {
        let owner = Guard::acquire().unwrap();
        let mut out = [0xff; 16];
        assert_eq!(fill(&mut out), Err(CryptoError::EntropyUnavailable));
        assert_eq!(out, [0; 16]);
        assert!(LOCKED.load(Ordering::Relaxed));
        drop(owner);
        assert!(!LOCKED.load(Ordering::Relaxed));
    }
}
