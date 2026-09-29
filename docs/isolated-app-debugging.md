# Isolated App Debugging

This guide captures the current debugging discipline for Rustlet entry,
return, and exception transitions.

Use it when:

- a Rustlet boots but crashes during `start()`, `install()`, or
  `process_apdu()`;
- the FAE `crt0` ABI changes;
- the isolated entry/return assembly changes;
- SVC, MemManage, PSP/MSP, or vector-table behavior becomes suspect.

## Start With a Proof Plan

Do not start by patching multiple layers at once.

First define which exact control-flow facts still need proof.

The current recommended sequence is:

1. `run_isolated_app` is reached.
2. The entry SVC is accepted from the privileged kernel call site.
3. Exception return reaches the Rustlet `crt0` on PSP.
4. The relocated payload entrypoint is reached.
5. The runtime issues `RETURN_TO_KERNEL` (`svc #1`).
6. The kernel SVC handler is entered.
7. The kernel resume path completes and returns to normal kernel code.

Until one step is proven, avoid changing the next layer.

## Use the Smallest Reproducer First

Start with the minimal scripted path before using the interactive APDU
flow.

Use the smallest automated APDU scenario on a native ELF kernel:

```bash
cargo run test rustlet mps2-an385 minimal_valid_test --on qemu --trace=semihosting
```

This exercises INSTALL, SELECT and the minimal Rustlet commands through the
QEMU UART transport. The historical `simulate_apdu` firmware mode is not the
runner used by this command. Start with this reproducible transcript before
adding richer Rustlet behavior or manual APDU exchanges.

The full Rustlet campaign also starts with `minimal_valid_test`.

## Address Rules That Matter

Three address forms appear in this workflow and must not be mixed:

- runtime code addresses in flash or RAM;
- Thumb-tagged branch targets and vector entries;
- actual memory addresses used by GDB breakpoints and disassembly.

Rule of thumb:

- use the odd Thumb form (`addr | 1`) for function pointers, exception
  vectors, and `bx`/`blx` targets;
- use the real even address for `break *...`, `x/i ...`, and raw memory
  inspection in GDB.

Example:

- branch/vector target: `0x200007c1`
- actual instruction address: `0x200007c0`

## Firmware Address Hygiene

For the native kernel, load symbols from the exact fixed-address ELF being
executed. Rustlet FAE symbols require a separate relocation calculation: their
ELF values need not equal the addresses at which the kernel loaded the FAE.
Keep both distinct from Thumb-tagged branch addresses.

Do not use a `kernel.gdbinit` left over from a legacy FAE kernel build for a
native ELF session. **FAE kernel images are no longer supported**; the kernel
`--fae` option is deprecated. Rustlet FAE images remain supported.

## QEMU + GDB Workflow

First run the minimal command above. It builds a native kernel ELF for QEMU
with the minimal Rustlet and semihosting traces. Use that exact
`target/kernel/firmware/kernel.elf` for the debugger session; do not rebuild a
different image between reproducing the issue and inspecting it.

Run QEMU frozen at reset with a GDB stub:

```bash
qemu-system-arm \
  -machine mps2-an385 \
  -nographic \
  -monitor none \
  -serial tcp:127.0.0.1:4444,server=on,wait=on \
  -semihosting-config enable=on,target=native \
  -S \
  -gdb tcp::33338 \
  -kernel target/kernel/firmware/kernel.elf
```

In another terminal, connect the APDU client before attaching GDB so QEMU
can finish opening its UART backend:

```bash
cargo run -p apdu_tool -- --atr-timeout infinite atr
```

The client waits for the ATR until execution resumes. In a third terminal,
attach GDB from `target/kernel/firmware/`:

```bash
arm-none-eabi-gdb -q
```

Then in GDB:

```gdb
file kernel.elf
target remote :33338
```

Set the breakpoints below, then `continue` to boot and deliver the ATR. Replay
the INSTALL/SELECT/process sequence from
[`run_rustlet_scenario`](../xtask/src/testing/scenarios/rustlets.rs) with
`apdu_tool`; increase `--response-timeout` for commands paused at breakpoints.
Preserve the same QEMU process and APDU session during the replay.

## Recommended First Breakpoints

Prefer runtime-address breakpoints over name-only breakpoints when both
the startup firmware and the kernel image expose similarly named code.

With kernel symbols loaded at their verified runtime addresses, start with:

```gdb
break oxi_core_run_isolated_app
break oxi_core_prepare_app_exception_frame
break oxi_core_resume_isolated_app
```

On ARMv6-M, use `oxi_core_armv6m_run_isolated_app` and
`oxi_core_armv6m_resume_isolated_app` for the first and last breakpoints.
There are no instructions or return gates in the shared ABI page.

## What To Inspect at Each Stage

At the launch wrapper, `r0` points to the kernel-owned `TargetAppEntry`:

```gdb
info registers sp msp psp control r0
x/7wx $r0
```

Its seven words are the entry PC, global pointer, four arguments, and stack top.
The wrapper executes `SVC 0` while still privileged on MSP. The handler accepts
this operation only from that exact kernel call site with an MSP Thread-mode
exception frame. Before the final `EXC_RETURN`, inspect the eight words at PSP:

```gdb
x/8wx $psp
```

They must contain the four arguments, zero R12/LR, an even FAE entry PC and
xPSR with Thumb state set. PSP is then `stack_top - 32`; hardware unstacking
restores the declared stack top and execution starts in unprivileged Thread
mode. The 512-byte exchange page stays read/write and execute-never.

During exception-entry debugging, inspect:

```gdb
info registers pc lr sp msp psp xpsr control
x/16wx 0xE000ED24
x/16wx 0x20006d80
```

This gives:

- active stack choice and privilege mode;
- fault-status registers (`SHCSR`, `CFSR`, `MMFAR`, ...);
- the current RAM vector-table contents.

Do not interpret a missing stacked PC/LR as address zero. Mainline fault
reporting omits them when CFSR indicates incomplete stacking. ARMv6-M
HardFault reporting also omits them because it cannot establish frame
completeness; fatal native startup fallbacks never dereference the failed stack.
Use debugger reads only after checking that the frame is within valid memory
and that exception stacking completed.

For a Rustlet return, inspect the SVC instruction in the Rustlet image and the
kernel's SVC vector/forwarding slot. The shared ABI page contains data only;
there is no executable return gate there. A fault before the Rust dispatcher
is reached points to vector resolution, exception entry or stack state.

## Discipline Rules

- Make one low-level change at a time, then re-run the same proof plan.
- Prefer the minimal automated APDU scenario before manual exchanges.
- Do not trust symbol names until their runtime addresses are validated.
- Record whether an address is: ELF-relative, runtime, or Thumb-tagged.
- For assembly/exception bugs, move to GDB early instead of relying on
  semihosting logs alone.
