use core::marker::PhantomData;

use crate::{ApduStatus, RustletCtx, APDU_PAYLOAD_LENGTH_MAX};

/// Clean command header exposed to Rustlet command logic.
///
/// The fifth APDU byte is intentionally not exposed here: it becomes `Lc` once
/// the command enters [`Receiving`], or `Le` once it enters [`Sending`].
#[derive(Clone, Copy)]
pub struct ApduHeader {
    /// Class byte, including any channel or secure-messaging bits.
    pub cla: u8,
    /// Instruction byte interpreted by the selected command handler.
    pub ins: u8,
    /// First instruction-specific parameter.
    pub p1: u8,
    /// Second instruction-specific parameter.
    pub p2: u8,
}

/// Initial APDU command state.
pub enum Command {}

/// APDU state after the incoming phase has been accepted.
pub enum Receiving {}

/// APDU state after the outgoing phase has been declared.
pub enum Sending {}

/// APDU state after the command has completed.
pub enum Done {}

/// Typed APDU session exposed to Rustlet code.
///
/// Methods are available only on the states where the APDU protocol allows
/// them. The raw shared ABI buffer remains hidden behind this state machine.
pub struct Apdu<'a, State> {
    raw: &'a mut RustletCtx,
    _state: PhantomData<State>,
}

impl<'a> Apdu<'a, Command> {
    /// Borrow the context exclusively for this command and clear any prior response.
    /// The caller must supply the active invocation's context, not a copied page.
    pub fn new(raw: &'a mut RustletCtx) -> Self {
        raw.clear_response();
        Self {
            raw,
            _state: PhantomData,
        }
    }

    /// Read the four command header bytes without receiving payload data.
    pub fn header(&self) -> ApduHeader {
        let header = self.raw.header();
        ApduHeader {
            cla: header.cla,
            ins: header.ins,
            p1: header.p1,
            p2: header.p2,
        }
    }

    /// Return the command's class byte.
    pub fn cla(&self) -> u8 {
        self.header().cla
    }

    /// Return the command's instruction byte.
    pub fn ins(&self) -> u8 {
        self.header().ins
    }

    /// Return the first command parameter.
    pub fn p1(&self) -> u8 {
        self.header().p1
    }

    /// Return the second command parameter.
    pub fn p2(&self) -> u8 {
        self.header().p2
    }

    /// Recognize exactly `CLA=00, INS=A4, P1=04`; does not validate P2 or the AID.
    pub fn is_select(&self) -> bool {
        let header = self.header();
        header.cla == 0x00 && header.ins == crate::INS_SELECT && header.p1 == 0x04
    }

    /// Test whether the header length byte is nonzero.
    /// This is not an APDU-case parser: an outgoing-only command's Le can also be
    /// nonzero. Choose the phase from your instruction's protocol.
    pub fn has_incoming(&self) -> bool {
        self.raw.lc() != 0
    }

    /// Consume this session and return `9000` without staging response bytes.
    pub fn accept(self) -> ApduStatus {
        ApduStatus::success()
    }

    /// Consume the command state and perform the incoming transport phase.
    /// May enter the kernel and wait for command data. Inspect `Receiving::data`
    /// on the returned session for the actual received payload.
    pub fn as_receiving(self) -> Apdu<'a, Receiving> {
        let _ = self.raw.set_incoming_and_receive();
        Apdu {
            raw: self.raw,
            _state: PhantomData,
        }
    }

    /// Consume the command state and declare an outgoing phase.
    /// The incoming payload is no longer available as incoming data. The shared
    /// bytes are reused for the response; no second payload buffer is allocated.
    pub fn as_sending(self) -> Apdu<'a, Sending> {
        self.raw.set_outgoing();
        Apdu {
            raw: self.raw,
            _state: PhantomData,
        }
    }

    /// Consume the session and return the supplied status without staging output.
    pub fn reject(self, status: ApduStatus) -> ApduStatus {
        status
    }
}

impl<'a> Apdu<'a, Receiving> {
    /// Return the command header's Lc interpretation, not the received slice length.
    pub fn lc(&self) -> usize {
        self.raw.lc() as usize
    }

    /// Borrow the received payload without copying it.
    /// The slice is bounded by the session borrow; use its length to validate
    /// received data. It cannot survive consuming the session for output.
    pub fn data(&self) -> &[u8] {
        self.raw.incoming_data()
    }

    /// End reception and reuse its payload storage for a response without copying.
    ///
    /// This consumes the receiving session and resets the logical output length,
    /// but preserves the bytes. Save the received length before this transition,
    /// then use [`Apdu::send_with`] to transform or publish that prefix. No input
    /// borrow may survive the transition. No heap allocation or additional
    /// payload buffer is introduced.
    /// As for the other APDU examples, the host doctest uses default features;
    /// an enabled `runtime` requires execution inside the active Rustlet.
    ///
    /// ```
    /// use rustlet_runtime::{Apdu, RustletApduHeader, RustletCtx};
    /// let mut ctx = RustletCtx::new();
    /// assert!(ctx.stage_command(RustletApduHeader {
    ///     cla: 0, ins: 8, p1: 0, p2: 0, lc: 3, le: 3,
    /// }, &[1, 2, 3]));
    /// let rx = Apdu::new(&mut ctx).as_receiving();
    /// let len = rx.data().len();
    /// let status = rx.as_sending().send_with(|buffer| {
    ///     buffer[..len].reverse();
    ///     len
    /// });
    /// assert_eq!(status.sw1, 0x90);
    /// assert_eq!(ctx.outgoing_data(), &[3, 2, 1]);
    /// ```
    ///
    /// ```compile_fail,E0505
    /// use rustlet_runtime::{Apdu, RustletCtx};
    /// let mut ctx = RustletCtx::new();
    /// let rx = Apdu::new(&mut ctx).as_receiving();
    /// let borrowed_input = rx.data();
    /// let tx = rx.as_sending();
    /// tx.send(borrowed_input); // The input loan cannot cross the phase change.
    /// ```
    ///
    /// ```compile_fail,E0382
    /// use rustlet_runtime::{Apdu, RustletCtx};
    /// let mut ctx = RustletCtx::new();
    /// let command = Apdu::new(&mut ctx);
    /// let receiving = command.as_receiving();
    /// command.as_sending(); // Reception consumed the command state.
    /// ```
    pub fn as_sending(self) -> Apdu<'a, Sending> {
        self.raw.set_outgoing();
        Apdu {
            raw: self.raw,
            _state: PhantomData,
        }
    }

    /// Consume this session and return `9000` without staging response bytes.
    pub fn accept(self) -> ApduStatus {
        ApduStatus::success()
    }

    /// Copy `data` into shared output and return `9000`.
    /// Returns `6700` without copying when data exceeds 255 bytes. An input slice
    /// borrowed from this same session cannot be passed while consuming it.
    pub fn accept_and_send(self, data: &[u8]) -> ApduStatus {
        stage_response(self.raw, data)
    }

    /// Consume the session and return the supplied status without staging output.
    pub fn reject(self, status: ApduStatus) -> ApduStatus {
        status
    }
}

impl Apdu<'_, Sending> {
    /// Return the raw short-APDU Le interpretation; zero is not expanded to 256.
    pub fn le(&self) -> usize {
        self.raw.le() as usize
    }

    /// Copy `data` into shared output and return `9000`, or `6700` above 255 bytes.
    /// The transport handles response delivery; this method stages bytes only.
    pub fn send(self, data: &[u8]) -> ApduStatus {
        stage_response(self.raw, data)
    }

    /// Generate response bytes directly in the shared buffer, without an extra copy.
    /// The closure receives all 256 physical bytes and returns the produced length.
    /// Only lengths up to 255 can be published: a larger result returns `6700`
    /// after the closure has run. Slice indexing in the closure can still panic.
    ///
    /// ```
    /// use rustlet_runtime::{Apdu, RustletCtx};
    /// let mut ctx = RustletCtx::new();
    /// let status = Apdu::new(&mut ctx).as_sending().send_with(|out| {
    ///     out[..3].copy_from_slice(&[0x10, 0x11, 0x12]);
    ///     3
    /// });
    /// assert_eq!(status.sw1, 0x90);
    /// assert_eq!(ctx.outgoing_data(), &[0x10, 0x11, 0x12]);
    /// ```
    /// This host example uses the default feature set; with `runtime` enabled the
    /// same sequence must execute within a kernel invocation.
    pub fn send_with(self, f: impl FnOnce(&mut [u8]) -> usize) -> ApduStatus {
        // Both constructors of Sending already declared the outgoing phase.
        // Its exclusive context loan prevents a phase change in between.
        let len = f(&mut self.raw.data);
        if len > APDU_PAYLOAD_LENGTH_MAX {
            return ApduStatus::wrong_length();
        }
        self.raw.set_outgoing_length(len);
        ApduStatus::success()
    }

    /// Consume the session and return the supplied status without staging output.
    pub fn reject(self, status: ApduStatus) -> ApduStatus {
        status
    }
}

impl Apdu<'_, Done> {
    /// Consume a completed session and return the supplied status.
    /// No public transition currently constructs the reserved `Done` state.
    pub fn status(self, status: ApduStatus) -> ApduStatus {
        status
    }
}

fn stage_response(raw: &mut RustletCtx, data: &[u8]) -> ApduStatus {
    if data.len() > APDU_PAYLOAD_LENGTH_MAX {
        return ApduStatus::wrong_length();
    }
    raw.set_outgoing();
    raw.data[..data.len()].copy_from_slice(data);
    raw.set_outgoing_length(data.len());
    ApduStatus::success()
}

/// Logical APDU header as seen by card-side command logic.
///
/// Under the current short APDU model, `p3` is the fifth command byte and is
/// interpreted as either `Lc` or `Le` depending on how the command later drives
/// the APDU session.
#[derive(Clone, Copy)]
pub struct SEApduHeader {
    /// Class byte, including any channel or secure-messaging bits.
    pub cla: u8,
    /// Instruction byte interpreted by the selected command handler.
    pub ins: u8,
    /// First instruction-specific parameter.
    pub p1: u8,
    /// Second instruction-specific parameter.
    pub p2: u8,
    /// Short-APDU length byte; interpreted by the incoming or outgoing phase.
    pub p3: u8,
}

/// Common card-side APDU processing interface.
///
/// This trait is the normalization point between kernel-side APDU handlers and
/// Rustlet-side APDU handlers. It intentionally models the APDU as seen by the
/// secure element while one command is being processed:
///
/// - the command header is already known;
/// - command logic may decide to receive incoming bytes;
/// - command logic may decide to prepare outgoing bytes.
///
/// In other words, `SEApdu` is not the low-level `T=0` transport object. The
/// transport loop remains responsible for procedure bytes, `6Cxx`, `61xx`,
/// `GET RESPONSE`, and final `SW1/SW2` emission. The trait only exposes the
/// command-processing surface shared by:
///
/// - the kernel-side APDU wrapper;
/// - the Rustlet ABI buffer;
/// - the kernel bridge object used while a Rustlet call is active.
///
/// The three primitive APDU transitions are:
///
/// - [`SEApdu::set_incoming_and_receive`], which performs the incoming data
///   phase;
/// - [`SEApdu::set_outgoing`], which declares an outgoing exchange and returns
///   the current `Le` interpretation;
/// - [`SEApdu::set_outgoing_length`], which declares how many response bytes
///   are available.
///
pub trait SEApdu {
    /// Returns the logical APDU header currently being processed.
    fn header(&self) -> SEApduHeader;

    /// Returns the mutable APDU payload buffer used for incoming or outgoing
    /// data staging.
    fn buffer_mut(&mut self) -> &mut [u8];

    /// Returns the incoming payload currently visible to command logic.
    fn incoming_data(&self) -> &[u8];

    /// Performs the incoming data phase and returns the number of bytes
    /// received. Repeated calls before output reuse the received payload.
    /// After output starts, returns zero without changing the response or
    /// reading the transport. Empty input emits no procedure byte.
    fn set_incoming_and_receive(&mut self) -> usize;

    /// Declares that the current command is an outgoing exchange and returns
    /// the current `Le` interpretation.
    fn set_outgoing(&mut self) -> usize;

    /// Declares how many outgoing bytes have been prepared in the APDU buffer.
    fn set_outgoing_length(&mut self, len: usize);

    /// Returns the `CLA` byte of the current command.
    fn cla(&self) -> u8 {
        self.header().cla
    }

    /// Returns the `INS` byte of the current command.
    fn ins(&self) -> u8 {
        self.header().ins
    }

    /// Returns the `P1` byte of the current command.
    fn p1(&self) -> u8 {
        self.header().p1
    }

    /// Returns the `P2` byte of the current command.
    fn p2(&self) -> u8 {
        self.header().p2
    }

    /// Returns the fifth command byte (`P3`), interpreted later as either
    /// `Lc` or `Le` depending on the APDU case.
    fn p3(&self) -> u8 {
        self.header().p3
    }
}

impl SEApdu for RustletCtx {
    fn header(&self) -> SEApduHeader {
        let header = self.header();
        SEApduHeader {
            cla: header.cla,
            ins: header.ins,
            p1: header.p1,
            p2: header.p2,
            p3: header.lc,
        }
    }

    fn buffer_mut(&mut self) -> &mut [u8] {
        &mut self.data
    }

    fn incoming_data(&self) -> &[u8] {
        self.incoming_data()
    }

    fn set_incoming_and_receive(&mut self) -> usize {
        self.set_incoming_and_receive()
    }

    fn set_outgoing(&mut self) -> usize {
        self.set_outgoing();
        self.le() as usize
    }

    fn set_outgoing_length(&mut self, len: usize) {
        self.set_outgoing_length(len);
    }
}
