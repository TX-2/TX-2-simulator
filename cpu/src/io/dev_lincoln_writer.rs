//! Lincoln Writer, units 65, 71 (input), 66, 72 (output).
//!
//! A TX-2 unit is always either for input or output, not both
//! (consider for example that the TSD instruction specifies no
//! direction - it is implicit).
//!
///! I am not sure about the timing characteristics of this
///! device.  For now we'll simply assume the output speed is
///! comparable with that of the IBM Selectric typewriter, which is
///! 14.8 characters per second.  This works out at roughly 68
///! milliseconds per character.
use std::cell::RefCell;
use std::fmt::Debug;
use std::rc::Rc;
use std::time::Duration;

use super::super::context::Context;
use super::super::event::{InputEvent, InputEventError, OutputEvent};
use super::super::io::{FlagChange, TransferFailed, Unit, UnitStatus};
use super::super::types::*;
use super::super::{Alarm, AlarmDetails};
use base::charset::LincolnStateTextInfo;
use base::charset::{lincoln_char_to_described_char, lincoln_writer_state_update, LincolnState};
use base::prelude::*;
use tracing::{event, Level};

#[cfg(test)]
use base::charset::{Colour, DescribedChar, LincolnChar, Script};

const CHAR_TRANSMIT_TIME: Duration = Duration::from_millis(68);
const LATER: Duration = Duration::from_secs(300);

#[derive(Debug)]
pub(crate) struct LincolnWriterOutput {
    unit: Unsigned6Bit,
    mode: Unsigned12Bit,
    connected: bool,
    transmit_will_be_finished_at: Option<Duration>,
    state: Rc<RefCell<LincolnState>>,
}

impl LincolnWriterOutput {
    pub(crate) fn new(unit: Unsigned6Bit, state: Rc<RefCell<LincolnState>>) -> LincolnWriterOutput {
        LincolnWriterOutput {
            unit,
            mode: Unsigned12Bit::ZERO,
            connected: false,
            transmit_will_be_finished_at: None,
            state,
        }
    }

    fn lw_number(&self) -> u8 {
        match u8::from(self.unit) {
            0o66 => 1,
            0o72 => 2,
            n => n,
        }
    }

    fn make_alarm(&self, details: AlarmDetails) -> Alarm {
        Alarm {
            sequence: Some(self.unit),
            details,
        }
    }
}

impl Unit for LincolnWriterOutput {
    fn poll(&mut self, ctx: &Context) -> UnitStatus {
        let (transmitting, next_poll) = match self.transmit_will_be_finished_at {
            Some(d) if d > ctx.simulated_time => {
                event!(
                    Level::TRACE,
                    "still transmitting; remaining transmit time is {:?}",
                    d - ctx.simulated_time
                );
                (true, d)
            }
            None => {
                event!(Level::TRACE, "no transmit has yet been started");
                (false, ctx.simulated_time + LATER)
            }
            Some(d) => {
                event!(
                    Level::TRACE,
                    "transmission completed {:?} ago, ready to transmit",
                    (ctx.simulated_time - d)
                );
                (false, ctx.simulated_time + LATER)
            }
        };
        // next_poll is far in the future if we are already ready to
        // transmit, since we're raising the flag now.  No need to
        // poll us again to discover we're still ready.
        let change_flag = if !self.connected || transmitting {
            None
        } else {
            Some(FlagChange::Raise)
        };
        event!(
            Level::TRACE,
            "connected: {}, flag: {:?}",
            self.connected,
            change_flag
        );
        UnitStatus {
            special: Unsigned12Bit::ZERO,
            change_flag,
            buffer_available_to_cpu: !transmitting,
            inability: false,
            missed_data: false,
            mode: self.mode,
            poll_after: next_poll,
            is_input_unit: false,
        }
    }

    fn connect(&mut self, _ctx: &Context, mode: base::Unsigned12Bit) {
        event!(Level::INFO, "{} connected", self.name(),);
        self.connected = true;
        self.mode = mode;
    }

    fn read(&mut self, _ctx: &Context) -> Result<MaskedWord, TransferFailed> {
        unreachable!("attempted to read from an output device")
    }

    fn write(
        &mut self,
        ctx: &Context,
        source: base::Unsigned36Bit,
    ) -> Result<Option<OutputEvent>, TransferFailed> {
        match self.state.try_borrow_mut() {
            Ok(mut state) => {
                match self.transmit_will_be_finished_at {
                    Some(t) if t > ctx.simulated_time => {
                        event!(
                            Level::DEBUG,
                            "cannot complete TSD, we are already transmitting"
                        );
                        return Err(TransferFailed::BufferNotFree);
                    }
                    None => {
                        event!(Level::TRACE, "this is the unit's first transmit operation");
                    }
                    Some(then) => {
                        let idle_for = ctx.simulated_time - then;
                        event!(
                            Level::TRACE,
                            "ready to transmit more data (and have been for {idle_for:?}"
                        );
                    }
                }
                let done_at = ctx.simulated_time + CHAR_TRANSMIT_TIME;
                event!(
                    Level::DEBUG,
                    "beginning new transmit operation at {:?}, it will complete at {:?}",
                    &ctx.simulated_time,
                    &done_at
                );
                self.transmit_will_be_finished_at = Some(done_at);
                let char_data = Unsigned6Bit::try_from(u64::from(source) & 0o77)
                    .expect("item should only have six value bits (this is a bug)");
                match lincoln_char_to_described_char(char_data, &mut state) {
                    None => Ok(None),
                    Some(described_char) => Ok(Some(OutputEvent::LincolnWriterPrint {
                        unit: self.unit,
                        ch: described_char,
                    })),
                }
            }
            Err(e) => Err(TransferFailed::Alarm(self.make_alarm(AlarmDetails::BUGAL {
                    instr: None,
                    message: format!(
                        "attempted to transmit on unit {:o} while the Lincoln Writer state is being mutated by receive path: {e}",
                        self.unit,
                    )
            })))
        }
    }

    fn name(&self) -> String {
        format!("Lincoln Writer output {:2o}", self.lw_number())
    }

    fn transfer_mode(&self) -> crate::TransferMode {
        TransferMode::Exchange
    }

    fn disconnect(&mut self, _ctx: &Context) {
        self.connected = false;
    }

    fn on_input_event(
        &mut self,
        _ctx: &Context,
        _event: crate::event::InputEvent,
    ) -> Result<(), InputEventError> {
        // Does nothing
        Ok(())
    }

    fn text_info(&self, _ctx: &Context) -> String {
        // Don't indicate connected/disconnected, because that is
        // shown separately.
        let maybe_transmitting = if self.transmit_will_be_finished_at.is_some() {
            "Transmitting."
        } else {
            "Idle."
        };
        match self.state.try_borrow() {
            Ok(state) => {
                let info: LincolnStateTextInfo = (&*state).into();
                format!(
                    "{} {}. {}. {}.",
                    maybe_transmitting, info.script, info.case, info.colour
                )
            }
            Err(_) => maybe_transmitting.to_string(),
        }
    }
}

#[cfg(test)]
fn check_output(
    writer: &mut LincolnWriterOutput,
    when: Duration,
    out: Unsigned6Bit,
    expected_output: &Option<DescribedChar>,
    expected_state: &LincolnState,
    actual_state: &Rc<RefCell<LincolnState>>,
) {
    let context = Context {
        simulated_time: when,
        real_elapsed_time: when,
    };
    match (expected_output, writer.write(&context, out.into())) {
        (Some(expected_output), Ok(Some(OutputEvent::LincolnWriterPrint { unit: _, ch }))) => {
            if &ch != expected_output {
                panic!("output of code {out:o} expected to generate character {expected_output:?}, actually generated {ch:?}");
            }
        }
        (None, Ok(None)) => (),
        (Some(expected), Ok(None)) => {
            panic!("printing code {out:o} produced no output event, but should have produced {expected:?}");
        }
        (None, Ok(Some(actual))) => {
            panic!("printing code {out:o} should have produced no output event, but actually produced {actual:?}");
        }
        (_, Err(e)) => {
            panic!("output transfer failed {e:?}");
        }
    }
    let actual = actual_state.borrow();
    if &*actual != expected_state {
        panic!("output of code {out:o} expected to generate state {expected_state:?}, actual state is {actual:?}");
    }
}

#[test]
fn lw_output_space() {
    let unit = u6!(0o66);
    let state = Rc::new(RefCell::new(LincolnState::default()));
    let mut lw_out = LincolnWriterOutput::new(unit, state.clone());

    check_output(
        &mut lw_out,
        Duration::from_millis(0),
        u6!(0o70), // SPACE
        &Some(DescribedChar {
            base_char: LincolnChar::UnicodeBaseChar(' '),
            unicode_representation: Some(' '),
            attributes: LincolnState {
                script: Script::Normal,
                uppercase: false,
                colour: Colour::Black,
            },
            advance: true,
            label_matches_unicode: false,
        }),
        &LincolnState::default(),
        &state,
    );
}

#[test]
fn lw_output_cr_resets_state() {
    let unit = u6!(0o66);
    let state = Rc::new(RefCell::new(LincolnState::default()));
    let mut lw_out = LincolnWriterOutput::new(unit, state.clone());

    check_output(
        &mut lw_out,
        Duration::from_millis(100),
        u6!(0o64), // SUPER
        &None,     // no output for this char
        &LincolnState {
            script: Script::Super,
            uppercase: false,
            colour: Colour::Black,
        },
        &state,
    );
    check_output(
        &mut lw_out,
        Duration::from_millis(200),
        u6!(0o67), // COLOR RED
        &None,     // no output for this char
        &LincolnState {
            script: Script::Super, // unchanged
            uppercase: false,
            colour: Colour::Red,
        },
        &state,
    );
    check_output(
        &mut lw_out,
        Duration::from_millis(300),
        u6!(0o26), // G
        &Some(DescribedChar {
            base_char: LincolnChar::UnicodeBaseChar('G'),
            unicode_representation: Some('ᴳ'),
            attributes: LincolnState {
                script: Script::Super,
                uppercase: false,
                colour: Colour::Red,
            },
            advance: true,
            label_matches_unicode: true,
        }),
        &LincolnState {
            script: Script::Super,
            uppercase: false,
            colour: Colour::Red,
        },
        &state,
    );

    // Now we emit a newline which should reset the script and case
    // state, but not the colour.
    check_output(
        &mut lw_out,
        Duration::from_millis(400),
        u6!(0o60), // CAR RETURN
        &Some(DescribedChar {
            base_char: LincolnChar::UnicodeBaseChar('\r'),
            unicode_representation: Some('\r'),
            attributes: LincolnState {
                script: Script::Normal,
                uppercase: false,
                // colour is not reset, per the Users Guide
                // (in the description of sequences 65,66).
                colour: Colour::Red,
            },
            advance: true,
            label_matches_unicode: false,
        }),
        &LincolnState {
            script: Script::Normal,
            uppercase: false,
            colour: Colour::Red,
        },
        &state,
    );
}

#[derive(Debug)]
pub(crate) struct LincolnWriterInput {
    unit: Unsigned6Bit,
    mode: Unsigned12Bit,
    connected: bool,
    data: Vec<Unsigned6Bit>,
    state: Rc<RefCell<LincolnState>>,
}

impl LincolnWriterInput {
    pub(crate) fn new(unit: Unsigned6Bit, state: Rc<RefCell<LincolnState>>) -> LincolnWriterInput {
        LincolnWriterInput {
            unit,
            mode: Unsigned12Bit::ZERO,
            connected: false,
            data: Vec::new(),
            state,
        }
    }

    fn lw_number(&self) -> u8 {
        match u8::from(self.unit) {
            0o65 => 1,
            0o71 => 2,
            n => n,
        }
    }
}

impl Unit for LincolnWriterInput {
    fn poll(&mut self, ctx: &Context) -> UnitStatus {
        let data_available = !self.data.is_empty();
        let change_flag: Option<FlagChange> = if self.connected {
            if data_available {
                event!(
                    Level::DEBUG,
                    "LW input {:o}: connected and data is ready; raising flag",
                    self.unit
                );
                Some(FlagChange::Raise) // data is ready, raise flag
            } else {
                event!(
                    Level::TRACE,
                    "LW input {:o}: connected but no data ready, will not raise flag",
                    self.unit
                );
                None // no data ready, so don't raise flag
            }
        } else {
            event!(
                Level::TRACE,
                "LW input {:o}: not connected, will not raise flag",
                self.unit
            );
            None // no flag raise since not connected
        };

        UnitStatus {
            special: Unsigned12Bit::ZERO,
            change_flag,
            buffer_available_to_cpu: self.connected && data_available,
            inability: false,
            missed_data: false,
            mode: self.mode,
            // Our input processing is driven by calls to
            // DeviceManager::on_input_event() which will result in
            // flag raises when necessary.  So there is no need to
            // call poll() in order to detect input becoming evailable
            // and so we provide long poll_after values.
            poll_after: ctx.simulated_time + LATER,
            is_input_unit: true,
        }
    }

    fn text_info(&self, _ctx: &Context) -> String {
        // Don't show connected/disconnected state here, as that is
        // shown separately.
        if self.data.is_empty() {
            "Idle."
        } else {
            "Input available."
        }
        .to_string()
    }

    fn connect(&mut self, _ctx: &Context, mode: Unsigned12Bit) {
        self.mode = mode;
        self.connected = true;
    }

    fn disconnect(&mut self, _ctx: &Context) {
        self.connected = false;
    }

    fn transfer_mode(&self) -> TransferMode {
        TransferMode::Exchange
    }

    fn read(&mut self, _ctx: &Context) -> Result<MaskedWord, TransferFailed> {
        event!(
            Level::DEBUG,
            "read from LW input device having state {self:?}"
        );
        if self.data.is_empty() {
            Err(TransferFailed::BufferNotFree)
        } else {
            Ok(MaskedWord {
                bits: Unsigned36Bit::from(self.data.remove(0)),
                mask: u36!(0o77),
            })
        }
    }

    fn write(
        &mut self,
        _ctx: &Context,
        _source: Unsigned36Bit,
    ) -> Result<Option<OutputEvent>, TransferFailed> {
        unreachable!("attempted to write to an input device")
    }

    fn name(&self) -> String {
        format!("Lincoln Writer input {:2o}", self.lw_number())
    }

    // The send and receive processes involve different units but
    // share the upper/lower case state within the lincoln writer.
    //
    // This implementation is not quite right because we don't emulate
    // a receive interval between the case-change code and the key
    // code that follows it.  Consier these codes:
    //
    //     Lower case    / Upper case
    // 20: A             /  ≈
    // 21: B             /  ⊂
    // 22: C             /  ∨
    // 23: D             /  q
    // 74: LOWER CASE
    // 75: UPPER CASE
    //
    // Suppose a program generates these codes for output: 75  20  74  21.
    // Suppose these codes arrive on input: 74  22  75  23.
    //
    // The streams would likely take effect in this order, where no
    // output occurs between the successive pairs of input characters.
    //
    // Output codes: 75,      20,     74, 21
    // Input unit:      74,22,   75,23
    //
    // This would output "AB" and input "Cq", perhaps not what was expected.
    //
    fn on_input_event(
        &mut self,
        _ctx: &Context,
        event: crate::InputEvent,
    ) -> Result<(), InputEventError> {
        event!(
            Level::DEBUG,
            "LW input {:o} processing input event: {:?}",
            self.unit,
            &event
        );
        let result = if let InputEvent::LwKeyboardInput { data } = event {
            match (self.data.is_empty(), data.as_slice()) {
                (_, []) => Ok(()),
                (false, _) => Err(InputEventError::BufferUnavailable),
                (true, [items @ ..]) => {
                    match self.state.try_borrow_mut() {
                        Ok(mut state) => {
                            self.data.clear();
                            for item in items.iter() {
                                // Deal with any state changes.
                                // Because all state changes occur in
                                // one go, we may get the unexpected
                                // behaviour described in the comment
                                // above.
                                lincoln_writer_state_update(*item, &mut state);
                                self.data.push(*item);
                            }
                            Ok(())
                        }
                        Err(_) => Err(InputEventError::InvalidReentrantCall),
                    }
                }
            }
        } else {
            Err(InputEventError::InputEventNotValidForDevice)
        };
        event!(
            Level::DEBUG,
            "LW input {:o} completing input event, data is now {:?}, result is {:?}",
            self.unit,
            self.data,
            &result
        );
        result
    }
}
