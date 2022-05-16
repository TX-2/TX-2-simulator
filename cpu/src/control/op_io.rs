use std::ops::BitAnd;

use base::prelude::*;
use std::time::Duration;

use tracing::{event, Level};

use super::super::*;
use crate::alarm::{Alarm, AlarmUnit, BadMemOp};
use crate::control::{
    ControlRegisters, ControlUnit, DeviceManager, OpcodeResult, ProgramCounterChange, TrapCircuit,
};
use crate::exchanger::exchanged_value_for_load;
use crate::io::Unit;
use crate::memory::{MemoryMapped, MemoryOpFailure, MemoryUnit, MetaBitChange};

#[derive(Debug, PartialEq, Eq)]
enum TransferOutcome {
    /// When the outcome is successful, let the caller know if the
    /// memory location's meta bit was set.  This allows the trap
    /// circuit to be triggered if necessary.
    Success(bool),

    /// When the outcome of the TSD is dismiss and wait, we don't
    /// trigger the trap circuit (not because we think the TX-2 behaved
    /// this way, but because it keeps the code simpler and we don't
    /// know if the oposite behaviour is needed).
    DismissAndWait,
}

type OpConversion = fn(Address) -> BadMemOp;

fn bad_write(addr: Address) -> BadMemOp {
    BadMemOp::Write(addr.into())
}

impl ControlUnit {
    /// Implements the IOS opcode
    pub(crate) fn op_ios(
        &mut self,
        devices: &mut DeviceManager,
        system_time: &Duration,
    ) -> Result<OpcodeResult, Alarm> {
        let j = self.regs.n.index_address();
        let cf = self.regs.n.configuration();

        if cf & 1 != 0 {
            // Setting the report bit in the configuration value
            // causes the device's status word from before any mode
            // change to be copied into the E register.  (as stated in
            // section 4-3.6 of the User Handbook).
            let flag_raised: bool = self.regs.flags.current_flag_state(&j);
            self.regs.e = devices.report(system_time, j, flag_raised, &self.alarm_unit)?;
        }
        let mut dismiss_reason: Option<&str> = if cf & 0o20 != 0 {
            Some("dismiss bit set in config")
        } else {
            None
        };

        let operand = self.regs.n.operand_address_and_defer_bit();
        let result = match u32::from(operand) {
            0o20_000 => devices.disconnect(&j, &self.alarm_unit),
            0o30_000..=0o37_777 => {
                let mode: Unsigned12Bit = Unsigned12Bit::try_from(operand & 0o07_777).unwrap();
                ControlUnit::connect_unit(
                    devices,
                    &mut self.regs,
                    &mut self.trap,
                    system_time,
                    j,
                    mode,
                    &self.alarm_unit,
                )
            }
            0o40_000 => {
                self.regs.flags.lower(&j);
                if self.regs.k == Some(j) {
                    // J is the current sequence, so the flag is
                    // lowered but don't perform a drop-out (see User
                    // Handbook page 4-7).
                    self.regs.current_sequence_is_runnable = true;
                }
                Ok(())
            }
            0o50_000 => {
                self.regs.flags.raise(&j);
                if Some(j) == self.regs.k {
                    dismiss_reason = None;
                }
                Ok(())
            }
            0o60_000..=0o60777 => {
                // Select unit XXX
                Err(self.alarm_unit.always_fire(Alarm::ROUNDTUITAL(format!(
                    "IOS operand {:o}: Select Unit command is not yet implemented.",
                    operand
                ))))
            }
            _ => {
                let command: u8 = (u32::from(operand) >> 12) as u8;
                self.alarm_unit.fire_if_not_masked(Alarm::IOSAL {
                    unit: j,
                    operand: Some(operand),
                    message: format!(
                        "IOS operand {:o} has unrecognised leading command digit {:o}",
                        operand, command,
                    ),
                })?;
                // IOSAL is masked.  Just do nothing.
                Ok(())
            }
        };
        if let Some(reason) = dismiss_reason {
            self.dismiss_unless_held(reason);
        }
        result.map(|()| OpcodeResult::default())
    }

    fn connect_unit(
        devices: &mut DeviceManager,
        regs: &mut ControlRegisters,
        trap: &mut TrapCircuit,
        system_time: &Duration,
        unit: Unsigned6Bit,
        mode: Unsigned12Bit,
        alarm_unit: &AlarmUnit,
    ) -> Result<(), Alarm> {
        let maybe_flag_change: Option<FlagChange> = match u8::from(unit) {
            0o42 => {
                trap.connect(system_time, mode);
                None
            }
            _ => devices.connect(system_time, &unit, mode, alarm_unit)?,
        };
        if let Some(FlagChange::Raise) = maybe_flag_change {
            regs.flags.raise(&unit);
        }
        Ok(())
    }

    pub(crate) fn op_tsd(
        &mut self,
        devices: &mut DeviceManager,
        execution_address: Address,
        system_time: &Duration,
        mem: &mut MemoryUnit,
    ) -> Result<OpcodeResult, Alarm> {
        fn make_tsd_qsal(inst: Instruction, op: BadMemOp) -> Alarm {
            Alarm::QSAL(inst, op, "TSD address is not mapped".to_string())
        }

        let result: Result<TransferOutcome, Alarm> = if let Some(unit) = self.regs.k {
            let target: Address = self.operand_address_with_optional_defer_and_index(mem)?;
            let not_mapped = |op_conv: OpConversion| -> Alarm {
                let op: BadMemOp = op_conv(target);
                make_tsd_qsal(self.regs.n, op)
            };

            let meta_op: MetaBitChange = if self.trap.set_metabits_of_operands() {
                MetaBitChange::Set
            } else {
                MetaBitChange::None
            };
            // There are no sequence numbers below 0o40, besides 0.
            if matches!(u8::from(unit), 0 | 0o75 | 0o76) {
                // Non-INOUT sequences just cycle the target location;
                // see section 4-1 (page 4-3) of the Users Handbook;
                // also pages 4-2 and 4-9).
                match mem.cycle_word(&target) {
                    Ok(extra_bits) => Ok(TransferOutcome::Success(extra_bits.meta)),
                    Err(MemoryOpFailure::ReadOnly(_address, extra_bits)) => {
                        // The read-only case is not an error, it's
                        // normal.  The TSD instruction simply has no
                        // effect when the target address is
                        // read-only.
                        // TODO: should there be an effect on the E register?
                        Ok(TransferOutcome::Success(extra_bits.meta))
                    }
                    Err(MemoryOpFailure::NotMapped(_)) => {
                        self.alarm_unit.fire_if_not_masked(not_mapped(bad_write))?;
                        // QSAL is masked, carry on.
                        Ok(TransferOutcome::Success(false)) // act as if metabit unset
                    }
                }
            } else {
                match devices.get_mut(&unit) {
                    None => {
                        event!(Level::WARN, "TSD on unknown unit {:o}", unit);
                        Ok(TransferOutcome::DismissAndWait)
                    }
                    Some(device) => {
                        let is_input_unit = device.is_input_unit;
                        if !device.connected {
                            // If the unit is not connected, perform
                            // dismiss and wait.  This requirement is
                            // described in section 4-3.7 of the Users
                            // Handbook.
                            Ok(TransferOutcome::DismissAndWait)
                        } else if device.in_maintenance {
                            event!(
                                Level::WARN,
                                "TSD on unit {:o}, but it is in maintenance",
                                unit
                            );
                            Ok(TransferOutcome::DismissAndWait)
                        } else {
                            // We're actually going to do the (input or output) transfer.
                            // First load into the M register the existing contents of
                            // memory.
                            let transfer_mode = device.transfer_mode();
                            let (m_register, extra_bits) = self
                                .fetch_operand_from_address_without_exchange(
                                    mem,
                                    &target,
                                    &UpdateE::No,
                                )?;
                            if is_input_unit {
                                // In read operations, data is transferred
                                // from the I/O device's buffer over the
                                // IOBM bus, into the E register.  See
                                // figure 15-18 in Volume 2 of the TX-2
                                // Techical Manual.
                                match device.read(system_time) {
                                    Ok(masked_word) => {
                                        const UPDATE_E_YES: UpdateE = UpdateE::Yes;
                                        let newval: Unsigned36Bit =
                                            masked_word.apply(Unsigned36Bit::ZERO);
                                        match transfer_mode {
                                            TransferMode::Assembly => {
                                                let bits: Unsigned6Bit =
                                                    newval.bitand(Unsigned6Bit::MAX);
                                                self.memory_store_without_exchange(
                                                    mem,
                                                    &target,
                                                    &cycle_and_splay(m_register, bits),
                                                    &UPDATE_E_YES,
                                                    &meta_op,
                                                )?;
                                            }
                                            TransferMode::Exchange => {
                                                self.memory_store_with_exchange(
                                                    mem,
                                                    &target,
                                                    &newval,
                                                    &m_register,
                                                    &UPDATE_E_YES,
                                                    &meta_op,
                                                )?;
                                            }
                                        }
                                        Ok(TransferOutcome::Success(extra_bits.meta))
                                    }
                                    Err(e) => match e {
                                        TransferFailed::BufferNotFree => {
                                            Ok(TransferOutcome::DismissAndWait)
                                        }
                                    },
                                }
                            } else {
                                // In write operations, data is
                                // transferred from the E register to
                                // the I/O device over the E bus.  See
                                // figure 15-17 in Volume 2 of the
                                // TX-2 Techical Manual.
                                self.regs.e = exchanged_value_for_load(
                                    &self.get_config(),
                                    &m_register,
                                    &self.regs.e,
                                );
                                match transfer_mode {
                                    TransferMode::Exchange => {
                                        match device.write(system_time, self.regs.e) {
                                            Err(TransferFailed::BufferNotFree) => {
                                                Ok(TransferOutcome::DismissAndWait)
                                            }
                                            Ok(()) => Ok(TransferOutcome::Success(extra_bits.meta)),
                                        }
                                    }
                                    TransferMode::Assembly => {
                                        Err(self.alarm_unit.always_fire(Alarm::ROUNDTUITAL(
                                            "TSD output in assembly mode is not yet implemented."
                                                .to_string(),
                                        )))
                                    }
                                }
                            }
                        }
                    }
                }
            }
        } else {
            Err(self.alarm_unit.always_fire(Alarm::BUGAL {
		instr: Some(self.regs.n),
		message: "Executed TSD instruction while the K register is None (i.e. there is no current sequence)".to_string(),
	    }))
        };
        match result {
            Ok(TransferOutcome::Success(meta_bit_set)) => {
                if meta_bit_set && self.trap.trap_on_operand() {
                    self.raise_trap();
                }
                Ok(OpcodeResult {
                    program_counter_change: None,
                    poll_order_change: true,
                })
            }
            Ok(TransferOutcome::DismissAndWait) => {
                // In the dismiss and wait case, the
                // sequence is dismissed even if the hold
                // bit is set (Users Handbook, section
                // 4-3.2).  The hold bit only governs what
                // happens following the completion of an
                // instruction.
                self.dismiss("TSD while data was not ready caused dismiss-and-wait");
                Ok(OpcodeResult {
                    program_counter_change: Some(ProgramCounterChange::DismissAndWait(
                        execution_address,
                    )),
                    poll_order_change: true,
                })
            }
            Err(e) => Err(e),
        }
    }
}
