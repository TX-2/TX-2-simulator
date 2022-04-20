use base::prelude::*;
use std::time::Duration;

use tracing::{event, Level};

use crate::alarm::{Alarm, AlarmUnit};
use crate::control::{ControlRegisters, ControlUnit, DeviceManager, TrapCircuit};
use crate::io::{FlagChange, TransferOutcome, Unit};
use crate::memory::{MemoryUnit, MetaBitChange};

impl ControlUnit {
    /// Implements the IOS opcode
    pub fn op_ios(&mut self, system_time: &Duration) -> Result<(), Alarm> {
        let j = self.regs.n.index_address();
        let cf = self.regs.n.configuration();

        if cf & 1 != 0 {
            // Setting the report bit in the configuration value
            // causes the device's status word from before any mode
            // change to be copied into the E register.  (as stated in
            // section 4-3.6 of the User Handbook).
            let flag_raised: bool = self.regs.flags.current_flag_state(&j);
            self.regs.e = self
                .devices
                .report(system_time, j, flag_raised, &self.alarm_unit)?;
        }
        let mut dismiss: bool = cf & 0o20 != 0;

        let operand = self.regs.n.operand_address_and_defer_bit();
        let result = match u32::from(operand) {
            0o20_000 => self.disconnect_unit(j),
            0o30_000..=0o37_777 => {
                let mode: Unsigned12Bit = Unsigned12Bit::try_from(operand & 0o07_777).unwrap();
                ControlUnit::connect_unit(
                    &mut self.devices,
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
                    dismiss = false;
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
        if dismiss {
            self.dismiss_unless_held();
        }
        result
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

    fn disconnect_unit(&mut self, unit: Unsigned6Bit) -> Result<(), Alarm> {
        match u8::from(unit) {
            0o42 => Ok(()),
            _ => self.devices.disconnect(&unit, &self.alarm_unit),
        }
    }

    pub fn op_tsd(&mut self, system_time: &Duration, mem: &mut MemoryUnit) -> Result<bool, Alarm> {
        let mut increment_pc: bool = true;
        if let Some(unit) = self.regs.k {
            let cf = self.regs.n.configuration();
            let target: Address = self.operand_address_with_optional_defer_and_index(mem)?;
            let meta_op: MetaBitChange = if self.trap.set_metabits_of_operands() {
                MetaBitChange::Set
            } else {
                MetaBitChange::None
            };
            match self.devices.transfer(
                system_time,
                &unit,
                &cf,
                &target,
                mem,
                &self.regs.n,
                &meta_op,
                &self.alarm_unit,
            ) {
                Ok(TransferOutcome::Success(meta_bit_set)) => {
                    if meta_bit_set && self.trap.trap_on_operand() {
                        self.raise_trap();
                    }
                    Ok(true)
                }
                Ok(TransferOutcome::DismissAndWait) => {
                    if let Some(current_seq) = self.regs.k {
                        if current_seq == Unsigned6Bit::ZERO {
                            event!(Level::WARN, "Ignoring TSD dismiss and wait for sequence 0",);
                        } else {
                            // The program counter has not yet been
                            // incremented, which is good, because
                            // this sequence should resume at the
                            // current address.  The P register will
                            // be saved in the relevant index register
                            // by fetch_instruction().
                            //
                            // In the dismiss and wait case, the
                            // sequence is dismissed even if the hold
                            // bit is set (Users Handbook, section
                            // 4-3.2).  The hold bit only governs what
                            // happens following the completion of an
                            // instruction.
                            self.dismiss();
                            increment_pc = false;
                        }
                    }
                    Ok(increment_pc)
                }
                Err(e) => Err(e),
            }
        } else {
            Err(self.alarm_unit.always_fire(Alarm::BUGAL {
		instr: Some(self.regs.n),
		message: "Executed TSD instruction while the K register is None (i.e. there is no current sequence)".to_string(),
	    }))
        }
    }
}
