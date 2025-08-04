use core::time::Duration;

use super::DeviceManager;
use super::alarm::{Alarm, AlarmDetails};
use super::context::Context;
use super::control::ConfigurationMemorySetup;
use super::memory::MetaBitChange;
use super::{ControlUnit, MemoryConfiguration, MemoryUnit, PanicOnUnmaskedAlarm, UpdateE};
use base::prelude::*;

fn make_ctx() -> Context {
    Context {
        simulated_time: Duration::new(42, 42),
        real_elapsed_time: Duration::new(7, 12),
    }
}

fn setup(ctx: &Context, p: Address) -> (ControlUnit, MemoryUnit) {
    let mut control = ControlUnit::new(
        PanicOnUnmaskedAlarm::No,
        ConfigurationMemorySetup::StandardForTestingOnly,
    );
    let mem = MemoryUnit::new(
        ctx,
        &MemoryConfiguration {
            with_u_memory: false,
        },
    );
    control.regs.p = p;
    control.regs.k = Some(Unsigned6Bit::ZERO);
    control.regs.flags.lower_all();
    control.regs.flags.raise(&SequenceNumber::ZERO);
    (control, mem)
}

#[test]
fn test_roundtuital_not_maskable() {
    // Simulate an unumplemented instruction, verify that the alarm
    // unit states that an unmaskable alarm (ROUNDTUITAL) is active.
    const COMPLAIN: &str = "failed to set up instruction as test data";
    let context = make_ctx();
    let p = Address::from(u18!(0o250));
    let mut devices = DeviceManager::default();
    let (mut control, mut mem) = setup(&context, p);
    let sym = SymbolicInstruction {
        held: false,
        configuration: Unsigned5Bit::ZERO,
        opcode: Opcode::Sca,
        index: u6!(1),
        operand_address: OperandAddress::direct(Address::ZERO),
    };
    let instruction = Instruction::from(&sym);
    let instruction_bits = instruction.bits();
    control
        .memory_store_without_exchange(
            &context,
            &mut mem,
            &p,
            &instruction_bits,
            &UpdateE::No,
            &MetaBitChange::None,
        )
        .expect(COMPLAIN);
    control.update_n_register(instruction_bits).expect(COMPLAIN);
    let mut poll_order_change: Option<SequenceNumber> = None;
    let result =
        control.execute_instruction(&context, &mut devices, &mut mem, &mut poll_order_change);
    match result {
        Ok(_) => {
            panic!(
                "execution of SCA is not expected to succeed, it is not implemented yet: {result:?}"
            );
        }
        Err((
            Alarm {
                sequence: _,
                details: AlarmDetails::ROUNDTUITAL(_),
            },
            _,
        )) => (),
        Err(_) => {
            panic!("expected execution of SCA to raise ROUNDTUITAL, but got {result:?}");
        }
    }
    assert!(control.unmasked_alarm_active());
}
