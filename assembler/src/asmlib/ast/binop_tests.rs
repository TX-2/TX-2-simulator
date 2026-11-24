use super::{ArithmeticExpression, Operator};
use base::prelude::*;

const ALL_BIT_POSITIONS: [Unsigned36Bit; 36] = [
    u36!(0b000_000_000_000_000_000_000_000_000_000_000_001),
    u36!(0b000_000_000_000_000_000_000_000_000_000_000_010),
    u36!(0b000_000_000_000_000_000_000_000_000_000_000_100),
    u36!(0b000_000_000_000_000_000_000_000_000_000_001_000),
    u36!(0b000_000_000_000_000_000_000_000_000_000_010_000),
    u36!(0b000_000_000_000_000_000_000_000_000_000_100_000),
    u36!(0b000_000_000_000_000_000_000_000_000_001_000_000),
    u36!(0b000_000_000_000_000_000_000_000_000_010_000_000),
    u36!(0b000_000_000_000_000_000_000_000_000_100_000_000),
    u36!(0b000_000_000_000_000_000_000_000_001_000_000_000),
    u36!(0b000_000_000_000_000_000_000_000_010_000_000_000),
    u36!(0b000_000_000_000_000_000_000_000_100_000_000_000),
    u36!(0b000_000_000_000_000_000_000_001_000_000_000_000),
    u36!(0b000_000_000_000_000_000_000_010_000_000_000_000),
    u36!(0b000_000_000_000_000_000_000_100_000_000_000_000),
    u36!(0b000_000_000_000_000_000_001_000_000_000_000_000),
    u36!(0b000_000_000_000_000_000_010_000_000_000_000_000),
    u36!(0b000_000_000_000_000_000_100_000_000_000_000_000),
    u36!(0b000_000_000_000_000_001_000_000_000_000_000_000),
    u36!(0b000_000_000_000_000_010_000_000_000_000_000_000),
    u36!(0b000_000_000_000_000_100_000_000_000_000_000_000),
    u36!(0b000_000_000_000_001_000_000_000_000_000_000_000),
    u36!(0b000_000_000_000_010_000_000_000_000_000_000_000),
    u36!(0b000_000_000_000_100_000_000_000_000_000_000_000),
    u36!(0b000_000_000_001_000_000_000_000_000_000_000_000),
    u36!(0b000_000_000_010_000_000_000_000_000_000_000_000),
    u36!(0b000_000_000_100_000_000_000_000_000_000_000_000),
    u36!(0b000_000_001_000_000_000_000_000_000_000_000_000),
    u36!(0b000_000_010_000_000_000_000_000_000_000_000_000),
    u36!(0b000_000_100_000_000_000_000_000_000_000_000_000),
    u36!(0b000_001_000_000_000_000_000_000_000_000_000_000),
    u36!(0b000_010_000_000_000_000_000_000_000_000_000_000),
    u36!(0b000_100_000_000_000_000_000_000_000_000_000_000),
    u36!(0b001_000_000_000_000_000_000_000_000_000_000_000),
    u36!(0b010_000_000_000_000_000_000_000_000_000_000_000),
    u36!(0b100_000_000_000_000_000_000_000_000_000_000_000),
];
const SOME_ARBITRARY_VALUES: [Unsigned36Bit; 9] = [
    u36!(0o000_002),
    u36!(0o000_005),
    u36!(0o000_000_000_007),
    u36!(0o000_000_007_000),
    u36!(0o000_007_000_000),
    u36!(0o007_000_000_000),
    u36!(0o070_000_000_000),
    u36!(0o700_000_000_000),
    u36!(0o700_000_300_001),
];

#[cfg(test)]
fn some_positive_values() -> impl Iterator<Item = Unsigned36Bit> {
    ALL_BIT_POSITIONS
        .iter()
        .chain(SOME_ARBITRARY_VALUES.iter())
        .copied()
}

#[test]
fn test_eval_binop_xor_12() {
    assert_eq!(
        ArithmeticExpression::eval_binop(u36!(0o1), Operator::LogicalXor, u36!(0o2)),
        u36!(3)
    );
}

#[test]
fn test_eval_binop_xor_55() {
    assert_eq!(
        ArithmeticExpression::eval_binop(u36!(0o5), Operator::LogicalXor, u36!(0o5)),
        Unsigned36Bit::ZERO,
    );
}

fn check_binop(left: Unsigned36Bit, op: Operator, right: Unsigned36Bit, expected: Unsigned36Bit) {
    let got = ArithmeticExpression::eval_binop(left, op, right);
    assert_eq!(
        got, expected,
        "{left} {op} {right} should produce {expected} but it actually produced {got}"
    );
}

fn check_commutative_binop(
    left: Unsigned36Bit,
    op: Operator,
    right: Unsigned36Bit,
    expected: Unsigned36Bit,
) {
    check_binop(left, op, right, expected);
    check_binop(right, op, left, expected);
}

#[test]
fn test_all_bit_positions_coverage() {
    let mut or_accumulator = Unsigned36Bit::ZERO;
    let mut xor_accumulator = Unsigned36Bit::ZERO;
    for input in ALL_BIT_POSITIONS {
        or_accumulator = or_accumulator | input;
        xor_accumulator = xor_accumulator ^ input;
    }
    // Verify that we have used each of the bits of the 36-bit word, just once.
    assert_eq!(
        xor_accumulator,
        Unsigned36Bit::MAX,
        "a bit position occcurs twice in the inputs"
    );
    assert_eq!(
        or_accumulator,
        Unsigned36Bit::MAX,
        "a bit position is missing from the test inputs"
    );
}

#[test]
fn test_eval_binop_add_identities() {
    for input in some_positive_values() {
        check_commutative_binop(input, Operator::Add, Unsigned36Bit::ZERO, input);
        if input < u36!(0o1 << 35) {
            let expected: Unsigned36Bit = input.checked_add(input).expect("should not overflow");
            check_commutative_binop(input, Operator::Add, input, expected);
        }
    }
    check_commutative_binop(
        Unsigned36Bit::ZERO,
        Operator::Add,
        Unsigned36Bit::ZERO,
        Unsigned36Bit::ZERO,
    );
}

#[test]
fn test_eval_binop_logical_and_identities() {
    for input in some_positive_values() {
        check_commutative_binop(
            input,
            Operator::LogicalAnd,
            Unsigned36Bit::ZERO,
            Unsigned36Bit::ZERO,
        );
        check_commutative_binop(input, Operator::LogicalAnd, input, input);
    }
    check_commutative_binop(
        Unsigned36Bit::ZERO,
        Operator::LogicalAnd,
        Unsigned36Bit::ZERO,
        Unsigned36Bit::ZERO,
    );
}

#[test]
fn test_eval_binop_logical_and_120() {
    check_commutative_binop(
        u36!(0o1),
        Operator::LogicalAnd,
        u36!(0o2),
        Unsigned36Bit::ZERO,
    );
}

#[test]
fn test_eval_binop_xor_identities() {
    for input in some_positive_values() {
        check_commutative_binop(input, Operator::LogicalXor, Unsigned36Bit::ZERO, input);
        check_commutative_binop(input, Operator::LogicalXor, input, Unsigned36Bit::ZERO);
    }
    check_commutative_binop(
        Unsigned36Bit::ZERO,
        Operator::LogicalXor,
        Unsigned36Bit::ZERO,
        Unsigned36Bit::ZERO,
    );
}

#[test]
fn test_eval_binop_logical_or_identities() {
    for input in some_positive_values() {
        check_commutative_binop(input, Operator::LogicalOr, Unsigned36Bit::ZERO, input);
        check_commutative_binop(input, Operator::LogicalOr, input, input);
    }
    check_commutative_binop(
        Unsigned36Bit::ZERO,
        Operator::LogicalOr,
        Unsigned36Bit::ZERO,
        Unsigned36Bit::ZERO,
    );
}

#[test]
fn test_eval_binop_logical_or_123() {
    check_commutative_binop(u36!(0o1), Operator::LogicalOr, u36!(0o2), u36!(0o3));
}

#[test]
fn test_eval_binop_multiply_identities() {
    for input in some_positive_values() {
        check_commutative_binop(
            input,
            Operator::Multiply,
            Unsigned36Bit::ZERO,
            Unsigned36Bit::ZERO,
        );
        check_commutative_binop(input, Operator::Multiply, u36!(1), input);
    }
    check_commutative_binop(
        Unsigned36Bit::ZERO,
        Operator::Multiply,
        Unsigned36Bit::ZERO,
        Unsigned36Bit::ZERO,
    );
}

#[test]
fn test_eval_binop_multiply_examples() {
    check_commutative_binop(u36!(2), Operator::Multiply, u36!(3), u36!(6));
}

#[test]
fn test_eval_binop_subtract_identities() {
    for input in some_positive_values() {
        check_binop(input, Operator::Subtract, Unsigned36Bit::ZERO, input);
        check_binop(input, Operator::Subtract, input, Unsigned36Bit::ZERO);
    }
    check_commutative_binop(
        Unsigned36Bit::ZERO,
        Operator::Subtract,
        Unsigned36Bit::ZERO,
        Unsigned36Bit::ZERO,
    );
}

#[test]
fn test_eval_binop_subtract_examples() {
    check_binop(u36!(0o7), Operator::Subtract, u36!(0o2), u36!(0o5));
}

#[test]
fn test_eval_binop_divide_identities() {
    for input in some_positive_values() {
        check_binop(input, Operator::Divide, u36!(1), input); // x/1 = x
        check_binop(input, Operator::Divide, input, u36!(1)); // x/x = 1
    }
    check_commutative_binop(
        Unsigned36Bit::ZERO,
        Operator::Subtract,
        Unsigned36Bit::ZERO,
        Unsigned36Bit::ZERO,
    );
}
