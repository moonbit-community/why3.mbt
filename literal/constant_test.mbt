// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "literal constructors retain exact integer and byte values" {
  let integer = Constant::integer(
    ILitHex,
    BigInt::from_string("123456789012345678901234567890"),
  )
  assert_true(
    integer is ConstInt({ kind: ILitHex, value }) &&
    value.to_string() == "123456789012345678901234567890",
  )
  let string = Constant::string(b"\x00\x7f\x80\xff")
  assert_true(string is ConstStr(value) && value == b"\x00\x7f\x80\xff")
}

///|
test "real normalization extracts powers of two and five exactly" {
  let value = RealValue::normalized(
    BigInt::from_int(-200),
    BigInt::from_int(-3),
    BigInt::from_int(-2),
  )
  assert_eq(value.significand(), BigInt::from_int(-1))
  assert_eq(value.pow2(), BigInt::from_int(0))
  assert_eq(value.pow5(), BigInt::from_int(0))
  let real = Constant::real(RLitDec(-2L), value)
  assert_true(
    real is ConstReal({ kind: RLitDec(-2L), value: normalized }) &&
    normalized == value,
  )
}

///|
test "zero has a unique normalized representation" {
  let zero = RealValue::normalized(
    BigInt::from_int(0),
    BigInt::from_int(999),
    BigInt::from_int(-999),
  )
  assert_eq(zero.significand(), BigInt::from_int(0))
  assert_eq(zero.pow2(), BigInt::from_int(0))
  assert_eq(zero.pow5(), BigInt::from_int(0))
}

///|
test "literal negation preserves source kinds and is involutive" {
  let integer = IntConstant::{ kind: ILitOct, value: BigInt::from_int(511) }
  assert_eq(integer.negated(), { kind: ILitOct, value: BigInt::from_int(-511) })
  assert_eq(integer.negated().negated(), integer)
  let real = RealConstant::{
    kind: RLitHex(5L),
    value: RealValue::normalized(
      BigInt::from_int(99),
      BigInt::from_int(1),
      BigInt::from_int(2),
    ),
  }
  assert_eq(real.negated().negated(), real)
  assert_true(real.negated().kind is RLitHex(5L))
}
