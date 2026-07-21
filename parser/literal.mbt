// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
pub(all) enum IntLiteralKind {
  ILitUnk
  ILitDec
  ILitHex
  ILitOct
  ILitBin
} derive(Debug, Eq)

///|
pub(all) struct IntConstant {
  kind : IntLiteralKind
  value : BigInt
} derive(Debug, Eq)

///|
pub struct RealValue {
  significand : BigInt
  pow2 : BigInt
  pow5 : BigInt
} derive(Debug, Eq)

///|
pub(all) enum RealLiteralKind {
  RLitUnk
  RLitDec(Int64)
  RLitHex(Int64)
} derive(Debug, Eq)

///|
pub(all) struct RealConstant {
  kind : RealLiteralKind
  value : RealValue
} derive(Debug, Eq)

///|
pub(all) enum Constant {
  ConstInt(IntConstant)
  ConstReal(RealConstant)
  ConstStr(Bytes)
} derive(Debug, Eq)

///|
pub fn RealValue::significand(self : RealValue) -> BigInt {
  self.significand
}

///|
pub fn RealValue::pow2(self : RealValue) -> BigInt {
  self.pow2
}

///|
pub fn RealValue::pow5(self : RealValue) -> BigInt {
  self.pow5
}

///|
fn digit_value(byte : Byte) -> Int? {
  let value = byte.to_int()
  if value >= b'0'.to_int() && value <= b'9'.to_int() {
    Some(value - b'0'.to_int())
  } else if value >= b'A'.to_int() && value <= b'Z'.to_int() {
    Some(10 + value - b'A'.to_int())
  } else if value >= b'a'.to_int() && value <= b'z'.to_int() {
    Some(10 + value - b'a'.to_int())
  } else {
    None
  }
}

///|
fn parse_bigint_digits(
  digits : BytesView,
  radix : Int,
  span : Span,
) -> BigInt raise ParseError {
  let base = BigInt::from_int(radix)
  let mut value = BigInt::from_int(0)
  let mut saw_digit = false
  for byte in digits {
    if byte == b'_' {
      continue
    }
    guard digit_value(byte) is Some(digit) && digit < radix else {
      fail_with_diagnostic(make_parse_diagnostic(InvalidNumericLiteral, span))
    }
    saw_digit = true
    value = value * base + BigInt::from_int(digit)
  }
  if !saw_digit {
    fail_with_diagnostic(make_parse_diagnostic(InvalidNumericLiteral, span))
  }
  value
}

///|
fn int_radix(kind : IntLiteralKind, span : Span) -> Int raise ParseError {
  match kind {
    ILitBin => 2
    ILitOct => 8
    ILitDec => 10
    ILitHex => 16
    ILitUnk =>
      fail_with_diagnostic(make_parse_diagnostic(InvalidNumericLiteral, span))
  }
}

///|
fn make_int_constant(
  kind : IntLiteralKind,
  digits : BytesView,
  negative? : Bool = false,
  span~ : Span,
) -> IntConstant raise ParseError {
  let value = parse_bigint_digits(digits, int_radix(kind, span), span)
  { kind, value: if negative { -value } else { value } }
}

///|
fn IntConstant::negated(self : IntConstant) -> IntConstant {
  { ..self, value: -self.value }
}

///|
fn extract_factor(
  value : BigInt,
  factor : BigInt,
  weight : BigInt,
) -> (BigInt, BigInt) {
  let quotient = value / factor
  if !(value % factor).is_zero() {
    return (value, BigInt::from_int(0))
  }
  let doubled = weight + weight
  let (reduced, count) = extract_factor(quotient, factor * factor, doubled)
  let quotient = reduced / factor
  if (reduced % factor).is_zero() {
    (quotient, count + doubled)
  } else {
    (reduced, count + weight)
  }
}

///|
fn normalized_real_value(
  significand : BigInt,
  pow2 : BigInt,
  pow5 : BigInt,
) -> RealValue {
  if significand.is_zero() {
    let zero = BigInt::from_int(0)
    return { significand: zero, pow2: zero, pow5: zero }
  }
  let (significand, factor2) = extract_factor(
    significand,
    BigInt::from_int(2),
    BigInt::from_int(1),
  )
  let (significand, factor5) = extract_factor(
    significand,
    BigInt::from_int(5),
    BigInt::from_int(1),
  )
  { significand, pow2: pow2 + factor2, pow5: pow5 + factor5 }
}

///|
fn make_real_constant(
  radix : Int,
  integer_digits : BytesView,
  fraction_digits : BytesView,
  exponent : Int64,
  negative? : Bool = false,
  span~ : Span,
) -> RealConstant raise ParseError {
  if integer_digits.is_empty() && fraction_digits.is_empty() {
    fail_with_diagnostic(make_parse_diagnostic(InvalidNumericLiteral, span))
  }
  let kind = match radix {
    10 => RLitDec(exponent)
    16 => RLitHex(exponent)
    _ =>
      fail_with_diagnostic(make_parse_diagnostic(InvalidNumericLiteral, span))
  }
  let all_digits = integer_digits.to_owned() + fraction_digits.to_owned()
  let significand = parse_bigint_digits(all_digits, radix, span)
  let significand = if negative { -significand } else { significand }
  let fractional_scale = BigInt::from_int(fraction_digits.length()) *
    BigInt::from_int(if radix == 16 { 4 } else { 1 })
  let power = BigInt::from_int64(exponent) - fractional_scale
  let value = if radix == 10 {
    normalized_real_value(significand, power, power)
  } else {
    normalized_real_value(significand, power, BigInt::from_int(0))
  }
  { kind, value }
}

///|
fn RealConstant::negated(self : RealConstant) -> RealConstant {
  { ..self, value: { ..self.value, significand: -self.value.significand } }
}

///|
const OCAML_INT_MIN : Int64 = -4611686018427387904L

///|
const OCAML_INT_MAX : Int64 = 4611686018427387903L

///|
const WHY3_MAX_LINE : Int64 = 140737488355327L

///|
fn checked_ocaml_int(value : BigInt, span : Span) -> Int64 raise ParseError {
  if value.compare_int64(OCAML_INT_MIN) < 0 ||
    value.compare_int64(OCAML_INT_MAX) > 0 {
    fail_with_diagnostic(make_parse_diagnostic(NumericOverflow, span))
  }
  value.to_int64()
}

///|
fn checked_directive_number(
  value : BigInt,
  span : Span,
) -> Int64 raise ParseError {
  if value.compare_int(0) < 0 || value.compare_int64(OCAML_INT_MAX) > 0 {
    fail_with_diagnostic(make_parse_diagnostic(NumericOverflow, span))
  }
  value.to_int64()
}

///|
fn checked_why3_line(value : BigInt, span : Span) -> Int64 raise ParseError {
  let value = checked_directive_number(value, span)
  if value > WHY3_MAX_LINE {
    fail_with_diagnostic(make_parse_diagnostic(NumericOverflow, span))
  }
  value
}

///|
fn why3_decode_line_column(line : Int64, column : Int64) -> (Int64, Int64) {
  let mask63 = 0x7fff_ffff_ffff_ffffUL
  let bits = (
      (line.reinterpret_as_uint64() << 16) | column.reinterpret_as_uint64()
    ) &
    mask63
  (
    (bits >> 16).reinterpret_as_int64(),
    (bits & 0xffffUL).reinterpret_as_int64(),
  )
}
