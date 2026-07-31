// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
pub type IntLiteralKind = @literal.IntLiteralKind

///|
pub type IntConstant = @literal.IntConstant

///|
pub type RealValue = @literal.RealValue

///|
pub type RealLiteralKind = @literal.RealLiteralKind

///|
pub type RealConstant = @literal.RealConstant

///|
pub type Constant = @literal.Constant

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
  let kind : RealLiteralKind = match radix {
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
    RealValue::normalized(significand, power, power)
  } else {
    RealValue::normalized(significand, power, BigInt::from_int(0))
  }
  { kind, value }
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
