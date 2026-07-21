// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
let uppercase_hex_digits : Bytes = b"0123456789ABCDEF"

///|
fn write_smt_string(state : PrinterState, value : BytesView) -> Unit {
  state.writer.write(b"\"")
  for byte in value {
    match byte {
      b'\\' => state.writer.write(b"\\x5C")
      b'"' => state.writer.write(b"\\x22")
      b' '..=b'~' => state.writer.write(Bytes::from_array([byte]))
      _ => {
        state.writer.write(b"\\x")
        state.writer.write(
          Bytes::from_array([
            uppercase_hex_digits[byte.to_int() >> 4],
            uppercase_hex_digits[byte.to_int() & 0x0f],
          ]),
        )
      }
    }
  }
  state.writer.write(b"\"")
}

///|
fn absolute_bigint(value : BigInt) -> BigInt {
  if value.compare_int(0) < 0 {
    -value
  } else {
    value
  }
}

///|
fn write_integer_constant(state : PrinterState, value : BigInt) -> Unit {
  if value.compare_int(0) < 0 {
    state.writer.write(b"(- ")
    state.writer.write_string_utf8(absolute_bigint(value).to_string())
    state.writer.write(b")")
  } else {
    state.writer.write_string_utf8(value.to_string())
  }
}

///|
fn write_real_constant(
  state : PrinterState,
  constant : @logic.Constant,
) -> Unit {
  guard constant.view() is RealConstant(_, value) else {
    abort("write_real_constant received a non-real constant")
  }
  let negative = value.significand().compare_int(0) < 0
  if negative {
    state.writer.write(b"(- ")
  }
  let two = BigInt::from_int(2)
  let five = BigInt::from_int(5)
  let one = BigInt::from_int(1)
  let mut numerator = absolute_bigint(value.significand())
  let mut denominator = one
  let pow2 = value.pow2()
  let factor2 = two.pow(absolute_bigint(pow2))
  if pow2.compare_int(0) < 0 {
    denominator = denominator * factor2
  } else {
    numerator = numerator * factor2
  }
  let pow5 = value.pow5()
  let factor5 = five.pow(absolute_bigint(pow5))
  if pow5.compare_int(0) < 0 {
    denominator = denominator * factor5
  } else {
    numerator = numerator * factor5
  }
  if denominator == one {
    state.writer.write_string_utf8(numerator.to_string())
    state.writer.write(b".0")
  } else {
    state.writer.write(b"(/ ")
    state.writer.write_string_utf8(numerator.to_string())
    state.writer.write(b".0 ")
    state.writer.write_string_utf8(denominator.to_string())
    state.writer.write(b".0)")
  }
  if negative {
    state.writer.write(b")")
  }
}

///|
fn print_constant(state : PrinterState, constant : @logic.Constant) -> Unit {
  match constant.view() {
    IntegerConstant(_, value) => write_integer_constant(state, value)
    RealConstant(_, _) => write_real_constant(state, constant)
    StringConstant(value) => write_smt_string(state, value)
  }
}
