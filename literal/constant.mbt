// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

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
/// Exact Why3 constants. Strings stay raw bytes; real constants retain the
/// normalized `(significand, pow2, pow5)` representation.
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
/// Constructs the normalized exact representation used by Why3 real values.
pub fn RealValue::normalized(
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
pub fn IntConstant::negated(self : IntConstant) -> IntConstant {
  { ..self, value: -self.value }
}

///|
pub fn RealConstant::negated(self : RealConstant) -> RealConstant {
  { ..self, value: { ..self.value, significand: -self.value.significand } }
}

///|
pub fn Constant::integer(kind : IntLiteralKind, value : BigInt) -> Constant {
  ConstInt({ kind, value })
}

///|
pub fn Constant::real(kind : RealLiteralKind, value : RealValue) -> Constant {
  ConstReal({ kind, value })
}

///|
pub fn Constant::string(value : BytesView) -> Constant {
  ConstStr(value.to_owned())
}
