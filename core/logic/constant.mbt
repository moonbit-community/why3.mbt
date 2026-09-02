// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

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
fn absolute_bigint(value : BigInt) -> BigInt {
  if value.compare_int(0) < 0 {
    -value
  } else {
    value
  }
}

///|
/// Exact representability check corresponding to Why3's `compute_float`.
fn real_fits_float(
  value : RealValue,
  exponent_digits : Int,
  significand_digits : Int,
) -> Bool {
  let zero = BigInt::from_int(0)
  let one = BigInt::from_int(1)
  let two = BigInt::from_int(2)
  let five = BigInt::from_int(5)
  let pow5 = value.pow5()
  if pow5 < zero {
    return false
  }
  let mut significand = value.significand() * five.pow(pow5)
  let mut exponent = value.pow2()
  if significand.is_zero() {
    return true
  }
  significand = absolute_bigint(significand)
  let exponent_bits = BigInt::from_int(exponent_digits)
  let significand_bits = BigInt::from_int(significand_digits)
  let minimum_significand = two.pow(significand_bits - one)
  let maximum_significand = two.pow(significand_bits) - one
  let maximum_exponent = two.pow(exponent_bits - one)
  let denormal_exponent = one - maximum_exponent
  let minimum_exponent = two + denormal_exponent - significand_bits
  while significand > maximum_significand || exponent < minimum_exponent {
    if !(significand % two).is_zero() {
      return false
    }
    significand = significand / two
    exponent = exponent + one
  }
  while significand < minimum_significand && exponent > minimum_exponent {
    significand = significand * two
    exponent = exponent - one
  }
  if significand < minimum_significand {
    true
  } else {
    let normalized_exponent = exponent + significand_bits - one
    normalized_exponent < maximum_exponent
  }
}

///|
fn validate_constant_type(
  constant : Constant,
  ty : Ty,
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  guard ty.node is ApplicationNode(symbol, arguments) && arguments.is_empty() else {
    fail_type(
      InvalidConstantType,
      span,
      "literal result type must be a nullary literal type",
    )
  }
  match constant {
    ConstInt({ value, .. }) =>
      match (symbol.builtin_kind, symbol.definition) {
        (Some(BuiltinInteger), DefinitionNone) => ()
        (None, DefinitionRange(lower, upper)) =>
          if value < lower || value > upper {
            fail_type(
              ConstantOutOfRange,
              span,
              "integer literal is outside the declared Range",
            )
          }
        _ =>
          fail_type(
            InvalidConstantType,
            span,
            "integer literal requires int or Range type",
          )
      }
    ConstReal({ value, .. }) =>
      match (symbol.builtin_kind, symbol.definition) {
        (Some(BuiltinReal), DefinitionNone) => ()
        (None, DefinitionFloat(exponent_digits, significand_digits)) =>
          if !real_fits_float(value, exponent_digits, significand_digits) {
            fail_type(
              NonRepresentableFloat,
              span,
              "real literal is not representable by the declared Float type",
            )
          }
        _ =>
          fail_type(
            InvalidConstantType,
            span,
            "real literal requires real or Float type",
          )
      }
    ConstStr(_) =>
      if symbol.builtin_kind != Some(BuiltinString) ||
        !(symbol.definition is DefinitionNone) {
        fail_type(
          InvalidConstantType,
          span,
          "string literal requires the trusted string type",
        )
      }
  }
}
