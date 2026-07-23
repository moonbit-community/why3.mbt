// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn canonical_type_identity(
  numbering : GlobalSymbolNumbering,
  id : @identity.SemanticId,
) -> CanonicalValue {
  canonical_array([
    canonical_text(GlobalSymbolKind::Type.canonical_name()),
    Unsigned(numbering.encounter(Type, id)),
  ])
}

///|
fn canonical_ty(
  numbering : GlobalSymbolNumbering,
  ty : @logic.Ty,
) -> CanonicalValue {
  match ty.view() {
    TyVar(variable) =>
      canonical_array([
        canonical_text(b"TyVar"),
        canonical_type_identity(numbering, variable.semantic_id()),
      ])
    TyApp(symbol, arguments) => {
      let symbol_id = canonical_type_identity(numbering, symbol.semantic_id())
      let encoded_arguments = [
        for argument in arguments => canonical_ty(numbering, argument)
      ]
      canonical_array([
        canonical_text(b"TyApp"),
        symbol_id,
        canonical_array(encoded_arguments),
      ])
    }
  }
}

///|
fn canonical_type_definition(
  numbering : GlobalSymbolNumbering,
  definition : @logic.TypeDefinitionView,
) -> CanonicalValue {
  match definition {
    NoDef => canonical_array([canonical_text(b"TypeDefinition.NoDef")])
    Alias(ty) =>
      canonical_array([
        canonical_text(b"TypeDefinition.Alias"),
        canonical_ty(numbering, ty),
      ])
    Range(lower, upper) =>
      canonical_array([
        canonical_text(b"TypeDefinition.Range"),
        Decimal(lower),
        Decimal(upper),
      ])
    Float(exponent_digits, significand_digits) =>
      canonical_array([
        canonical_text(b"TypeDefinition.Float"),
        Signed(exponent_digits.to_int64()),
        Signed(significand_digits.to_int64()),
      ])
  }
}

///|
fn canonical_type_symbol(
  numbering : GlobalSymbolNumbering,
  symbol : @logic.TypeSymbol,
) -> CanonicalValue {
  let view = symbol.view()
  let symbol_id = canonical_type_identity(numbering, view.id)
  let parameters = [
    for parameter in view.parameters => {
      canonical_type_identity(numbering, parameter.semantic_id())
    }
  ]
  canonical_array([
    canonical_text(b"TypeSymbol"),
    symbol_id,
    canonical_hex(view.name),
    canonical_origin(view.origin),
    canonical_array(parameters),
    canonical_type_definition(numbering, view.definition),
  ])
}

///|
/// Encodes one immutable semantic type using a fresh first-encounter symbol
/// numbering traversal.
pub fn encode_ty(ty : @logic.Ty) -> CanonicalJson {
  encode_canonical_value(canonical_ty(GlobalSymbolNumbering::new(), ty))
}

///|
/// Encodes a type declaration and its definition using frozen schema-v2 field
/// order and first-preorder-encounter identities.
pub fn encode_type_symbol(symbol : @logic.TypeSymbol) -> CanonicalJson {
  encode_canonical_value(
    canonical_type_symbol(GlobalSymbolNumbering::new(), symbol),
  )
}
