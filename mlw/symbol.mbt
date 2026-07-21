// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum RoutineLogic {
  RLnone
  RLls(@logic.LSymbol)
}

///|
struct RoutineSymbol {
  id : @identity.SemanticId
  name : Bytes
  origin : @identity.Origin
  cty : Cty
  logic : RoutineLogic
  field : PVariable?
}

///|
pub(all) struct RoutineSymbolView {
  id : @identity.SemanticId
  name : Bytes
  origin : @identity.Origin
  cty : Cty
  logic : RoutineLogic
  field : PVariable?
}

///|
pub fn RoutineSymbol::trusted_new(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  cty : Cty,
  logic : RoutineLogic,
  field : PVariable?,
  span : @identity.SourceSpan?,
) -> RoutineSymbol raise MlwError {
  require_snapshot_program_origin(origin, span)
  let anchor = cty.context_anchor()
  if !context.contains(anchor) {
    fail_mlw(MlwContextMismatch, span, "routine belongs to another context")
  }
  match logic {
    RLnone => ()
    RLls(symbol) => require_mlw_context(anchor, symbol.semantic_id(), span)
  }
  if field is Some(field) {
    require_mlw_context(anchor, field.semantic_id(), span)
  }
  { id: context.fresh_id(), name: name.to_owned(), origin, cty, logic, field }
}

///|
/// Creates an ordinary user routine. Logical projections and fields are
/// intentionally unavailable at this boundary; the MVP accepts only RLnone.
pub fn RoutineSymbol::new_user(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  cty : Cty,
  span : @identity.SourceSpan?,
) -> RoutineSymbol raise MlwError {
  if !(origin.kind().view() is UserKind) {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "user routine requires user provenance",
    )
  }
  let anchor = cty.context_anchor()
  if !context.contains(anchor) {
    fail_mlw(MlwContextMismatch, span, "routine belongs to another context")
  }
  {
    id: context.fresh_id(),
    name: name.to_owned(),
    origin,
    cty,
    logic: RLnone,
    field: None,
  }
}

///|
pub fn RoutineSymbol::semantic_id(self : RoutineSymbol) -> @identity.SemanticId {
  self.id
}

///|
pub fn RoutineSymbol::view(self : RoutineSymbol) -> RoutineSymbolView {
  {
    id: self.id,
    name: self.name,
    origin: self.origin,
    cty: self.cty,
    logic: self.logic,
    field: self.field,
  }
}

///|
pub impl Eq for RoutineSymbol with fn equal(self, other) {
  self.id == other.id
}

///|
pub impl Hash for RoutineSymbol with fn hash_combine(self, hasher) {
  hasher.combine(self.id)
}
