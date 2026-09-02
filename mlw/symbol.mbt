// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
pub(all) enum RoutineLogic {
  RLnone
  RLpv(PVariable)
  RLls(@logic.LSymbol)
  RLlemma
}

///|
pub(all) enum RoutineKind {
  RKnone
  RKlocal
  RKfunc
  RKpred
  RKlemma
} derive(Eq, Debug)

///|
fn validate_routine_logic_context(
  anchor : @identity.SemanticId,
  logic : RoutineLogic,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  match logic {
    RLnone | RLlemma => ()
    RLpv(variable) => require_mlw_context(anchor, variable.semantic_id(), span)
    RLls(symbol) => require_mlw_context(anchor, symbol.semantic_id(), span)
  }
}

///|
fn validate_pure_routine(
  cty : Cty,
  kind : RoutineKind,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  if kind is RKnone {
    return
  }
  if !cty.is_pure() {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "pure routine has side effects, may fail, or may diverge",
    )
  }
  if kind is RKlocal && !cty.view().freeze.view().regions.is_empty() {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "local pure routine captures frozen state",
    )
  }
  if (kind is RKfunc || kind is RKpred) && !cty.reads().is_empty() {
    let read = cty.reads()[0]
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "top-level pure routine depends on external program variable '\{read.view().name.view().name}'#\{read.semantic_id().local_id()}",
    )
  }
}

///|
fn validate_routine_logic_signature(
  cty : Cty,
  logic : RoutineLogic,
  span : @identity.SourceSpan?,
) -> Unit raise {
  guard logic is RLls(symbol) else { return }
  let cty_view = cty.view()
  let symbol_view = symbol.view()
  if symbol_view.argument_types.length() != cty_view.arguments.length() {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "routine and logical symbol have different arities",
    )
  }
  for index = 0; index < symbol_view.argument_types.length(); index = index + 1 {
    if symbol_view.argument_types[index] !=
      cty_view.arguments[index].view().ity.to_ty(span) {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "routine argument differs from its logical symbol",
      )
    }
  }
  match symbol_view.result_type {
    Some(result) =>
      if result != cty_view.result.to_ty(span) {
        fail_mlw(
          InvalidProgramDeclaration,
          span,
          "routine result differs from its logical symbol",
        )
      }
    None =>
      match cty_view.result.to_ty(span).view() {
        TyApp(type_symbol, _) if type_symbol.builtin_kind()
          is Some(BuiltinBoolean) => ()
        _ =>
          fail_mlw(
            InvalidProgramDeclaration,
            span,
            "predicate routine does not return boolean",
          )
      }
  }
}

///|
struct RoutineSymbol {
  context : @identity.CompilationContext
  id : @identity.SemanticId
  name : Bytes
  origin : @identity.Origin
  mut cty : Cty
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
pub fn RoutineSymbol::new(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  cty : Cty,
  logic : RoutineLogic,
  field : PVariable?,
  span : @identity.SourceSpan?,
) -> RoutineSymbol raise MlwError {
  let anchor = cty.context_anchor()
  if !context.contains(anchor) {
    fail_mlw(MlwContextMismatch, span, "routine belongs to another context")
  }
  validate_routine_logic_context(anchor, logic, span)
  if field is Some(field) {
    require_mlw_context(anchor, field.semantic_id(), span)
  }
  {
    context,
    id: context.fresh_id(),
    name: name.to_owned(),
    origin,
    cty,
    logic,
    field,
  }
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
    context,
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
pub fn RoutineSymbol::kind(self : RoutineSymbol) -> RoutineKind {
  match self.logic {
    RLnone => RKnone
    RLpv(_) => RKlocal
    RLls(symbol) =>
      if symbol.view().result_type is Some(_) {
        RKfunc
      } else {
        RKpred
      }
    RLlemma => RKlemma
  }
}

///|
pub fn RoutineSymbol::is_ghost(self : RoutineSymbol) -> Bool {
  self.cty.is_ghost()
}

///|
/// Rebuilds the computation type attached to a defined routine from the
/// cloned definition effect while retaining the symbol's enriched contract.
///
/// Why3 creates a routine symbol with `let_sym` only after rebuilding its
/// computation.  In particular, a clone substitution may erase a phantom
/// type parameter from the body effect.  Copying the source symbol's effect
/// would then retain a stale `spoils` entry.
fn RoutineSymbol::refresh_definition_cty(
  self : RoutineSymbol,
  computation : Cty,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  let view = self.cty.view()
  let computation_view = computation.view()
  if view.result != computation_view.result {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "routine definition result differs from its symbol",
    )
  }
  let effect = if view.effect.view().ghost &&
    !computation_view.effect.view().ghost {
    computation_view.effect.ghostify(true, span)
  } else {
    computation_view.effect
  }
  self.cty = Cty::new_with_variables(
    view.program_variables,
    view.arguments,
    view.preconditions,
    view.postconditions,
    view.exceptional_postconditions,
    view.oldies,
    effect,
    view.result,
    span,
    mask=view.mask,
  )
}

///|
pub fn RoutineSymbol::new_with_logic(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  cty : Cty,
  logic : RoutineLogic,
  field : PVariable?,
  span : @identity.SourceSpan?,
) -> RoutineSymbol raise {
  if !(origin.kind().view() is UserKind) {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "program routine requires user provenance",
    )
  }
  let anchor = cty.context_anchor()
  if !context.contains(anchor) {
    fail_mlw(MlwContextMismatch, span, "routine belongs to another context")
  }
  validate_routine_logic_context(anchor, logic, span)
  if field is Some(field) {
    require_mlw_context(anchor, field.semantic_id(), span)
  }
  let kind = match logic {
    RLnone => RKnone
    RLpv(_) => RKlocal
    RLls(symbol) =>
      if symbol.view().result_type is Some(_) {
        RKfunc
      } else {
        RKpred
      }
    RLlemma => RKlemma
  }
  validate_pure_routine(cty, kind, span)
  validate_routine_logic_signature(cty, logic, span)
  {
    context,
    id: context.fresh_id(),
    name: name.to_owned(),
    origin,
    cty,
    logic,
    field,
  }
}

///|
fn RoutineSymbol::compilation_context(
  self : RoutineSymbol,
) -> @identity.CompilationContext {
  self.context
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
