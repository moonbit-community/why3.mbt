// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
struct VSymbol {
  id : @identity.SemanticId
  identifier_id : @identity.IdentifierId
  clone_source_identifier_id : @identity.IdentifierId?
  name : Bytes
  origin : @identity.Origin
  ty : Ty
}

///|
priv enum LogicSymbolRole {
  OrdinaryRole
  ConstructorRole(Int)
  ProjectionRole
}

///|
pub(all) enum LogicSymbolRoleView {
  Ordinary
  Constructor(Int)
  Projection
} derive(Eq, Debug)

///|
struct LSymbol {
  id : @identity.SemanticId
  name : Bytes
  origin : @identity.Origin
  type_parameters : Array[TyVarSymbol]
  argument_types : Array[Ty]
  result_type : Ty?
  role : LogicSymbolRole
}

///|
struct PrSymbol {
  id : @identity.SemanticId
  name : Bytes
  origin : @identity.Origin
}

///|
pub(all) struct VSymbolView {
  id : @identity.SemanticId
  name : Bytes
  origin : @identity.Origin
  ty : Ty
}

///|
pub(all) struct LSymbolView {
  id : @identity.SemanticId
  name : Bytes
  origin : @identity.Origin
  type_parameters : ArrayView[TyVarSymbol]
  argument_types : ArrayView[Ty]
  result_type : Ty?
  role : LogicSymbolRoleView
}

///|
pub(all) struct PrSymbolView {
  id : @identity.SemanticId
  name : Bytes
  origin : @identity.Origin
}

///|
pub fn VSymbol::new(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  ty : Ty,
  span : @identity.SourceSpan?,
) -> VSymbol raise TypeError {
  require_context_id(
    context,
    ty.context_anchor(),
    span,
    "variable type belongs to another compilation context",
  )
  let id = context.fresh_id()
  {
    id,
    identifier_id: id.identifier_id(),
    clone_source_identifier_id: None,
    name: name.to_owned(),
    origin,
    ty,
  }
}

///|
fn VSymbol::fresh_like(
  self : VSymbol,
  context : @identity.CompilationContext,
  span : @identity.SourceSpan?,
) -> VSymbol raise TypeError {
  require_context_id(
    context,
    self.ty.context_anchor(),
    span,
    "cloned variable type belongs to another compilation context",
  )
  let id = context.fresh_id()
  {
    id,
    identifier_id: context.fresh_identifier_clone_id(self.identifier_id),
    clone_source_identifier_id: Some(self.identifier_id),
    name: self.name,
    origin: self.origin,
    ty: self.ty,
  }
}

///|
/// Creates a semantically fresh variable while retaining the Why3-style
/// identifier clone edge used by checkpoint provenance tracking.
pub fn VSymbol::clone_with_type(
  self : VSymbol,
  context : @identity.CompilationContext,
  ty : Ty,
  span : @identity.SourceSpan?,
) -> VSymbol raise TypeError {
  self.clone_as(context, self.name, self.origin, ty, span)
}

///|
/// Creates a semantically fresh variable with selected presentation metadata
/// while retaining this variable as its Why3-style identifier clone source.
pub fn VSymbol::clone_as(
  self : VSymbol,
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  ty : Ty,
  span : @identity.SourceSpan?,
) -> VSymbol raise TypeError {
  require_context_id(
    context,
    ty.context_anchor(),
    span,
    "cloned variable type belongs to another compilation context",
  )
  let id = context.fresh_id()
  {
    id,
    identifier_id: context.fresh_identifier_clone_id(self.identifier_id),
    clone_source_identifier_id: Some(self.identifier_id),
    name: name.to_owned(),
    origin,
    ty,
  }
}

///|
/// Clones only the underlying Why3-style identifier. Semantic equality and
/// allocation remain unchanged; this is used when opening and reclosing a
/// binder changes identifier provenance but not the represented variable.
pub fn VSymbol::clone_identifier(
  self : VSymbol,
  context : @identity.CompilationContext,
  span : @identity.SourceSpan?,
) -> VSymbol raise TypeError {
  self.clone_identifier_with_origin(context, self.origin, span)
}

///|
/// Clones only the underlying Why3-style identifier while replacing its
/// presentation provenance. Transformation code uses this when opening a
/// closure keeps the represented variable but makes the opened identifier
/// observable at a generated checkpoint.
pub fn VSymbol::clone_identifier_with_origin(
  self : VSymbol,
  context : @identity.CompilationContext,
  origin : @identity.Origin,
  span : @identity.SourceSpan?,
) -> VSymbol raise TypeError {
  require_context_id(
    context,
    self.id,
    span,
    "identifier clone belongs to another compilation context",
  )
  {
    ..self,
    identifier_id: context.fresh_identifier_clone_id(self.identifier_id),
    clone_source_identifier_id: Some(self.identifier_id),
    origin,
  }
}

///|
pub fn VSymbol::semantic_id(self : VSymbol) -> @identity.SemanticId {
  self.id
}

///|
pub fn VSymbol::identifier_id(self : VSymbol) -> @identity.IdentifierId {
  self.identifier_id
}

///|
pub fn VSymbol::clone_source_identifier_id(
  self : VSymbol,
) -> @identity.IdentifierId? {
  self.clone_source_identifier_id
}

///|
pub fn VSymbol::ty(self : VSymbol) -> Ty {
  self.ty
}

///|
pub fn VSymbol::view(self : VSymbol) -> VSymbolView {
  { id: self.id, name: self.name, origin: self.origin, ty: self.ty }
}

///|
pub impl Eq for VSymbol with fn equal(self, other) {
  self.id == other.id
}

///|
pub impl Hash for VSymbol with fn hash_combine(self, hasher) {
  hasher.combine(self.id)
}

///|
fn append_type_variables(
  ty : Ty,
  seen : Map[TyVarSymbol, Unit],
  variables : Array[TyVarSymbol],
) -> Unit {
  for variable in ty.free_variables() {
    if !seen.contains(variable) {
      seen[variable] = ()
      variables.push(variable)
    }
  }
}

///|
fn make_logic_symbol(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  argument_types : ArrayView[Ty],
  result_type : Ty?,
  role : LogicSymbolRole,
  span : @identity.SourceSpan?,
) -> LSymbol raise TypeError {
  let arguments = argument_types.to_owned()
  let variables : Array[TyVarSymbol] = []
  let seen : Map[TyVarSymbol, Unit] = Map([])
  for argument in arguments {
    require_context_id(
      context,
      argument.context_anchor(),
      span,
      "logic symbol argument belongs to another compilation context",
    )
    append_type_variables(argument, seen, variables)
  }
  if result_type is Some(result) {
    require_context_id(
      context,
      result.context_anchor(),
      span,
      "logic symbol result belongs to another compilation context",
    )
    append_type_variables(result, seen, variables)
  }
  {
    id: context.fresh_id(),
    name: name.to_owned(),
    origin,
    type_parameters: variables,
    argument_types: arguments,
    result_type,
    role,
  }
}

///|
pub fn LSymbol::new_function(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  argument_types : ArrayView[Ty],
  result_type : Ty,
  span : @identity.SourceSpan?,
) -> LSymbol raise TypeError {
  make_logic_symbol(
    context,
    name,
    origin,
    argument_types,
    Some(result_type),
    OrdinaryRole,
    span,
  )
}

///|
pub fn LSymbol::new_predicate(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  argument_types : ArrayView[Ty],
  span : @identity.SourceSpan?,
) -> LSymbol raise TypeError {
  make_logic_symbol(
    context,
    name,
    origin,
    argument_types,
    None,
    OrdinaryRole,
    span,
  )
}

///|
pub fn LSymbol::new_constructor(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  argument_types : ArrayView[Ty],
  result_type : Ty,
  constructor_count : Int,
  span : @identity.SourceSpan?,
) -> LSymbol raise TypeError {
  if constructor_count < 1 {
    fail_type(InvalidDeclaration, span, "constructor count must be positive")
  }
  make_logic_symbol(
    context,
    name,
    origin,
    argument_types,
    Some(result_type),
    ConstructorRole(constructor_count),
    span,
  )
}

///|
pub fn LSymbol::new_projection(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  source_type : Ty,
  result_type : Ty,
  span : @identity.SourceSpan?,
) -> LSymbol raise TypeError {
  make_logic_symbol(
    context,
    name,
    origin,
    [source_type],
    Some(result_type),
    ProjectionRole,
    span,
  )
}

///|
pub fn LSymbol::semantic_id(self : LSymbol) -> @identity.SemanticId {
  self.id
}

///|
pub fn LSymbol::view(self : LSymbol) -> LSymbolView {
  let role = match self.role {
    OrdinaryRole => Ordinary
    ConstructorRole(count) => Constructor(count)
    ProjectionRole => Projection
  }
  {
    id: self.id,
    name: self.name,
    origin: self.origin,
    type_parameters: self.type_parameters[:],
    argument_types: self.argument_types[:],
    result_type: self.result_type,
    role,
  }
}

///|
pub impl Eq for LSymbol with fn equal(self, other) {
  self.id == other.id
}

///|
pub impl Hash for LSymbol with fn hash_combine(self, hasher) {
  hasher.combine(self.id)
}

///|
pub fn PrSymbol::new(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
) -> PrSymbol {
  { id: context.fresh_id(), name: name.to_owned(), origin }
}

///|
pub fn PrSymbol::semantic_id(self : PrSymbol) -> @identity.SemanticId {
  self.id
}

///|
pub fn PrSymbol::view(self : PrSymbol) -> PrSymbolView {
  { id: self.id, name: self.name, origin: self.origin }
}

///|
pub impl Eq for PrSymbol with fn equal(self, other) {
  self.id == other.id
}

///|
pub impl Hash for PrSymbol with fn hash_combine(self, hasher) {
  hasher.combine(self.id)
}
