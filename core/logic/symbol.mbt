// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
struct VSymbol {
  id : @identity.SemanticId
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
  { id: context.fresh_id(), name: name.to_owned(), origin, ty }
}

///|
fn VSymbol::fresh_like(
  self : VSymbol,
  context : @identity.CompilationContext,
  span : @identity.SourceSpan?,
) -> VSymbol raise TypeError {
  VSymbol::new(context, self.name, self.origin, self.ty, span)
}

///|
pub fn VSymbol::semantic_id(self : VSymbol) -> @identity.SemanticId {
  self.id
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
pub fn LSymbol::trusted_constructor(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  argument_types : ArrayView[Ty],
  result_type : Ty,
  constructor_count : Int,
  span : @identity.SourceSpan?,
) -> LSymbol raise TypeError {
  require_snapshot_origin(origin, span)
  if constructor_count < 1 {
    fail_type(
      InvalidDeclaration,
      span,
      "trusted constructor count must be positive",
    )
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
pub fn LSymbol::trusted_projection(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  source_type : Ty,
  result_type : Ty,
  span : @identity.SourceSpan?,
) -> LSymbol raise TypeError {
  require_snapshot_origin(origin, span)
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
