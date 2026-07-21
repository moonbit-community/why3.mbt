// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) struct ProgramTypeArgumentFlag {
  frozen : Bool
  exposed : Bool
  liable : Bool
  fixed : Bool
  visible : Bool
} derive(Eq, Debug)

///|
pub(all) struct ProgramTypeFlags {
  nonfree : Bool
  private_ : Bool
  mutable_ : Bool
  fragile : Bool
  argument_flags : Array[ProgramTypeArgumentFlag]
  region_flags : Array[ProgramTypeArgumentFlag]
} derive(Eq, Debug)

///|
pub(all) enum ProgramTypeDefinition {
  ProgramNoDef
  ProgramAlias(Ity)
  ProgramRange(BigInt, BigInt)
  ProgramFloat(Int, Int)
}

///|
struct ProgramTypeSymbol {
  id : @identity.SemanticId
  logic_type : @logic.TypeSymbol
  origin : @identity.Origin
  flags : ProgramTypeFlags
  definition : ProgramTypeDefinition
  mutable_fields : Array[PVariable]
  immutable_fields : Array[PVariable]
}

///|
priv enum ItyNode {
  ItyVariable(@logic.TyVarSymbol)
  ItyApplication(ProgramTypeSymbol, Array[Ity])
}

///|
struct Ity {
  node : ItyNode
}

///|
struct PVariable {
  id : @identity.SemanticId
  name : @theory.SemanticName
  ity : Ity
  ghost : Bool
  pure_symbol : @logic.VSymbol
}

///|
pub(all) struct ProgramTypeSymbolView {
  id : @identity.SemanticId
  logic_type : @logic.TypeSymbol
  origin : @identity.Origin
  flags : ProgramTypeFlags
  definition : ProgramTypeDefinition
  mutable_fields : ArrayView[PVariable]
  immutable_fields : ArrayView[PVariable]
}

///|
pub(all) enum ItyView {
  ItyVar(@logic.TyVarSymbol)
  ItyApp(ProgramTypeSymbol, ArrayView[Ity])
}

///|
pub(all) struct PVariableView {
  id : @identity.SemanticId
  name : @theory.SemanticName
  ity : Ity
  ghost : Bool
  pure_symbol : @logic.VSymbol
}

///|
pub fn ProgramTypeSymbol::trusted_new(
  context : @identity.CompilationContext,
  logic_type : @logic.TypeSymbol,
  origin : @identity.Origin,
  flags : ProgramTypeFlags,
  definition : ProgramTypeDefinition,
  mutable_fields : ArrayView[PVariable],
  immutable_fields : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> ProgramTypeSymbol raise MlwError {
  require_snapshot_program_origin(origin, span)
  let anchor = logic_type.semantic_id()
  if !context.contains(anchor) {
    fail_mlw(
      MlwContextMismatch,
      span,
      "program type belongs to another context",
    )
  }
  if !flags.region_flags.is_empty() {
    fail_mlw(
      UnsupportedProgramType,
      span,
      "snapshot program type contains regions",
    )
  }
  match definition {
    ProgramAlias(target) =>
      require_mlw_context(anchor, target.context_anchor(), span)
    ProgramNoDef | ProgramRange(_, _) | ProgramFloat(_, _) => ()
  }
  let mutable_fields = mutable_fields.to_owned()
  let immutable_fields = immutable_fields.to_owned()
  for field in mutable_fields {
    require_mlw_context(anchor, field.id, span)
  }
  for field in immutable_fields {
    require_mlw_context(anchor, field.id, span)
  }
  {
    id: context.fresh_id(),
    logic_type,
    origin,
    flags,
    definition,
    mutable_fields,
    immutable_fields,
  }
}

///|
pub fn ProgramTypeSymbol::semantic_id(
  self : ProgramTypeSymbol,
) -> @identity.SemanticId {
  self.id
}

///|
pub fn ProgramTypeSymbol::view(
  self : ProgramTypeSymbol,
) -> ProgramTypeSymbolView {
  {
    id: self.id,
    logic_type: self.logic_type,
    origin: self.origin,
    flags: self.flags,
    definition: self.definition,
    mutable_fields: self.mutable_fields[:],
    immutable_fields: self.immutable_fields[:],
  }
}

///|
pub impl Eq for ProgramTypeSymbol with fn equal(self, other) {
  self.id == other.id
}

///|
pub impl Hash for ProgramTypeSymbol with fn hash_combine(self, hasher) {
  hasher.combine(self.id)
}

///|
pub fn Ity::app(
  symbol : ProgramTypeSymbol,
  arguments : ArrayView[Ity],
  span : @identity.SourceSpan?,
) -> Ity raise MlwError {
  if arguments.length() != symbol.logic_type.arity() {
    fail_mlw(
      UnsupportedProgramType,
      span,
      "program type application has the wrong arity",
    )
  }
  let arguments = arguments.to_owned()
  for argument in arguments {
    require_mlw_context(symbol.id, argument.context_anchor(), span)
  }
  { node: ItyApplication(symbol, arguments) }
}

///|
/// Preserves a trusted polymorphic program type until a call site supplies a
/// monomorphic instantiation. User routines must reject this shape at their
/// declaration boundary.
pub fn Ity::variable(symbol : @logic.TyVarSymbol) -> Ity {
  { node: ItyVariable(symbol) }
}

///|
pub fn Ity::view(self : Ity) -> ItyView {
  match self.node {
    ItyVariable(symbol) => ItyVar(symbol)
    ItyApplication(symbol, arguments) => ItyApp(symbol, arguments[:])
  }
}

///|
pub fn Ity::context_anchor(self : Ity) -> @identity.SemanticId {
  match self.node {
    ItyVariable(symbol) => symbol.semantic_id()
    ItyApplication(symbol, _) => symbol.id
  }
}

///|
pub fn Ity::to_ty(
  self : Ity,
  span : @identity.SourceSpan?,
) -> @logic.Ty raise @logic.TypeError {
  match self.node {
    ItyVariable(symbol) => @logic.Ty::variable(symbol)
    ItyApplication(symbol, arguments) =>
      @logic.Ty::app(
        symbol.logic_type,
        [
          for argument in arguments => argument.to_ty(span)
        ],
        span,
      )
  }
}

///|
pub impl Eq for Ity with fn equal(self, other) {
  match (self.node, other.node) {
    (ItyVariable(left), ItyVariable(right)) => left == right
    (ItyApplication(left, left_args), ItyApplication(right, right_args)) =>
      left == right && left_args == right_args
    _ => false
  }
}

///|
pub impl Hash for Ity with fn hash_combine(self, hasher) {
  match self.node {
    ItyVariable(symbol) => {
      hasher.combine(0)
      hasher.combine(symbol)
    }
    ItyApplication(symbol, arguments) => {
      hasher.combine(1)
      hasher.combine(symbol)
      for argument in arguments {
        hasher.combine(argument)
      }
    }
  }
}

///|
pub fn Ity::is_closed(self : Ity) -> Bool {
  match self.node {
    ItyVariable(_) => false
    ItyApplication(_, arguments) => arguments.all(Ity::is_closed)
  }
}

///|
/// Converts a core type through the exact program-type symbols already
/// present in the current Pmodule namespace. No symbol is reconstructed from
/// a spelling.
pub fn Ity::from_ty(
  program_space : ProgramNamespace,
  ty : @logic.Ty,
  span : @identity.SourceSpan?,
) -> Ity raise {
  match ty.view() {
    TyVar(variable) => Ity::variable(variable)
    TyApp(logic_symbol, arguments) => {
      let program_symbol = program_space.find_type_by_logic(logic_symbol, span)
      Ity::app(
        program_symbol,
        [
          for argument in arguments => {
            Ity::from_ty(program_space, argument, span)
          }
        ],
        span,
      )
    }
  }
}

///|
pub fn PVariable::trusted_new(
  context : @identity.CompilationContext,
  name : @theory.SemanticName,
  ity : Ity,
  ghost : Bool,
  span : @identity.SourceSpan?,
) -> PVariable raise {
  if !context.contains(ity.context_anchor()) {
    fail_mlw(
      MlwContextMismatch,
      span,
      "program variable belongs to another context",
    )
  }
  let name_view = name.view()
  let origin = @identity.Origin::user(
    name_view.name,
    name_view.source_span,
    name_view.attributes,
  )
  let pure_symbol = @logic.VSymbol::new(
    context,
    name_view.name,
    origin,
    ity.to_ty(span),
    span,
  )
  { id: context.fresh_id(), name, ity, ghost, pure_symbol }
}

///|
pub fn PVariable::semantic_id(self : PVariable) -> @identity.SemanticId {
  self.id
}

///|
pub fn PVariable::view(self : PVariable) -> PVariableView {
  {
    id: self.id,
    name: self.name,
    ity: self.ity,
    ghost: self.ghost,
    pure_symbol: self.pure_symbol,
  }
}

///|
pub impl Eq for PVariable with fn equal(self, other) {
  self.id == other.id
}

///|
pub impl Hash for PVariable with fn hash_combine(self, hasher) {
  hasher.combine(self.id)
}
