// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
/// A semantically identified type variable. Its spelling is diagnostic data,
/// never its equality key.
struct TyVarSymbol {
  id : @identity.SemanticId
  name : Bytes
  origin : @identity.Origin
}

///|
/// An immutable semantic type. Construction is restricted to the smart
/// constructors in this package.
struct Ty {
  node : TyNode
  allocation_tag : Int64
}

///|
priv enum TyNode {
  VariableNode(TyVarSymbol)
  ApplicationNode(TypeSymbol, Array[Ty])
}

///|
priv enum TypeDefinition {
  DefinitionNone
  DefinitionAlias(Ty)
  DefinitionRange(BigInt, BigInt)
  DefinitionFloat(Int, Int)
}

///|
let interned_type_tags : Ref[Map[Ty, Int64]] = Ref(Map([]))

///|
let next_type_allocation_tag : Ref[Int64] = Ref(0L)

///|
fn make_type(node : TyNode) -> Ty {
  let candidate = { node, allocation_tag: -1L }
  match interned_type_tags.val.get(candidate) {
    Some(allocation_tag) => { node, allocation_tag }
    None => {
      let allocation_tag = next_type_allocation_tag.val
      next_type_allocation_tag.val = allocation_tag + 1L
      interned_type_tags.val[candidate] = allocation_tag
      { node, allocation_tag }
    }
  }
}

///|
/// Primitive classes needed to validate exact literals. The marker is
/// semantic metadata attached by builtin construction; canonical identity
/// still comes from the symbol and its origin.
pub(all) enum BuiltinTypeKind {
  BuiltinInteger
  BuiltinReal
  BuiltinBoolean
  BuiltinString
} derive(Eq, Debug)

///|
/// A semantically identified type constructor. Its definition and parameter
/// list are immutable after validation.
struct TypeSymbol {
  id : @identity.SemanticId
  name : Bytes
  origin : @identity.Origin
  parameters : Array[TyVarSymbol]
  definition : TypeDefinition
  builtin_kind : BuiltinTypeKind?
}

///|
/// Read-only views of semantic type nodes.
pub(all) enum TyView {
  TyVar(TyVarSymbol)
  TyApp(TypeSymbol, ArrayView[Ty])
}

///|
/// Read-only views of validated type definitions.
pub(all) enum TypeDefinitionView {
  NoDef
  Alias(Ty)
  Range(BigInt, BigInt)
  Float(Int, Int)
}

///|
/// Read-only metadata for a type constructor.
pub(all) struct TypeSymbolView {
  id : @identity.SemanticId
  name : Bytes
  origin : @identity.Origin
  parameters : ArrayView[TyVarSymbol]
  definition : TypeDefinitionView
}

///|
pub fn TyVarSymbol::new(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
) -> TyVarSymbol {
  { id: context.fresh_id(), name: name.to_owned(), origin }
}

///|
pub fn TyVarSymbol::semantic_id(self : TyVarSymbol) -> @identity.SemanticId {
  self.id
}

///|
pub fn TyVarSymbol::name(self : TyVarSymbol) -> BytesView {
  self.name[:]
}

///|
pub fn TyVarSymbol::origin(self : TyVarSymbol) -> @identity.Origin {
  self.origin
}

///|
pub impl Eq for TyVarSymbol with fn equal(self, other) {
  self.id == other.id
}

///|
pub impl Hash for TyVarSymbol with fn hash_combine(self, hasher) {
  hasher.combine(self.id)
}

///|
pub fn TypeSymbol::semantic_id(self : TypeSymbol) -> @identity.SemanticId {
  self.id
}

///|
pub fn TypeSymbol::name(self : TypeSymbol) -> BytesView {
  self.name[:]
}

///|
pub fn TypeSymbol::origin(self : TypeSymbol) -> @identity.Origin {
  self.origin
}

///|
pub fn TypeSymbol::arity(self : TypeSymbol) -> Int {
  self.parameters.length()
}

///|
pub fn TypeSymbol::builtin_kind(self : TypeSymbol) -> BuiltinTypeKind? {
  self.builtin_kind
}

///|
pub fn TypeSymbol::view(self : TypeSymbol) -> TypeSymbolView {
  let definition = match self.definition {
    DefinitionNone => NoDef
    DefinitionAlias(ty) => Alias(ty)
    DefinitionRange(lower, upper) => Range(lower, upper)
    DefinitionFloat(exponent_digits, significand_digits) =>
      Float(exponent_digits, significand_digits)
  }
  {
    id: self.id,
    name: self.name,
    origin: self.origin,
    parameters: self.parameters[:],
    definition,
  }
}

///|
pub impl Eq for TypeSymbol with fn equal(self, other) {
  self.id == other.id
}

///|
pub impl Hash for TypeSymbol with fn hash_combine(self, hasher) {
  hasher.combine(self.id)
}

///|
fn require_context_id(
  context : @identity.CompilationContext,
  id : @identity.SemanticId,
  span : @identity.SourceSpan?,
  operation : String,
) -> Unit raise TypeError {
  if !context.contains(id) {
    fail_type(ContextMismatch, span, operation)
  }
}

///|
fn validate_parameters(
  context : @identity.CompilationContext,
  parameters : ArrayView[TyVarSymbol],
  span : @identity.SourceSpan?,
) -> Array[TyVarSymbol] raise TypeError {
  let copied = parameters.to_owned()
  let seen : Map[TyVarSymbol, Unit] = Map([])
  for parameter in copied {
    require_context_id(
      context,
      parameter.semantic_id(),
      span,
      "type parameter belongs to another compilation context",
    )
    if seen.contains(parameter) {
      fail_type(DuplicateTypeParameter, span, "duplicate type parameter")
    }
    seen[parameter] = ()
  }
  copied
}

///|
fn make_type_symbol(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  parameters : Array[TyVarSymbol],
  definition : TypeDefinition,
  builtin_kind : BuiltinTypeKind?,
) -> TypeSymbol {
  {
    id: context.fresh_id(),
    name: name.to_owned(),
    origin,
    parameters,
    definition,
    builtin_kind,
  }
}

///|
/// Creates a user-visible abstract type constructor after validating parameter
/// identity and uniqueness.
pub fn TypeSymbol::new_abstract(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  parameters : ArrayView[TyVarSymbol],
  span : @identity.SourceSpan?,
) -> TypeSymbol raise TypeError {
  make_type_symbol(
    context,
    name,
    origin,
    validate_parameters(context, parameters, span),
    DefinitionNone,
    None,
  )
}

///|
/// Creates an alias whose free variables are all bound by its declared type
/// parameters. Alias applications are expanded by `Ty::app`.
pub fn TypeSymbol::new_alias(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  parameters : ArrayView[TyVarSymbol],
  target : Ty,
  span : @identity.SourceSpan?,
) -> TypeSymbol raise TypeError {
  let parameters = validate_parameters(context, parameters, span)
  require_context_id(
    context,
    target.context_anchor(),
    span,
    "alias target belongs to another compilation context",
  )
  let declared : Map[TyVarSymbol, Unit] = Map([])
  for parameter in parameters {
    declared[parameter] = ()
  }
  for variable in target.free_variables() {
    if !declared.contains(variable) {
      fail_type(
        UnboundTypeVariable,
        span,
        "alias contains an undeclared type variable",
      )
    }
  }
  make_type_symbol(
    context,
    name,
    origin,
    parameters,
    DefinitionAlias(target),
    None,
  )
}

///|
/// Creates Why3's exact bounded-integer type constructor.
///
/// As in `Ty.create_tysymbol`, Range types are nullary and an empty interval
/// is rejected at construction time.
pub fn TypeSymbol::new_range(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  lower : BigInt,
  upper : BigInt,
  span : @identity.SourceSpan?,
) -> TypeSymbol raise TypeError {
  if lower > upper {
    fail_type(InvalidRange, span, "Range lower bound exceeds upper bound")
  }
  make_type_symbol(
    context,
    name,
    origin,
    [],
    DefinitionRange(lower, upper),
    None,
  )
}

///|
/// Creates Why3's floating-point format type constructor.
///
/// Float types are nullary. Both format dimensions must be strictly positive,
/// matching `Ty.create_tysymbol`.
pub fn TypeSymbol::new_float(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  exponent_digits : Int,
  significand_digits : Int,
  span : @identity.SourceSpan?,
) -> TypeSymbol raise TypeError {
  if exponent_digits < 1 || significand_digits < 1 {
    fail_type(
      InvalidFloat,
      span,
      "Float exponent and significand digits must both be positive",
    )
  }
  make_type_symbol(
    context,
    name,
    origin,
    [],
    DefinitionFloat(exponent_digits, significand_digits),
    None,
  )
}

///|
/// Creates a primitive symbol owned by a compilation context. Environment
/// construction uses this for Why3's `int`, `real`, `bool`, and `string`
/// builtins; the marker participates only in literal validation.
pub fn TypeSymbol::new_builtin(
  context : @identity.CompilationContext,
  name : BytesView,
  origin : @identity.Origin,
  kind : BuiltinTypeKind,
) -> TypeSymbol {
  make_type_symbol(context, name, origin, [], DefinitionNone, Some(kind))
}

///|
pub fn Ty::variable(symbol : TyVarSymbol) -> Ty {
  make_type(VariableNode(symbol))
}

///|
fn Ty::application_unchecked(symbol : TypeSymbol, arguments : Array[Ty]) -> Ty {
  make_type(ApplicationNode(symbol, arguments))
}

///|
/// Applies a validated type constructor. Aliases are expanded immediately, so
/// no public API can create an alias application or an arity-invalid type.
pub fn Ty::app(
  symbol : TypeSymbol,
  arguments : ArrayView[Ty],
  span : @identity.SourceSpan?,
) -> Ty raise TypeError {
  if arguments.length() != symbol.arity() {
    fail_type(
      ArityMismatch,
      span,
      "type constructor expected \{symbol.arity()} arguments but received \{arguments.length()}",
    )
  }
  let copied = arguments.to_owned()
  for argument in copied {
    if !symbol.semantic_id().same_context(argument.context_anchor()) {
      fail_type(
        ContextMismatch,
        span,
        "type application combines different compilation contexts",
      )
    }
  }
  match symbol.definition {
    DefinitionAlias(target) => {
      let mut substitution = TySubstitution::new()
      for index, parameter in symbol.parameters {
        substitution = substitution.bind(parameter, copied[index], span)
      }
      substitution.apply(target, span)
    }
    DefinitionNone | DefinitionRange(_, _) | DefinitionFloat(_, _) =>
      Ty::application_unchecked(symbol, copied)
  }
}

///|
pub fn Ty::view(self : Ty) -> TyView {
  match self.node {
    VariableNode(symbol) => TyVar(symbol)
    ApplicationNode(symbol, arguments) => TyApp(symbol, arguments[:])
  }
}

///|
pub fn Ty::context_anchor(self : Ty) -> @identity.SemanticId {
  match self.node {
    VariableNode(symbol) => symbol.semantic_id()
    ApplicationNode(symbol, _) => symbol.semantic_id()
  }
}

///|
/// Returns Why3's hash-cons allocation observer for deterministic set folds.
///
/// The tag is runtime metadata and is deliberately excluded from equality,
/// hashing, and canonical serialization.
pub fn Ty::allocation_order(self : Ty) -> Int64 {
  self.allocation_tag
}

///|
pub impl Eq for Ty with fn equal(self, other) {
  match (self.node, other.node) {
    (VariableNode(left), VariableNode(right)) => left == right
    (
      ApplicationNode(left_symbol, left_arguments),
      ApplicationNode(right_symbol, right_arguments),
    ) => left_symbol == right_symbol && left_arguments == right_arguments
    _ => false
  }
}

///|
pub impl Hash for Ty with fn hash_combine(self, hasher) {
  match self.node {
    VariableNode(symbol) => {
      hasher.combine(0)
      hasher.combine(symbol)
    }
    ApplicationNode(symbol, arguments) => {
      hasher.combine(1)
      hasher.combine(symbol)
      for argument in arguments {
        hasher.combine(argument)
      }
    }
  }
}

///|
fn collect_free_variables(
  ty : Ty,
  seen : Map[TyVarSymbol, Unit],
  result : Array[TyVarSymbol],
) -> Unit {
  match ty.node {
    VariableNode(symbol) =>
      if !seen.contains(symbol) {
        seen[symbol] = ()
        result.push(symbol)
      }
    ApplicationNode(_, arguments) =>
      for argument in arguments {
        collect_free_variables(argument, seen, result)
      }
  }
}

///|
/// Returns free variables in deterministic first-preorder-encounter order.
pub fn Ty::free_variables(self : Ty) -> Array[TyVarSymbol] {
  let result : Array[TyVarSymbol] = []
  collect_free_variables(self, Map([]), result)
  result
}

///|
pub fn Ty::is_closed(self : Ty) -> Bool {
  self.free_variables().is_empty()
}
