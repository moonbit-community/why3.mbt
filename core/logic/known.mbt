// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum DeclDependency {
  TypeDependency(TypeSymbol)
  LogicDependency(LSymbol)
  PropositionDependency(PrSymbol)
}

///|
fn DeclDependency::kind_tag(self : DeclDependency) -> Int {
  match self {
    TypeDependency(_) => 0
    LogicDependency(_) => 1
    PropositionDependency(_) => 2
  }
}

///|
pub fn DeclDependency::semantic_id(
  self : DeclDependency,
) -> @identity.SemanticId {
  match self {
    TypeDependency(symbol) => symbol.semantic_id()
    LogicDependency(symbol) => symbol.semantic_id()
    PropositionDependency(symbol) => symbol.semantic_id()
  }
}

///|
pub impl Eq for DeclDependency with fn equal(self, other) {
  self.kind_tag() == other.kind_tag() &&
  self.semantic_id() == other.semantic_id()
}

///|
pub impl Hash for DeclDependency with fn hash_combine(self, hasher) {
  hasher.combine(self.kind_tag())
  hasher.combine(self.semantic_id())
}

///|
priv struct DependencyCollector {
  seen : Map[(Int, @identity.SemanticId), Unit]
  values : Array[DeclDependency]
}

///|
fn DependencyCollector::new() -> DependencyCollector {
  { seen: Map([]), values: [] }
}

///|
fn DependencyCollector::add(
  self : DependencyCollector,
  dependency : DeclDependency,
) -> Unit {
  let key = (dependency.kind_tag(), dependency.semantic_id())
  if !self.seen.contains(key) {
    self.seen[key] = ()
    self.values.push(dependency)
  }
}

///|
fn collect_ty_dependencies(collector : DependencyCollector, ty : Ty) -> Unit {
  match ty.node {
    VariableNode(_) => ()
    ApplicationNode(symbol, arguments) => {
      collector.add(TypeDependency(symbol))
      for argument in arguments {
        collect_ty_dependencies(collector, argument)
      }
    }
  }
}

///|
fn collect_type_symbol_definition(
  collector : DependencyCollector,
  symbol : TypeSymbol,
) -> Unit {
  match symbol.definition {
    DefinitionAlias(ty) => collect_ty_dependencies(collector, ty)
    DefinitionNone | DefinitionRange(_, _) | DefinitionFloat(_, _) => ()
  }
}

///|
fn collect_logic_signature(
  collector : DependencyCollector,
  symbol : LSymbol,
) -> Unit {
  for ty in symbol.argument_types {
    collect_ty_dependencies(collector, ty)
  }
  if symbol.result_type is Some(ty) {
    collect_ty_dependencies(collector, ty)
  }
}

///|
fn collect_pattern_dependencies(
  collector : DependencyCollector,
  pattern : Pattern,
) -> Unit {
  collect_ty_dependencies(collector, pattern.ty)
  match pattern.node {
    WildPattern | VariablePattern(_) => ()
    ApplicationPattern(symbol, arguments) => {
      collector.add(LogicDependency(symbol))
      collect_logic_signature(collector, symbol)
      for argument in arguments {
        collect_pattern_dependencies(collector, argument)
      }
    }
    OrPattern(left, right) => {
      collect_pattern_dependencies(collector, left)
      collect_pattern_dependencies(collector, right)
    }
    AsPattern(inner, _) => collect_pattern_dependencies(collector, inner)
  }
}

///|
fn collect_term_dependencies(
  collector : DependencyCollector,
  term : Term,
) -> Unit {
  if term.result_type is Some(ty) {
    collect_ty_dependencies(collector, ty)
  }
  let recurse = fn(child) { collect_term_dependencies(collector, child) }
  match term.node {
    VariableTerm(variable) => collect_ty_dependencies(collector, variable.ty)
    ConstantTerm(_) | TrueTerm | FalseTerm => ()
    ApplicationTerm(symbol, instantiation, arguments) => {
      collector.add(LogicDependency(symbol))
      collect_logic_signature(collector, symbol)
      for entry in instantiation {
        collect_ty_dependencies(collector, entry.1)
      }
      for argument in arguments {
        recurse(argument)
      }
    }
    IfTerm(condition, then_branch, else_branch) => {
      recurse(condition)
      recurse(then_branch)
      recurse(else_branch)
    }
    LetTerm(variable, value, body) => {
      collect_ty_dependencies(collector, variable.ty)
      recurse(value)
      recurse(body)
    }
    CaseTerm(scrutinee, branches) => {
      recurse(scrutinee)
      for branch in branches {
        collect_pattern_dependencies(collector, branch.pattern)
        recurse(branch.body)
      }
    }
    EpsilonTerm(variable, body) => {
      collect_ty_dependencies(collector, variable.ty)
      recurse(body)
    }
    QuantifiedTerm(_, binders, triggers, body) => {
      for binder in binders {
        collect_ty_dependencies(collector, binder.ty)
      }
      for group in triggers {
        for trigger in group {
          recurse(trigger)
        }
      }
      recurse(body)
    }
    BinaryTerm(_, left, right) => {
      recurse(left)
      recurse(right)
    }
    NotTerm(inner) => recurse(inner)
  }
}

///|
fn introduced_symbols(node : DeclNode) -> Array[DeclDependency] {
  let result : Array[DeclDependency] = []
  match node {
    TypeDeclaration(symbols) =>
      for symbol in symbols {
        result.push(TypeDependency(symbol))
      }
    DataDeclarationNode(declarations) =>
      for declaration in declarations {
        result.push(TypeDependency(declaration.type_symbol))
        for data_constructor in declaration.constructors {
          result.push(LogicDependency(data_constructor.symbol))
          for projection in data_constructor.projections {
            if projection is Some(projection) {
              result.push(LogicDependency(projection))
            }
          }
        }
      }
    ParameterDeclaration(symbol) => result.push(LogicDependency(symbol))
    LogicDeclaration(definitions) =>
      for definition in definitions {
        result.push(LogicDependency(definition.symbol))
      }
    InductiveDeclarationNode(declarations) =>
      for declaration in declarations {
        result.push(LogicDependency(declaration.predicate))
        for case_ in declaration.cases {
          result.push(PropositionDependency(case_.proposition))
        }
      }
    PropositionDeclaration(_, symbol, _) =>
      result.push(PropositionDependency(symbol))
  }
  result
}

///|
fn collect_node_dependencies(node : DeclNode) -> Array[DeclDependency] {
  let collector = DependencyCollector::new()
  match node {
    TypeDeclaration(symbols) =>
      for symbol in symbols {
        collect_type_symbol_definition(collector, symbol)
      }
    DataDeclarationNode(declarations) =>
      for declaration in declarations {
        for data_constructor in declaration.constructors {
          collect_logic_signature(collector, data_constructor.symbol)
          for projection in data_constructor.projections {
            if projection is Some(projection) {
              collect_logic_signature(collector, projection)
            }
          }
        }
      }
    ParameterDeclaration(symbol) => collect_logic_signature(collector, symbol)
    LogicDeclaration(definitions) =>
      for definition in definitions {
        collect_logic_signature(collector, definition.symbol)
        collect_term_dependencies(collector, definition.body)
      }
    InductiveDeclarationNode(declarations) =>
      for declaration in declarations {
        collect_logic_signature(collector, declaration.predicate)
        for case_ in declaration.cases {
          collect_term_dependencies(collector, case_.formula)
        }
      }
    PropositionDeclaration(_, _, formula) =>
      collect_term_dependencies(collector, formula)
  }
  collector.values
}

///|
fn validate_introduced_symbols(
  context : @identity.CompilationContext,
  introduced : ArrayView[DeclDependency],
  span : @identity.SourceSpan?,
) -> Unit raise TypeError {
  let seen : Map[(Int, @identity.SemanticId), Unit] = Map([])
  for dependency in introduced {
    require_context_id(
      context,
      dependency.semantic_id(),
      span,
      "declaration symbol belongs to another compilation context",
    )
    let key = (dependency.kind_tag(), dependency.semantic_id())
    if seen.contains(key) {
      fail_type(
        DuplicateDeclarationSymbol,
        span,
        "declaration introduces the same symbol twice",
      )
    }
    seen[key] = ()
  }
}

///|
fn make_decl(
  context : @identity.CompilationContext,
  origin : @identity.Origin,
  node : DeclNode,
  span : @identity.SourceSpan?,
) -> Decl raise TypeError {
  let introduced = introduced_symbols(node)
  validate_introduced_symbols(context, introduced, span)
  let introduced_keys : Map[(Int, @identity.SemanticId), Unit] = Map([])
  for dependency in introduced {
    introduced_keys[(dependency.kind_tag(), dependency.semantic_id())] = ()
  }
  let dependencies : Array[DeclDependency] = []
  for dependency in collect_node_dependencies(node) {
    let key = (dependency.kind_tag(), dependency.semantic_id())
    if !introduced_keys.contains(key) {
      require_context_id(
        context,
        dependency.semantic_id(),
        span,
        "declaration dependency belongs to another compilation context",
      )
      dependencies.push(dependency)
    }
  }
  { origin, dependencies, introduced, node }
}

///|
struct KnownMap {
  context : @identity.CompilationContext
  entries : Map[(Int, @identity.SemanticId), Decl]
}

///|
pub fn KnownMap::new(context : @identity.CompilationContext) -> KnownMap {
  { context, entries: Map([]) }
}

///|
pub fn KnownMap::contains(self : KnownMap, dependency : DeclDependency) -> Bool {
  self.entries.contains((dependency.kind_tag(), dependency.semantic_id()))
}

///|
/// Adds a declaration only after every ordered dependency is known. The
/// returned map is independent of the original value.
pub fn KnownMap::add(
  self : KnownMap,
  declaration : Decl,
  span : @identity.SourceSpan?,
) -> KnownMap raise TypeError {
  for dependency in declaration.dependencies {
    require_context_id(
      self.context,
      dependency.semantic_id(),
      span,
      "known-map dependency belongs to another compilation context",
    )
    if !self.contains(dependency) {
      fail_type(
        UnknownDependency,
        span,
        "declaration references a symbol that has not been declared",
      )
    }
  }
  let entries = self.entries.copy()
  for introduced in declaration.introduced {
    require_context_id(
      self.context,
      introduced.semantic_id(),
      span,
      "known-map declaration belongs to another compilation context",
    )
    let key = (introduced.kind_tag(), introduced.semantic_id())
    if entries.contains(key) {
      fail_type(
        DuplicateDeclarationSymbol,
        span,
        "known map already contains the declared symbol",
      )
    }
    entries[key] = declaration
  }
  { context: self.context, entries }
}

///|
/// Merges declarations imported from another theory in the same compilation
/// context. Repeated entries for the same semantic symbol are idempotent.
pub fn KnownMap::merge(
  self : KnownMap,
  other : KnownMap,
  span : @identity.SourceSpan?,
) -> KnownMap raise TypeError {
  let entries = self.entries.copy()
  for key, declaration in other.entries {
    require_context_id(
      self.context,
      key.1,
      span,
      "known maps belong to different compilation contexts",
    )
    if !entries.contains(key) {
      entries[key] = declaration
    }
  }
  { context: self.context, entries }
}

///|
/// Trusted snapshot insertion validates context and duplicate identities but
/// permits dependencies supplied by a recorded Use/Clone history. User-built
/// theories must continue to use `add`, which enforces declaration order.
pub fn KnownMap::trusted_add_snapshot(
  self : KnownMap,
  declaration : Decl,
  span : @identity.SourceSpan?,
) -> KnownMap raise TypeError {
  if !(declaration.origin.kind().view() is SnapshotKind) {
    fail_type(
      SnapshotOriginRequired,
      span,
      "trusted known-map insertion requires snapshot provenance",
    )
  }
  let entries = self.entries.copy()
  for introduced in declaration.introduced {
    require_context_id(
      self.context,
      introduced.semantic_id(),
      span,
      "trusted known-map declaration belongs to another compilation context",
    )
    let key = (introduced.kind_tag(), introduced.semantic_id())
    if entries.contains(key) {
      fail_type(
        DuplicateDeclarationSymbol,
        span,
        "trusted known map already contains the declared symbol",
      )
    }
    entries[key] = declaration
  }
  { context: self.context, entries }
}
