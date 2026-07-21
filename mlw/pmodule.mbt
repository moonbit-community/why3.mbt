// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
struct ProgramTypeDeclaration {
  symbol : ProgramTypeSymbol
  fields : Array[RoutineSymbol]
  constructors : Array[RoutineSymbol]
  invariants : Array[@logic.Term]
}

///|
pub(all) struct ProgramTypeDeclarationView {
  symbol : ProgramTypeSymbol
  fields : ArrayView[RoutineSymbol]
  constructors : ArrayView[RoutineSymbol]
  invariants : ArrayView[@logic.Term]
}

///|
pub(all) enum ProgramComputation {
  Cany(Cty)
  Cfun(Cty, Expr?)
}

///|
pub(all) enum ProgramDeclaration {
  PDtype(Array[ProgramTypeDeclaration], Array[@logic.Decl])
  PDpure(Array[@logic.Decl])
  PDlet(RoutineSymbol, ProgramComputation, Array[@logic.Decl])
}

///|
struct ProgramCloneWitness {
  anchor : @identity.SemanticId
  source : @theory.TheoryKey
  type_instantiations : Array[(@logic.TypeSymbol, Ity)]
  program_type_instantiations : Array[(@logic.TypeSymbol, ProgramTypeSymbol)]
  logic_instantiations : Array[(@logic.LSymbol, @logic.LSymbol)]
  proposition_instantiations : Array[(@logic.PrSymbol, @logic.PrSymbol)]
  proposition_kinds : Array[(@logic.PrSymbol, @logic.PropositionKind)]
  program_variable_instantiations : Array[(@logic.VSymbol, PVariable)]
  routine_instantiations : Array[(RoutineSymbol, RoutineSymbol)]
  default_proposition_kind : @logic.PropositionKind
}

///|
pub(all) struct ProgramCloneWitnessView {
  source : @theory.TheoryKey
  type_instantiations : ArrayView[(@logic.TypeSymbol, Ity)]
  program_type_instantiations : ArrayView[
    (@logic.TypeSymbol, ProgramTypeSymbol),
  ]
  logic_instantiations : ArrayView[(@logic.LSymbol, @logic.LSymbol)]
  proposition_instantiations : ArrayView[(@logic.PrSymbol, @logic.PrSymbol)]
  proposition_kinds : ArrayView[(@logic.PrSymbol, @logic.PropositionKind)]
  program_variable_instantiations : ArrayView[(@logic.VSymbol, PVariable)]
  routine_instantiations : ArrayView[(RoutineSymbol, RoutineSymbol)]
  default_proposition_kind : @logic.PropositionKind
}

///|
pub(all) enum ModuleItem {
  Udecl(ProgramDeclaration)
  Uuse(@theory.TheoryKey)
  Uclone(ProgramCloneWitness)
  Umeta(@theory.Meta)
}

///|
struct Pmodule {
  anchor : @identity.SemanticId
  key : @theory.TheoryKey
  pure_theory : @theory.Theory
  items : Array[ModuleItem]
  export_namespace : ProgramNamespace
}

///|
pub(all) struct PmoduleView {
  key : @theory.TheoryKey
  pure_theory : @theory.Theory
  items : ArrayView[ModuleItem]
  export_namespace : ProgramNamespace
}

///|
/// Minimal program-module builder used before executable expressions are
/// introduced. It keeps the projected pure theory and program namespace in
/// lockstep for module `use` declarations.
struct PmoduleBuilder {
  anchor : @identity.SemanticId
  key : @theory.TheoryKey
  pure_builder : @theory.TheoryBuilder
  items : Array[ModuleItem]
  mut current_namespace : ProgramNamespace
  mut export_namespace : ProgramNamespace
  mut closed : Bool
}

///|
pub fn ProgramTypeDeclaration::trusted_new(
  symbol : ProgramTypeSymbol,
  fields : ArrayView[RoutineSymbol],
  constructors : ArrayView[RoutineSymbol],
  invariants : ArrayView[@logic.Term],
  span : @identity.SourceSpan?,
) -> ProgramTypeDeclaration raise MlwError {
  let anchor = symbol.semantic_id()
  for field in fields {
    require_mlw_context(anchor, field.semantic_id(), span)
  }
  for constructor_symbol in constructors {
    require_mlw_context(anchor, constructor_symbol.semantic_id(), span)
  }
  for invariant in invariants {
    if !invariant.is_formula() {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "type invariant is not a formula",
      )
    }
  }
  {
    symbol,
    fields: fields.to_owned(),
    constructors: constructors.to_owned(),
    invariants: invariants.to_owned(),
  }
}

///|
pub fn ProgramTypeDeclaration::view(
  self : ProgramTypeDeclaration,
) -> ProgramTypeDeclarationView {
  {
    symbol: self.symbol,
    fields: self.fields[:],
    constructors: self.constructors[:],
    invariants: self.invariants[:],
  }
}

///|
pub fn ProgramCloneWitness::trusted_new(
  context_anchor : @identity.SemanticId,
  source : @theory.TheoryKey,
  type_instantiations : ArrayView[(@logic.TypeSymbol, Ity)],
  program_type_instantiations : ArrayView[
    (@logic.TypeSymbol, ProgramTypeSymbol),
  ],
  logic_instantiations : ArrayView[(@logic.LSymbol, @logic.LSymbol)],
  proposition_instantiations : ArrayView[(@logic.PrSymbol, @logic.PrSymbol)],
  proposition_kinds : ArrayView[(@logic.PrSymbol, @logic.PropositionKind)],
  program_variable_instantiations : ArrayView[(@logic.VSymbol, PVariable)],
  routine_instantiations : ArrayView[(RoutineSymbol, RoutineSymbol)],
  default_proposition_kind : @logic.PropositionKind,
  span : @identity.SourceSpan?,
) -> ProgramCloneWitness raise MlwError {
  for entry in type_instantiations {
    require_mlw_context(context_anchor, entry.0.semantic_id(), span)
    require_mlw_context(context_anchor, entry.1.context_anchor(), span)
  }
  for entry in program_type_instantiations {
    require_mlw_context(context_anchor, entry.0.semantic_id(), span)
    require_mlw_context(context_anchor, entry.1.semantic_id(), span)
  }
  for entry in logic_instantiations {
    require_mlw_context(context_anchor, entry.0.semantic_id(), span)
    require_mlw_context(context_anchor, entry.1.semantic_id(), span)
  }
  for entry in proposition_instantiations {
    require_mlw_context(context_anchor, entry.0.semantic_id(), span)
    require_mlw_context(context_anchor, entry.1.semantic_id(), span)
  }
  for entry in proposition_kinds {
    require_mlw_context(context_anchor, entry.0.semantic_id(), span)
  }
  for entry in program_variable_instantiations {
    require_mlw_context(context_anchor, entry.0.semantic_id(), span)
    require_mlw_context(context_anchor, entry.1.semantic_id(), span)
  }
  for entry in routine_instantiations {
    require_mlw_context(context_anchor, entry.0.semantic_id(), span)
    require_mlw_context(context_anchor, entry.1.semantic_id(), span)
  }
  {
    anchor: context_anchor,
    source,
    type_instantiations: type_instantiations.to_owned(),
    program_type_instantiations: program_type_instantiations.to_owned(),
    logic_instantiations: logic_instantiations.to_owned(),
    proposition_instantiations: proposition_instantiations.to_owned(),
    proposition_kinds: proposition_kinds.to_owned(),
    program_variable_instantiations: program_variable_instantiations.to_owned(),
    routine_instantiations: routine_instantiations.to_owned(),
    default_proposition_kind,
  }
}

///|
pub fn ProgramCloneWitness::context_anchor(
  self : ProgramCloneWitness,
) -> @identity.SemanticId {
  self.anchor
}

///|
pub fn ProgramCloneWitness::view(
  self : ProgramCloneWitness,
) -> ProgramCloneWitnessView {
  {
    source: self.source,
    type_instantiations: self.type_instantiations[:],
    program_type_instantiations: self.program_type_instantiations[:],
    logic_instantiations: self.logic_instantiations[:],
    proposition_instantiations: self.proposition_instantiations[:],
    proposition_kinds: self.proposition_kinds[:],
    program_variable_instantiations: self.program_variable_instantiations[:],
    routine_instantiations: self.routine_instantiations[:],
    default_proposition_kind: self.default_proposition_kind,
  }
}

///|
pub fn Pmodule::trusted_new(
  key : @theory.TheoryKey,
  pure_theory : @theory.Theory,
  items : ArrayView[ModuleItem],
  export_namespace : ProgramNamespace,
) -> Pmodule raise {
  let anchor = pure_theory.context_anchor()
  if key != pure_theory.key() {
    fail_mlw(
      InvalidProgramDeclaration,
      None,
      "program module key differs from its projected pure theory",
    )
  }
  require_program_namespace_context(anchor, export_namespace, None)
  let copied = items.to_owned()
  for item in copied {
    match item {
      Udecl(declaration) =>
        require_program_declaration_context(anchor, declaration, None)
      Uuse(_) => ()
      Uclone(witness) =>
        require_mlw_context(anchor, witness.context_anchor(), None)
      Umeta(meta) => meta.validate_context(anchor, None)
    }
  }
  { anchor, key, pure_theory, items: copied, export_namespace }
}

///|
pub fn Pmodule::context_anchor(self : Pmodule) -> @identity.SemanticId {
  self.anchor
}

///|
pub fn Pmodule::key(self : Pmodule) -> @theory.TheoryKey {
  self.key
}

///|
pub fn Pmodule::pure_theory(self : Pmodule) -> @theory.Theory {
  self.pure_theory
}

///|
pub fn Pmodule::export_namespace(self : Pmodule) -> ProgramNamespace {
  self.export_namespace
}

///|
pub fn Pmodule::view(self : Pmodule) -> PmoduleView {
  {
    key: self.key,
    pure_theory: self.pure_theory,
    items: self.items[:],
    export_namespace: self.export_namespace,
  }
}

///|
fn require_program_namespace_context(
  anchor : @identity.SemanticId,
  program_space : ProgramNamespace,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  for entry in program_space.types {
    require_mlw_context(anchor, entry.1.semantic_id(), span)
  }
  for entry in program_space.routines {
    require_mlw_context(anchor, entry.1.semantic_id(), span)
  }
  for entry in program_space.subspaces {
    require_program_namespace_context(anchor, entry.1, span)
  }
}

///|
fn require_pure_declaration_context(
  anchor : @identity.SemanticId,
  declaration : @logic.Decl,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  for symbol in declaration.introduced_symbols() {
    require_mlw_context(anchor, symbol.semantic_id(), span)
  }
  for symbol in declaration.dependencies() {
    require_mlw_context(anchor, symbol.semantic_id(), span)
  }
}

///|
fn require_program_declaration_context(
  anchor : @identity.SemanticId,
  declaration : ProgramDeclaration,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  match declaration {
    PDtype(declarations, pure) => {
      for entry in declarations {
        require_mlw_context(anchor, entry.view().symbol.semantic_id(), span)
      }
      for entry in pure {
        require_pure_declaration_context(anchor, entry, span)
      }
    }
    PDpure(pure) =>
      for entry in pure {
        require_pure_declaration_context(anchor, entry, span)
      }
    PDlet(symbol, computation, pure) => {
      require_mlw_context(anchor, symbol.semantic_id(), span)
      match computation {
        Cany(cty) => require_mlw_context(anchor, cty.context_anchor(), span)
        Cfun(cty, body) => {
          require_mlw_context(anchor, cty.context_anchor(), span)
          if body is Some(body) {
            require_mlw_context(anchor, body.context_anchor(), span)
          }
        }
      }
      for entry in pure {
        require_pure_declaration_context(anchor, entry, span)
      }
    }
  }
}

///|
pub fn PmoduleBuilder::new(
  context : @identity.CompilationContext,
  key : @theory.TheoryKey,
  name : @theory.SemanticName,
) -> PmoduleBuilder {
  {
    anchor: context.fresh_id(),
    key,
    pure_builder: @theory.TheoryBuilder::new(context, key, name),
    items: [],
    current_namespace: ProgramNamespace::empty(),
    export_namespace: ProgramNamespace::empty(),
    closed: false,
  }
}

///|
fn PmoduleBuilder::require_open(
  self : PmoduleBuilder,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  if self.closed {
    fail_mlw(
      ProgramModuleBuilderSealed,
      span,
      "program module builder is closed",
    )
  }
}

///|
pub fn PmoduleBuilder::pure_namespace(
  self : PmoduleBuilder,
) -> @theory.Namespace {
  self.pure_builder.export_namespace()
}

///|
pub fn PmoduleBuilder::program_namespace(
  self : PmoduleBuilder,
) -> ProgramNamespace {
  self.current_namespace
}

///|
pub fn PmoduleBuilder::add_pure_decl(
  self : PmoduleBuilder,
  declaration : @logic.Decl,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  self.pure_builder.add_decl(declaration, span)
  self.items.push(Udecl(PDpure([declaration])))
}

///|
/// Adds one user-visible routine declaration while keeping its pure
/// projection and exported program namespace synchronized.
pub fn PmoduleBuilder::add_program_decl(
  self : PmoduleBuilder,
  symbol : RoutineSymbol,
  computation : ProgramComputation,
  pure_declarations : ArrayView[@logic.Decl],
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  require_mlw_context(self.anchor, symbol.semantic_id(), span)
  let computation_cty = match computation {
    Cany(cty) | Cfun(cty, _) => cty
  }
  require_mlw_context(self.anchor, computation_cty.context_anchor(), span)
  if computation_cty.result != symbol.view().cty.view().result {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "routine definition result differs from its symbol",
    )
  }
  let pure = pure_declarations.to_owned()
  for declaration in pure {
    self.pure_builder.add_decl(declaration, span)
  }
  self.current_namespace = self.current_namespace.add_routine(
    symbol.view().name,
    symbol,
    span,
  )
  self.export_namespace = self.export_namespace.add_routine(
    symbol.view().name,
    symbol,
    span,
  )
  self.items.push(Udecl(PDlet(symbol, computation, pure)))
}

///|
pub fn PmoduleBuilder::add_use(
  self : PmoduleBuilder,
  used : Pmodule,
  import_ : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  require_mlw_context(self.anchor, used.anchor, span)
  self.pure_builder.add_use(used.pure_theory, import_, span)
  if import_ {
    self.current_namespace = self.current_namespace.merge(
      used.export_namespace,
      span,
    )
    self.export_namespace = self.export_namespace.merge(
      used.export_namespace,
      span,
    )
  } else {
    self.current_namespace = self.current_namespace.add_subspace(
      used.key.view().name,
      used.export_namespace,
      span,
    )
    self.export_namespace = self.export_namespace.add_subspace(
      used.key.view().name,
      used.export_namespace,
      span,
    )
  }
  self.items.push(Uuse(used.key))
}

///|
/// Mirrors Why3's `use [import] path.Module`: the used module is retained as
/// a named exported scope, while `import` controls only unqualified lookup in
/// the current module body.
pub fn PmoduleBuilder::add_scoped_use(
  self : PmoduleBuilder,
  scope_name : BytesView,
  used : Pmodule,
  import_ : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  require_mlw_context(self.anchor, used.anchor, span)
  self.pure_builder.open_scope(scope_name, span)
  self.pure_builder.add_use(used.pure_theory, true, span)
  self.pure_builder.close_scope(import_, span)
  if import_ {
    self.current_namespace = self.current_namespace.merge(
      used.export_namespace,
      span,
    )
  }
  self.current_namespace = self.current_namespace.add_subspace(
    scope_name,
    used.export_namespace,
    span,
  )
  self.export_namespace = self.export_namespace.add_subspace(
    scope_name,
    used.export_namespace,
    span,
  )
  self.items.push(Uuse(used.key))
}

///|
pub fn PmoduleBuilder::close(self : PmoduleBuilder) -> Pmodule raise {
  self.require_open(None)
  self.closed = true
  Pmodule::trusted_new(
    self.key,
    self.pure_builder.close(),
    self.items,
    self.export_namespace,
  )
}
