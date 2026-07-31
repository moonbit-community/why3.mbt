// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
struct ProgramTypeDeclaration {
  symbol : ProgramTypeSymbol
  fields : Array[RoutineSymbol]
  constructors : Array[RoutineSymbol]
  invariants : Array[@logic.Term]
  witness : Expr?
}

///|
pub(all) struct ProgramTypeDeclarationView {
  symbol : ProgramTypeSymbol
  fields : ArrayView[RoutineSymbol]
  constructors : ArrayView[RoutineSymbol]
  invariants : ArrayView[@logic.Term]
  witness : Expr?
}

///|
pub(all) enum ProgramComputation {
  Cany(Cty)
  Cfun(Cty, Expr?)
  Cexpression(Cexp)
}

///|
pub(all) enum ProgramDeclaration {
  PDtype(Array[ProgramTypeDeclaration], Array[@logic.Decl], Array[@theory.Meta])
  PDpure(Array[@logic.Decl], Array[@theory.Meta])
  PDlet(
    RoutineSymbol,
    ProgramComputation,
    Array[@logic.Decl],
    Array[@theory.Meta]
  )
  PDvar(PVariable, Expr, Array[@logic.Decl], Array[@theory.Meta])
  PDrec(Array[RecursiveDefinition], Array[@logic.Decl], Array[@theory.Meta])
  PDexn(XSymbol, Array[@logic.Decl], Array[@theory.Meta])
}

///|
pub fn ProgramComputation::cty(self : ProgramComputation) -> Cty {
  match self {
    Cany(cty) | Cfun(cty, _) => cty
    Cexpression(expression) => expression.cty()
  }
}

///|
pub fn ProgramComputation::body(self : ProgramComputation) -> Expr? {
  match self {
    Cany(_) | Cfun(_, None) => None
    Cfun(_, Some(body)) => Some(body)
    Cexpression(expression) =>
      match expression.view() {
        Cfun(body) => Some(body)
        Capp(_, _) | Cpur(_, _) | Cany => None
      }
  }
}

///|
pub fn ProgramDeclaration::pure_declarations(
  self : ProgramDeclaration,
) -> ArrayView[@logic.Decl] {
  match self {
    PDtype(_, pure, _)
    | PDpure(pure, _)
    | PDlet(_, _, pure, _)
    | PDvar(_, _, pure, _)
    | PDrec(_, pure, _)
    | PDexn(_, pure, _) => pure[:]
  }
}

///|
pub fn ProgramDeclaration::metas(
  self : ProgramDeclaration,
) -> ArrayView[@theory.Meta] {
  match self {
    PDtype(_, _, metas)
    | PDpure(_, metas)
    | PDlet(_, _, _, metas)
    | PDvar(_, _, _, metas)
    | PDrec(_, _, metas)
    | PDexn(_, _, metas) => metas[:]
  }
}

///|
pub fn ProgramDeclaration::type_declarations(
  anchor : @identity.SemanticId,
  declarations : ArrayView[ProgramTypeDeclaration],
  pure : ArrayView[@logic.Decl],
  metas : ArrayView[@theory.Meta],
  span : @identity.SourceSpan?,
) -> ProgramDeclaration raise {
  if declarations.is_empty() {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "program type declaration group cannot be empty",
    )
  }
  let declaration = PDtype(
    declarations.to_owned(),
    pure.to_owned(),
    metas.to_owned(),
  )
  require_program_declaration_context(anchor, declaration, span)
  declaration
}

///|
pub fn ProgramDeclaration::pure(
  anchor : @identity.SemanticId,
  declarations : ArrayView[@logic.Decl],
  metas : ArrayView[@theory.Meta],
  span : @identity.SourceSpan?,
) -> ProgramDeclaration raise {
  let declaration = PDpure(declarations.to_owned(), metas.to_owned())
  require_program_declaration_context(anchor, declaration, span)
  declaration
}

///|
pub fn ProgramDeclaration::routine(
  anchor : @identity.SemanticId,
  symbol : RoutineSymbol,
  computation : ProgramComputation,
  pure : ArrayView[@logic.Decl],
  metas : ArrayView[@theory.Meta],
  span : @identity.SourceSpan?,
) -> ProgramDeclaration raise {
  symbol.refresh_definition_cty(computation.cty(), span)
  let declaration = PDlet(
    symbol,
    computation,
    pure.to_owned(),
    metas.to_owned(),
  )
  require_program_declaration_context(anchor, declaration, span)
  declaration
}

///|
pub fn ProgramDeclaration::variable(
  anchor : @identity.SemanticId,
  variable : PVariable,
  value : Expr,
  pure : ArrayView[@logic.Decl],
  metas : ArrayView[@theory.Meta],
  span : @identity.SourceSpan?,
) -> ProgramDeclaration raise {
  if variable.view().ity != value.ity() {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "program variable definition has a different value type",
    )
  }
  let declaration = PDvar(variable, value, pure.to_owned(), metas.to_owned())
  require_program_declaration_context(anchor, declaration, span)
  declaration
}

///|
pub fn ProgramDeclaration::recursive(
  anchor : @identity.SemanticId,
  definitions : ArrayView[RecursiveDefinition],
  pure : ArrayView[@logic.Decl],
  metas : ArrayView[@theory.Meta],
  span : @identity.SourceSpan?,
) -> ProgramDeclaration raise {
  if definitions.is_empty() {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "recursive program declaration group cannot be empty",
    )
  }
  let definitions = definitions.to_owned()
  // Module cloning constructs the recursive members before wrapping them in a
  // declaration. Run the same effect fixpoint as `let_rec`: calls initially
  // see clean internal symbols, then both the body computations and exported
  // symbols are refined to the stabilized effects.
  stabilize_recursive_definitions(definitions, span)
  let declaration = PDrec(definitions, pure.to_owned(), metas.to_owned())
  require_program_declaration_context(anchor, declaration, span)
  declaration
}

///|
pub fn ProgramDeclaration::exception(
  anchor : @identity.SemanticId,
  exception : XSymbol,
  pure : ArrayView[@logic.Decl],
  metas : ArrayView[@theory.Meta],
  span : @identity.SourceSpan?,
) -> ProgramDeclaration raise {
  let declaration = PDexn(exception, pure.to_owned(), metas.to_owned())
  require_program_declaration_context(anchor, declaration, span)
  declaration
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
  exception_instantiations : Array[(XSymbol, XSymbol)]
  default_proposition_kind : @logic.PropositionKind
  // VC generation is deliberately delayed until the complete program module
  // is available.  Why3, however, checks explicit routine refinements while
  // cloning and marks every ordinary cloned declaration as `vc:false`.
  // Retain that operational information outside `view()` so the canonical
  // clone witness remains the exact public Why3 correspondence.
  vc_refinements : Array[(RoutineSymbol, Cty, Expr, Int)]
  vc_suppressed_routines : Array[RoutineSymbol]
  vc_suppressed_types : Array[ProgramTypeSymbol]
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
  exception_instantiations : ArrayView[(XSymbol, XSymbol)]
  default_proposition_kind : @logic.PropositionKind
}

///|
pub(all) enum ModuleItem {
  Udecl(ProgramDeclaration)
  Uuse(@theory.TheoryKey)
  Uclone(ProgramCloneWitness)
  Umeta(@theory.Meta)
  Uscope(Bytes, Array[ModuleItem])
}

///|
struct Pmodule {
  anchor : @identity.SemanticId
  key : @theory.TheoryKey
  pure_theory : @theory.Theory
  items : Array[ModuleItem]
  export_namespace : ProgramNamespace
  dependencies : Array[(@theory.TheoryKey, Pmodule)]
}

///|
pub(all) struct PmoduleView {
  key : @theory.TheoryKey
  pure_theory : @theory.Theory
  items : ArrayView[ModuleItem]
  export_namespace : ProgramNamespace
  dependencies : ArrayView[(@theory.TheoryKey, Pmodule)]
}

///|
/// Minimal program-module builder used before executable expressions are
/// introduced. It keeps the projected pure theory and program namespace in
/// lockstep for module `use` declarations.
struct PmoduleBuilder {
  context : @identity.CompilationContext
  anchor : @identity.SemanticId
  key : @theory.TheoryKey
  pure_builder : @theory.TheoryBuilder
  items : Array[ModuleItem]
  scope_items : Array[Array[ModuleItem]]
  scope_names : Array[Bytes]
  import_parents : Array[ProgramNamespace]
  export_parents : Array[ProgramNamespace]
  mut current_namespace : ProgramNamespace
  mut export_namespace : ProgramNamespace
  dependencies : Array[(@theory.TheoryKey, Pmodule)]
  mut closed : Bool
}

///|
pub fn ProgramTypeDeclaration::trusted_new(
  symbol : ProgramTypeSymbol,
  fields : ArrayView[RoutineSymbol],
  constructors : ArrayView[RoutineSymbol],
  invariants : ArrayView[@logic.Term],
  span : @identity.SourceSpan?,
  witness? : Expr? = None,
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
  if witness is Some(expression) {
    require_mlw_context(anchor, expression.context_anchor(), span)
    let effect = expression.effect().view()
    if !(effect.termination is Total) || !effect.raises.is_empty() {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "type witness may not fail, diverge, or raise an exception",
      )
    }
  }
  symbol.register_invariants(invariants)
  {
    symbol,
    fields: fields.to_owned(),
    constructors: constructors.to_owned(),
    invariants: invariants.to_owned(),
    witness,
  }
}

///|
fn ity_head_program_symbol(ity : Ity) -> ProgramTypeSymbol? {
  match ity.view() {
    ItyVar(_) => None
    ItyApp(symbol, _, _) => Some(symbol)
    ItyReg(region) => Some(region.view().symbol)
  }
}

///|
pub fn ProgramTypeDeclaration::new(
  symbol : ProgramTypeSymbol,
  fields : ArrayView[RoutineSymbol],
  constructors : ArrayView[RoutineSymbol],
  invariants : ArrayView[@logic.Term],
  span : @identity.SourceSpan?,
  witness? : Expr? = None,
) -> ProgramTypeDeclaration raise MlwError {
  let declaration = ProgramTypeDeclaration::trusted_new(
    symbol,
    fields,
    constructors,
    invariants,
    span,
    witness~,
  )
  let symbol_view = symbol.view()
  let declared_fields = symbol_view.mutable_fields.to_owned() +
    symbol_view.immutable_fields.to_owned()
  let projected : Array[PVariable] = []
  for routine in fields {
    let routine_view = routine.view()
    guard routine_view.field is Some(field) else {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "program type field routine is not a projection",
      )
    }
    if !declared_fields.any(candidate => candidate == field) {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "projection field is absent from its program type",
      )
    }
    if projected.any(candidate => candidate == field) {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "program type declares one projection twice",
      )
    }
    projected.push(field)
    guard routine_view.logic is RLls(logic_symbol) &&
      (
        logic_symbol.view().role is Projection ||
        (symbol_view.flags.nonfree && logic_symbol.view().role is Ordinary)
      ) else {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "program field does not have a logical projection",
      )
    }
    let cty = routine_view.cty.view()
    if cty.arguments.length() != 1 ||
      ity_head_program_symbol(cty.arguments[0].view().ity) != Some(symbol) {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "projection argument does not belong to its program type",
      )
    }
  }
  let constructor_count = constructors.length()
  for routine in constructors {
    let routine_view = routine.view()
    let valid_constructor_logic = match routine_view.logic {
      RLls(logic_symbol) =>
        logic_symbol.view().role is Constructor(count) &&
        count == constructor_count
      RLnone =>
        symbol_view.flags.nonfree &&
        !invariants.is_empty() &&
        constructor_count == 1
      RLpv(_) | RLlemma => false
    }
    if !valid_constructor_logic {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "program constructor has inconsistent logical constructor metadata",
      )
    }
    let cty = routine_view.cty.view()
    if ity_head_program_symbol(cty.result) != Some(symbol) {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "constructor result does not belong to its program type",
      )
    }
    let seen : Array[PVariable] = []
    for argument in cty.arguments {
      if seen.any(candidate => candidate == argument) {
        fail_mlw(
          InvalidProgramDeclaration,
          span,
          "constructor repeats one program field",
        )
      }
      seen.push(argument)
      if !declared_fields.any(candidate => candidate == argument) {
        fail_mlw(
          InvalidProgramDeclaration,
          span,
          "constructor argument is absent from its program type fields",
        )
      }
    }
  }
  for invariant in invariants {
    for variable in invariant.free_variables() {
      if !declared_fields.any(field => field.view().pure_symbol == variable) {
        fail_mlw(
          InvalidProgramTypeInvariant,
          span,
          "type invariant references a non-field variable",
        )
      }
    }
  }
  declaration
}

///|
pub fn ProgramTypeDeclaration::simple(
  symbol : ProgramTypeSymbol,
) -> ProgramTypeDeclaration {
  { symbol, fields: [], constructors: [], invariants: [], witness: None }
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
    witness: self.witness,
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
  exception_instantiations : ArrayView[(XSymbol, XSymbol)],
  default_proposition_kind : @logic.PropositionKind,
  span : @identity.SourceSpan?,
  vc_refinements? : ArrayView[(RoutineSymbol, Cty, Expr, Int)] = [],
  vc_suppressed_routines? : ArrayView[RoutineSymbol] = [],
  vc_suppressed_types? : ArrayView[ProgramTypeSymbol] = [],
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
  for entry in exception_instantiations {
    require_mlw_context(context_anchor, entry.0.semantic_id(), span)
    require_mlw_context(context_anchor, entry.1.semantic_id(), span)
  }
  for refinement in vc_refinements {
    require_mlw_context(context_anchor, refinement.0.semantic_id(), span)
    require_mlw_context(context_anchor, refinement.1.context_anchor(), span)
    require_mlw_context(context_anchor, refinement.2.context_anchor(), span)
  }
  for routine in vc_suppressed_routines {
    require_mlw_context(context_anchor, routine.semantic_id(), span)
  }
  for symbol in vc_suppressed_types {
    require_mlw_context(context_anchor, symbol.semantic_id(), span)
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
    exception_instantiations: exception_instantiations.to_owned(),
    default_proposition_kind,
    vc_refinements: vc_refinements.to_owned(),
    vc_suppressed_routines: vc_suppressed_routines.to_owned(),
    vc_suppressed_types: vc_suppressed_types.to_owned(),
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
    exception_instantiations: self.exception_instantiations[:],
    default_proposition_kind: self.default_proposition_kind,
  }
}

///|
/// Internal clone obligations consumed by the delayed VC pass.  Each entry is
/// the derived `'<refn>` routine, its translated source contract, and the call
/// to the explicit target implementation.
pub fn ProgramCloneWitness::vc_refinements(
  self : ProgramCloneWitness,
) -> ArrayView[(RoutineSymbol, Cty, Expr, Int)] {
  self.vc_refinements[:]
}

///|
/// Routines copied by this clone were already checked in their source module.
pub fn ProgramCloneWitness::vc_suppressed_routines(
  self : ProgramCloneWitness,
) -> ArrayView[RoutineSymbol] {
  self.vc_suppressed_routines[:]
}

///|
/// Program types copied by this clone likewise retain their source checks.
pub fn ProgramCloneWitness::vc_suppressed_types(
  self : ProgramCloneWitness,
) -> ArrayView[ProgramTypeSymbol] {
  self.vc_suppressed_types[:]
}

///|
pub fn Pmodule::trusted_new(
  key : @theory.TheoryKey,
  pure_theory : @theory.Theory,
  items : ArrayView[ModuleItem],
  export_namespace : ProgramNamespace,
) -> Pmodule raise {
  Pmodule::trusted_new_with_dependencies(
    key,
    pure_theory,
    items,
    export_namespace,
    [],
  )
}

///|
pub fn Pmodule::trusted_new_with_dependencies(
  key : @theory.TheoryKey,
  pure_theory : @theory.Theory,
  items : ArrayView[ModuleItem],
  export_namespace : ProgramNamespace,
  dependencies : ArrayView[(@theory.TheoryKey, Pmodule)],
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
  validate_module_items(anchor, copied)
  {
    anchor,
    key,
    pure_theory,
    items: copied,
    export_namespace,
    dependencies: dependencies.to_owned(),
  }
}

///|
fn validate_module_items(
  anchor : @identity.SemanticId,
  items : ArrayView[ModuleItem],
) -> Unit raise {
  for item in items {
    match item {
      Udecl(declaration) =>
        require_program_declaration_context(anchor, declaration, None)
      Uuse(_) => ()
      Uclone(witness) =>
        require_mlw_context(anchor, witness.context_anchor(), None)
      Umeta(meta) => meta.validate_context(anchor, None)
      Uscope(_, nested) => validate_module_items(anchor, nested)
    }
  }
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
/// Pure declaration environment visible from this completed module, including
/// declarations imported through `use` and `clone`.
pub fn Pmodule::pure_known(self : Pmodule) -> @logic.KnownMap {
  self.pure_theory.known_map()
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
    dependencies: self.dependencies[:],
  }
}

///|
pub fn Pmodule::dependency_modules(
  self : Pmodule,
) -> ArrayView[(@theory.TheoryKey, Pmodule)] {
  self.dependencies[:]
}

///|
pub fn Pmodule::referenced_module(
  self : Pmodule,
  key : @theory.TheoryKey,
) -> Pmodule? {
  for entry in self.dependencies {
    if entry.0 == key {
      return Some(entry.1)
    }
  }
  None
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
  for entry in program_space.variables {
    require_mlw_context(anchor, entry.1.semantic_id(), span)
  }
  for entry in program_space.routines {
    require_mlw_context(anchor, entry.1.semantic_id(), span)
  }
  for entry in program_space.exceptions {
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
) -> Unit raise {
  match declaration {
    PDtype(declarations, pure, metas) => {
      for entry in declarations {
        require_mlw_context(anchor, entry.view().symbol.semantic_id(), span)
        if entry.view().witness is Some(witness) {
          require_mlw_context(anchor, witness.context_anchor(), span)
        }
      }
      for entry in pure {
        require_pure_declaration_context(anchor, entry, span)
      }
      for meta in metas {
        meta.validate_context(anchor, span)
      }
    }
    PDpure(pure, metas) => {
      for entry in pure {
        require_pure_declaration_context(anchor, entry, span)
      }
      for meta in metas {
        meta.validate_context(anchor, span)
      }
    }
    PDlet(symbol, computation, pure, metas) => {
      require_mlw_context(anchor, symbol.semantic_id(), span)
      match computation {
        Cany(cty) => require_mlw_context(anchor, cty.context_anchor(), span)
        Cfun(cty, body) => {
          require_mlw_context(anchor, cty.context_anchor(), span)
          if body is Some(body) {
            require_mlw_context(anchor, body.context_anchor(), span)
          }
        }
        Cexpression(expression) =>
          require_mlw_context(anchor, expression.cty().context_anchor(), span)
      }
      for entry in pure {
        require_pure_declaration_context(anchor, entry, span)
      }
      for meta in metas {
        meta.validate_context(anchor, span)
      }
    }
    PDvar(variable, value, pure, metas) => {
      require_mlw_context(anchor, variable.semantic_id(), span)
      require_mlw_context(anchor, value.context_anchor(), span)
      if variable.view().ity != value.ity() {
        fail_mlw(
          InvalidProgramDeclaration,
          span,
          "program variable definition has a different value type",
        )
      }
      for entry in pure {
        require_pure_declaration_context(anchor, entry, span)
      }
      for meta in metas {
        meta.validate_context(anchor, span)
      }
    }
    PDrec(definitions, pure, metas) => {
      for definition in definitions {
        let view = definition.view()
        require_mlw_context(anchor, view.symbol.semantic_id(), span)
        require_mlw_context(anchor, view.internal_symbol.semantic_id(), span)
        require_mlw_context(anchor, view.function_.cty().context_anchor(), span)
      }
      for entry in pure {
        require_pure_declaration_context(anchor, entry, span)
      }
      for meta in metas {
        meta.validate_context(anchor, span)
      }
    }
    PDexn(exception, pure, metas) => {
      require_mlw_context(anchor, exception.semantic_id(), span)
      for entry in pure {
        require_pure_declaration_context(anchor, entry, span)
      }
      for meta in metas {
        meta.validate_context(anchor, span)
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
    context,
    anchor: context.fresh_id(),
    key,
    pure_builder: @theory.TheoryBuilder::new(context, key, name),
    items: [],
    scope_items: [],
    scope_names: [],
    import_parents: [],
    export_parents: [],
    current_namespace: ProgramNamespace::empty(),
    export_namespace: ProgramNamespace::empty(),
    dependencies: [],
    closed: false,
  }
}

///|
fn PmoduleBuilder::remember_module(
  self : PmoduleBuilder,
  pmodule : Pmodule,
) -> Unit {
  if !self.dependencies.any(entry => entry.0 == pmodule.key) {
    self.dependencies.push((pmodule.key, pmodule))
  }
}

///|
fn PmoduleBuilder::push_item(self : PmoduleBuilder, item : ModuleItem) -> Unit {
  match self.scope_items.last() {
    Some(items) => items.push(item)
    None => self.items.push(item)
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
fn PmoduleBuilder::add_exported_type(
  self : PmoduleBuilder,
  name : BytesView,
  symbol : ProgramTypeSymbol,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  let exported = self.export_namespace.add_type(name, symbol, span)
  self.current_namespace = self.current_namespace.overlay(exported)
  self.export_namespace = exported
}

///|
fn PmoduleBuilder::add_exported_routine(
  self : PmoduleBuilder,
  name : BytesView,
  symbol : RoutineSymbol,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  let exported = self.export_namespace.add_routine(name, symbol, span)
  self.current_namespace = self.current_namespace.overlay(exported)
  self.export_namespace = exported
}

///|
fn PmoduleBuilder::add_exported_variable(
  self : PmoduleBuilder,
  name : BytesView,
  variable : PVariable,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  let exported = self.export_namespace.add_variable(name, variable, span)
  self.current_namespace = self.current_namespace.overlay(exported)
  self.export_namespace = exported
}

///|
fn PmoduleBuilder::add_exported_exception(
  self : PmoduleBuilder,
  name : BytesView,
  symbol : XSymbol,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  let exported = self.export_namespace.add_exception(name, symbol, span)
  self.current_namespace = self.current_namespace.overlay(exported)
  self.export_namespace = exported
}

///|
fn PmoduleBuilder::merge_exported_namespace(
  self : PmoduleBuilder,
  imported : ProgramNamespace,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  let exported = self.export_namespace.merge(imported, span)
  self.current_namespace = self.current_namespace.overlay(exported)
  self.export_namespace = exported
}

///|
fn PmoduleBuilder::add_exported_subspace(
  self : PmoduleBuilder,
  name : BytesView,
  nested : ProgramNamespace,
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  let exported = self.export_namespace.add_subspace(name, nested, span)
  self.current_namespace = self.current_namespace.overlay(exported)
  self.export_namespace = exported
}

///|
pub fn PmoduleBuilder::pure_namespace(
  self : PmoduleBuilder,
) -> @theory.Namespace {
  self.pure_builder.export_namespace()
}

///|
/// Current pure declaration environment, including every theory imported by
/// the module so far.
pub fn PmoduleBuilder::pure_known(self : PmoduleBuilder) -> @logic.KnownMap {
  self.pure_builder.current_known()
}

///|
pub fn PmoduleBuilder::pure_coercions(
  self : PmoduleBuilder,
) -> @theory.CoercionMap {
  self.pure_builder.current_coercions()
}

///|
pub fn PmoduleBuilder::pure_elaboration_checkpoint(
  self : PmoduleBuilder,
) -> Int {
  self.pure_builder.item_count()
}

///|
pub fn PmoduleBuilder::pure_elaboration_builder(
  self : PmoduleBuilder,
) -> @theory.TheoryBuilder {
  self.pure_builder
}

///|
/// Adds a source proposition in the same order as Why3 parser typing:
/// non-goal propositions first introduce their ghost `'<lemma>` routine, then
/// the original proposition itself.
pub fn PmoduleBuilder::add_pure_proposition(
  self : PmoduleBuilder,
  declaration : @logic.Decl,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  guard declaration.view() is Dprop(kind, proposition, formula) else {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "pure proposition boundary received a non-proposition declaration",
    )
  }
  if kind != Pgoal {
    match
      Cty::from_formula(
        self.context,
        self.pure_builder.current_namespace(),
        self.current_namespace,
        formula,
        span,
      ) {
      Some(cty) => {
        let proposition_view = proposition.view()
        let name = proposition_view.name + b"'lemma"
        let source_origin = proposition_view.origin
        let routine_cty = cty.ghostify(true, span)
        let routine = RoutineSymbol::new_user(
          self.context,
          name,
          @identity.Origin::user(
            name,
            source_origin.source_span(),
            source_origin.attributes(),
          ),
          routine_cty,
          span,
        )
        self.add_program_decl(routine, ProgramComputation::Cany(cty), [], span)
      }
      None => ()
    }
  }
  self.pure_builder.add_decl(declaration, span)
  self.push_item(
    Udecl(ProgramDeclaration::pure(self.anchor, [declaration], [], span)),
  )
}

///|
pub fn PmoduleBuilder::finish_pure_elaboration(
  self : PmoduleBuilder,
  checkpoint : Int,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  let end = self.pure_builder.item_count()
  if checkpoint < 0 || checkpoint > end {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "pure elaboration checkpoint is out of bounds",
    )
  }
  for index = checkpoint; index < end; index = index + 1 {
    match self.pure_builder.item_at(index, span) {
      TheoryDecl(declaration) =>
        self.push_item(
          Udecl(ProgramDeclaration::pure(self.anchor, [declaration], [], span)),
        )
      TheoryMeta(meta) => self.push_item(Umeta(meta))
      TheoryUse(_) | TheoryClone(_) =>
        fail_mlw(
          InvalidProgramDeclaration,
          span,
          "pure source elaboration cannot directly add module use or clone items",
        )
    }
  }
}

///|
pub fn PmoduleBuilder::program_namespace(
  self : PmoduleBuilder,
) -> ProgramNamespace {
  self.current_namespace
}

///|
/// Opens a program namespace in lockstep with the projected pure theory.
pub fn PmoduleBuilder::open_scope(
  self : PmoduleBuilder,
  name : BytesView,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  if name.is_empty() {
    fail_mlw(InvalidProgramDeclaration, span, "program namespace name is empty")
  }
  self.pure_builder.open_scope(name, span)
  self.scope_names.push(name.to_owned())
  self.scope_items.push([])
  self.import_parents.push(self.current_namespace)
  self.export_parents.push(self.export_namespace)
  self.export_namespace = ProgramNamespace::empty()
}

///|
/// Closes the current namespace. Its exports remain qualified, and `import_`
/// additionally makes them visible without qualification in the parent.
pub fn PmoduleBuilder::close_scope(
  self : PmoduleBuilder,
  import_ : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  if self.scope_names.is_empty() {
    fail_mlw(
      NoOpenedProgramNamespace,
      span,
      "no program namespace scope is open",
    )
  }
  self.pure_builder.close_scope(import_, span)
  guard self.scope_names.pop() is Some(name) &&
    self.scope_items.pop() is Some(items) &&
    self.import_parents.pop() is Some(parent_import) &&
    self.export_parents.pop() is Some(parent_export) else {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "program namespace stack is inconsistent",
    )
  }
  let scope_export = self.export_namespace
  if items.is_empty() {
    self.current_namespace = parent_import
    self.export_namespace = parent_export
    return
  }
  let mut imported = parent_import
  if import_ {
    imported = imported.overlay(scope_export)
  }
  self.current_namespace = imported.overlay(
    ProgramNamespace::empty().add_subspace(name, scope_export, span),
  )
  self.export_namespace = parent_export.add_subspace(name, scope_export, span)
  self.push_item(Uscope(name, items))
}

///|
/// Imports an existing qualified program namespace for lookup only.
pub fn PmoduleBuilder::import_scope(
  self : PmoduleBuilder,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  self.pure_builder.import_scope(path, span)
  self.current_namespace = self.current_namespace.import_scope(path, span)
}

///|
pub fn PmoduleBuilder::add_pure_decl(
  self : PmoduleBuilder,
  declaration : @logic.Decl,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.add_pure_decl_with_metas(declaration, [], span)
}

///|
/// Adds a dependency to the projected pure theory without exposing the
/// dependency as a program-module `use`. Why3's builtin `Unit` module uses
/// this boundary for the implicit `BuiltIn` theory inherited by
/// `empty_module`.
pub fn PmoduleBuilder::add_pure_use(
  self : PmoduleBuilder,
  used : @theory.Theory,
  import_ : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  self.pure_builder.add_use(used, import_, span)
}

///|
pub fn PmoduleBuilder::add_pure_decl_with_metas(
  self : PmoduleBuilder,
  declaration : @logic.Decl,
  metas : ArrayView[@theory.Meta],
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  self.pure_builder.add_decl(declaration, span)
  let metas = metas.to_owned()
  for meta in metas {
    self.pure_builder.add_meta(meta, span)
  }
  self.push_item(Udecl(PDpure([declaration], metas)))
}

///|
pub fn PmoduleBuilder::add_type_declarations(
  self : PmoduleBuilder,
  declarations : ArrayView[ProgramTypeDeclaration],
  pure_declarations : ArrayView[@logic.Decl],
  metas : ArrayView[@theory.Meta],
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  let declaration = ProgramDeclaration::type_declarations(
    self.anchor,
    declarations,
    pure_declarations,
    metas,
    span,
  )
  for pure in pure_declarations {
    self.pure_builder.add_decl(pure, span)
  }
  for meta in metas {
    self.pure_builder.add_meta(meta, span)
  }
  self.register_type_declaration(declaration, declarations, span)
}

///|
pub fn PmoduleBuilder::add_existing_type_declarations(
  self : PmoduleBuilder,
  declarations : ArrayView[ProgramTypeDeclaration],
  pure_declarations : ArrayView[@logic.Decl],
  metas : ArrayView[@theory.Meta],
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  let declaration = ProgramDeclaration::type_declarations(
    self.anchor,
    declarations,
    pure_declarations,
    metas,
    span,
  )
  for pure in pure_declarations {
    for introduced in pure.introduced_symbols() {
      if !self.pure_builder.current_known().contains(introduced) {
        fail_mlw(
          InvalidProgramDeclaration,
          span,
          "existing program type references a pure declaration not in the builder",
        )
      }
    }
  }
  self.register_type_declaration(declaration, declarations, span)
}

///|
fn PmoduleBuilder::register_type_declaration(
  self : PmoduleBuilder,
  declaration : ProgramDeclaration,
  declarations : ArrayView[ProgramTypeDeclaration],
  span : @identity.SourceSpan?,
) -> Unit raise {
  for entry in declarations {
    let view = entry.view()
    let name = view.symbol.view().logic_type.name()
    self.add_exported_type(name, view.symbol, span)
    for routine in view.fields {
      let routine_name = routine.view().name
      self.add_exported_routine(routine_name, routine, span)
    }
    for routine in view.constructors {
      let routine_name = routine.view().name
      self.add_exported_routine(routine_name, routine, span)
    }
  }
  self.push_item(Udecl(declaration))
}

///|
/// Adds a program declaration whose pure projection was already inserted by
/// a preceding theory clone. This mirrors Why3's program half of
/// `clone_export` without duplicating the cloned pure declarations.
pub fn PmoduleBuilder::add_existing_program_declaration(
  self : PmoduleBuilder,
  declaration : ProgramDeclaration,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  require_program_declaration_context(self.anchor, declaration, span)
  match declaration {
    PDtype(declarations, _, _) =>
      self.register_type_declaration(declaration, declarations, span)
    PDpure(_, _) => self.push_item(Udecl(declaration))
    PDlet(symbol, _, _, _) => {
      self.add_exported_routine(symbol.view().name, symbol, span)
      self.push_item(Udecl(declaration))
    }
    PDvar(variable, _, _, _) => {
      self.add_exported_variable(
        variable.view().name.view().name,
        variable,
        span,
      )
      self.push_item(Udecl(declaration))
    }
    PDrec(definitions, _, _) => {
      for definition in definitions {
        let symbol = definition.view().symbol
        self.add_exported_routine(symbol.view().name, symbol, span)
      }
      self.push_item(Udecl(declaration))
    }
    PDexn(exception, _, _) => {
      self.add_exported_exception(
        exception.view().name.view().name,
        exception,
        span,
      )
      self.push_item(Udecl(declaration))
    }
  }
}

///|
/// Records the program projection of a meta already emitted by the pure clone.
pub fn PmoduleBuilder::add_existing_meta(
  self : PmoduleBuilder,
  meta : @theory.Meta,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  meta.validate_context(self.anchor, span)
  self.push_item(Umeta(meta))
}

///|
/// Records a nested clone that was already expanded by an enclosing program
/// clone. Its pure counterpart was emitted by the enclosing theory clone.
pub fn PmoduleBuilder::add_existing_clone(
  self : PmoduleBuilder,
  source : Pmodule,
  witness : ProgramCloneWitness,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  require_mlw_context(self.anchor, source.anchor, span)
  require_mlw_context(self.anchor, witness.context_anchor(), span)
  if witness.view().source != source.key {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "nested clone witness names a different source module",
    )
  }
  self.remember_module(source)
  self.push_item(Uclone(witness))
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
  self.add_program_decl_with_metas(
    symbol,
    computation,
    pure_declarations,
    [],
    span,
  )
}

///|
pub fn PmoduleBuilder::add_program_decl_with_metas(
  self : PmoduleBuilder,
  symbol : RoutineSymbol,
  computation : ProgramComputation,
  pure_declarations : ArrayView[@logic.Decl],
  metas : ArrayView[@theory.Meta],
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  require_mlw_context(self.anchor, symbol.semantic_id(), span)
  let computation_cty = computation.cty()
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
  let metas = metas.to_owned()
  for meta in metas {
    self.pure_builder.add_meta(meta, span)
  }
  self.add_exported_routine(symbol.view().name, symbol, span)
  self.push_item(Udecl(PDlet(symbol, computation, pure, metas)))
}

///|
pub fn PmoduleBuilder::add_variable_decl(
  self : PmoduleBuilder,
  variable : PVariable,
  value : Expr,
  pure_declarations : ArrayView[@logic.Decl],
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.add_variable_decl_with_metas(
    variable,
    value,
    pure_declarations,
    [],
    span,
  )
}

///|
pub fn PmoduleBuilder::add_variable_decl_with_metas(
  self : PmoduleBuilder,
  variable : PVariable,
  value : Expr,
  pure_declarations : ArrayView[@logic.Decl],
  metas : ArrayView[@theory.Meta],
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  require_mlw_context(self.anchor, variable.semantic_id(), span)
  require_mlw_context(self.anchor, value.context_anchor(), span)
  if variable.view().ity != value.ity() {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "program variable definition has a different value type",
    )
  }
  let pure = pure_declarations.to_owned()
  for declaration in pure {
    self.pure_builder.add_decl(declaration, span)
  }
  let metas = metas.to_owned()
  for meta in metas {
    self.pure_builder.add_meta(meta, span)
  }
  let declaration = ProgramDeclaration::variable(
    self.anchor,
    variable,
    value,
    pure,
    metas,
    span,
  )
  self.add_exported_variable(variable.view().name.view().name, variable, span)
  self.push_item(Udecl(declaration))
}

///|
pub fn PmoduleBuilder::add_recursive_decl(
  self : PmoduleBuilder,
  definitions : ArrayView[RecursiveDefinition],
  pure_declarations : ArrayView[@logic.Decl],
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.add_recursive_decl_with_metas(definitions, pure_declarations, [], span)
}

///|
pub fn PmoduleBuilder::add_recursive_decl_with_metas(
  self : PmoduleBuilder,
  definitions : ArrayView[RecursiveDefinition],
  pure_declarations : ArrayView[@logic.Decl],
  metas : ArrayView[@theory.Meta],
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  if definitions.is_empty() {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "recursive program declaration group cannot be empty",
    )
  }
  let pure = pure_declarations.to_owned()
  for declaration in pure {
    self.pure_builder.add_decl(declaration, span)
  }
  let metas = metas.to_owned()
  for meta in metas {
    self.pure_builder.add_meta(meta, span)
  }
  let definitions = definitions.to_owned()
  let declaration = ProgramDeclaration::recursive(
    self.anchor,
    definitions,
    pure,
    metas,
    span,
  )
  for definition in definitions {
    let symbol = definition.view().symbol
    let name = symbol.view().name
    self.add_exported_routine(name, symbol, span)
  }
  self.push_item(Udecl(declaration))
}

///|
pub fn PmoduleBuilder::add_exception_decl(
  self : PmoduleBuilder,
  exception : XSymbol,
  pure_declarations : ArrayView[@logic.Decl],
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.add_exception_decl_with_metas(exception, pure_declarations, [], span)
}

///|
pub fn PmoduleBuilder::add_exception_decl_with_metas(
  self : PmoduleBuilder,
  exception : XSymbol,
  pure_declarations : ArrayView[@logic.Decl],
  metas : ArrayView[@theory.Meta],
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  require_mlw_context(self.anchor, exception.semantic_id(), span)
  let pure = pure_declarations.to_owned()
  for declaration in pure {
    self.pure_builder.add_decl(declaration, span)
  }
  let metas = metas.to_owned()
  for meta in metas {
    self.pure_builder.add_meta(meta, span)
  }
  let name = exception.view().name.view().name
  self.add_exported_exception(name, exception, span)
  self.push_item(Udecl(PDexn(exception, pure, metas)))
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
  self.remember_module(used)
  self.pure_builder.add_use(used.pure_theory, import_, span)
  if import_ {
    self.merge_exported_namespace(used.export_namespace, span)
  } else {
    self.add_exported_subspace(
      used.key.view().name,
      used.export_namespace,
      span,
    )
  }
  self.push_item(Uuse(used.key))
}

///|
/// Adds a semantic module dependency for symbols used only inside a
/// declaration body, without exposing its pure or program namespace.
pub fn PmoduleBuilder::add_hidden_use(
  self : PmoduleBuilder,
  used : Pmodule,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  require_mlw_context(self.anchor, used.anchor, span)
  let already_used = self.dependencies.any(entry => entry.0 == used.key)
  let already_known = self.pure_builder.knows_theory(used.pure_theory)
  let add_dependency = !already_used && !already_known
  if add_dependency {
    self.remember_module(used)
  }
  self.pure_builder.add_hidden_use(used.pure_theory, span)
  self.current_namespace = self.current_namespace.overlay(used.export_namespace)
  if add_dependency {
    self.push_item(Uuse(used.key))
  }
}

///|
pub fn PmoduleBuilder::add_meta(
  self : PmoduleBuilder,
  meta : @theory.Meta,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  self.pure_builder.add_meta(meta, span)
  self.push_item(Umeta(meta))
}

///|
/// Records a fully translated program clone while the pure clone engine
/// performs and validates the corresponding theory clone. `cloned_namespace`
/// is the namespace produced by the program-symbol clone pass.
pub fn PmoduleBuilder::add_clone(
  self : PmoduleBuilder,
  source : Pmodule,
  pure_instantiation : @theory.TheoryInstantiation,
  witness : ProgramCloneWitness,
  cloned_namespace : ProgramNamespace,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  require_mlw_context(self.anchor, source.anchor, span)
  self.remember_module(source)
  require_mlw_context(self.anchor, witness.context_anchor(), span)
  if witness.view().source != source.key {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "program clone witness names a different source module",
    )
  }
  require_program_namespace_context(self.anchor, cloned_namespace, span)
  ignore(
    self.pure_builder.add_clone(
      source.pure_theory,
      pure_instantiation,
      span,
      omit_empty_source_subspaces=true,
    ),
  )
  self.merge_exported_namespace(cloned_namespace, span)
  self.finish_clone(source, witness, cloned_namespace, span)
}

///|
/// Finishes the program half of a clone whose pure theory and exported program
/// units have already been cloned. This split lets source elaboration construct
/// program symbols from the exact core `SymbolMap` returned by the theory clone
/// engine without merging the source namespace a second time.
pub fn PmoduleBuilder::finish_clone(
  self : PmoduleBuilder,
  source : Pmodule,
  witness : ProgramCloneWitness,
  cloned_namespace : ProgramNamespace,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  require_mlw_context(self.anchor, source.anchor, span)
  self.remember_module(source)
  require_mlw_context(self.anchor, witness.context_anchor(), span)
  if witness.view().source != source.key {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "program clone witness names a different source module",
    )
  }
  require_program_namespace_context(self.anchor, cloned_namespace, span)
  self.push_item(Uclone(witness))
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
  self.open_scope(scope_name, span)
  self.add_use(used, true, span)
  self.close_scope(import_, span)
}

///|
pub fn PmoduleBuilder::close(self : PmoduleBuilder) -> Pmodule raise {
  self.require_open(None)
  if !self.scope_names.is_empty() {
    fail_mlw(
      InvalidProgramDeclaration,
      None,
      "cannot close a program module while a namespace scope is open",
    )
  }
  self.closed = true
  Pmodule::trusted_new_with_dependencies(
    self.key,
    self.pure_builder.close(),
    self.items,
    self.export_namespace,
    self.dependencies,
  )
}
