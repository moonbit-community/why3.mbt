// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
fn append_expression_variable(
  variables : Array[PVariable],
  variable : PVariable,
) -> Unit {
  if !variables.any(existing => existing == variable) {
    variables.push(variable)
  }
}

///|
fn expression_term_reads(
  term : @logic.Term,
  variables : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> Array[PVariable] raise MlwError {
  let reads : Array[PVariable] = []
  for symbol in term.free_variables() {
    let mut found : PVariable? = None
    for variable in variables {
      if variable.view().pure_symbol == symbol {
        found = Some(variable)
        break
      }
    }
    guard found is Some(variable) else {
      fail_mlw(
        UnboundSpecificationVariable,
        span,
        "expression term references an unknown program variable",
      )
    }
    append_expression_variable(reads, variable)
  }
  reads
}

///|
fn make_expr(
  node : ExprNode,
  ity : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  effect : Effect,
  mask : ProgramMask,
) -> Expr {
  {
    node,
    ity,
    origin,
    attributes: @identity.SemanticAttributes::from_array(attributes),
    effect,
    mask: if effect.view().ghost {
      Ghost
    } else {
      mask
    },
  }
}

///|
pub fn ProgramPattern::trusted_new(
  pattern : @logic.Pattern,
  ity : Ity,
  mask : ProgramMask,
  failure : PatternGhost,
  variables : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> ProgramPattern raise {
  if pattern.ty() != ity.to_ty(span) {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "program pattern and matched program type differ",
    )
  }
  let variables = variables.to_owned()
  let bound = pattern.bound_variables()
  if bound.length() != variables.length() {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "program pattern variable map is incomplete",
    )
  }
  for index = 0; index < variables.length(); index = index + 1 {
    let variable = variables[index]
    require_mlw_context(ity.context_anchor(), variable.semantic_id(), span)
    if !bound.any(symbol => symbol == variable.view().pure_symbol) {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "program pattern variable is not bound by its pure pattern",
      )
    }
    for previous = 0; previous < index; previous = previous + 1 {
      if variables[previous] == variable {
        fail_mlw(
          InvalidProgramDeclaration,
          span,
          "program pattern variable map contains a duplicate",
        )
      }
    }
  }
  { pattern, ity, mask: mask.validate_for_ity(ity, span), failure, variables }
}

///|
pub fn ProgramPattern::view(self : ProgramPattern) -> ProgramPatternView {
  {
    pattern: self.pattern,
    ity: self.ity,
    mask: self.mask,
    failure: self.failure,
    variables: self.variables[:],
  }
}

///|
fn prepattern_constructor_arity(
  symbol : RoutineSymbol,
  span : @identity.SourceSpan?,
) -> (@logic.LSymbol, Int) raise MlwError {
  guard symbol.view().logic is RLls(logic_symbol) else {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "program pattern application expects a constructor routine",
    )
  }
  guard logic_symbol.view().role is Constructor(count) else {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "program pattern application expects a logical constructor",
    )
  }
  (logic_symbol, count)
}

///|
fn mark_ghost_pattern_name(
  ghost_names : Array[Bytes],
  name : @theory.SemanticName,
  ghost : Bool,
  mask : ProgramMask,
) -> Unit {
  let bytes = name.view().name
  if (ghost || mask.is_ghost()) &&
    !ghost_names.any(existing => existing == bytes) {
    ghost_names.push(bytes)
  }
}

///|
fn scan_prepattern_ghosts(
  pattern : PrePattern,
  inherited_failure : PatternGhost,
  mask : ProgramMask,
  ghost_names : Array[Bytes],
  failure : Ref[PatternGhost],
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  match pattern {
    PPwild => ()
    PPvar(name, ghost) =>
      mark_ghost_pattern_name(ghost_names, name, ghost, mask)
    PPas(inner, name, ghost) => {
      mark_ghost_pattern_name(ghost_names, name, ghost, mask)
      scan_prepattern_ghosts(
        inner, inherited_failure, mask, ghost_names, failure, span,
      )
    }
    PPor(left, right) => {
      scan_prepattern_ghosts(left, PGfail, mask, ghost_names, failure, span)
      scan_prepattern_ghosts(
        right, inherited_failure, mask, ghost_names, failure, span,
      )
    }
    PPapp(symbol, arguments) => {
      let (_, constructor_count) = prepattern_constructor_arity(symbol, span)
      if mask is Ghost && constructor_count > 1 && !(failure.val is PGfail) {
        failure.val = inherited_failure
      }
      let formals = symbol.view().cty.view().arguments
      if formals.length() != arguments.length() {
        fail_mlw(
          InvalidProgramDeclaration,
          span,
          "constructor pattern has the wrong arity",
        )
      }
      let masks : Array[ProgramMask] = match mask {
        Ghost => [ for _ in arguments => Ghost ]
        Visible => [ for formal in formals => ProgramMask::of_variable(formal) ]
        Tuple(items) => {
          if items.length() != arguments.length() {
            fail_mlw(
              InvalidProgramMask,
              span,
              "tuple pattern mask has the wrong arity",
            )
          }
          items.copy()
        }
      }
      for index = 0; index < arguments.length(); index = index + 1 {
        scan_prepattern_ghosts(
          arguments[index],
          inherited_failure,
          masks[index],
          ghost_names,
          failure,
          span,
        )
      }
    }
  }
}

///|
fn find_pattern_variable_by_name(
  variables : ArrayView[PVariable],
  name : BytesView,
) -> PVariable? {
  for variable in variables {
    if variable.view().name.view().name[:] == name {
      return Some(variable)
    }
  }
  None
}

///|
fn build_program_pattern(
  context : @identity.CompilationContext,
  pattern : PrePattern,
  ity : Ity,
  ghost_names : ArrayView[Bytes],
  variables : Array[PVariable],
  span : @identity.SourceSpan?,
) -> @logic.Pattern raise {
  match pattern {
    PPwild => @logic.Pattern::wild(ity.to_ty(span))
    PPvar(name, _) => {
      let bytes = name.view().name
      let variable = match find_pattern_variable_by_name(variables, bytes) {
        Some(variable) => {
          if variable.view().ity != ity {
            fail_mlw(
              ProgramTypeMismatch,
              span,
              "or-pattern binds one name at different program types",
            )
          }
          variable
        }
        None => {
          let variable = PVariable::trusted_new(
            context,
            name,
            ity,
            ghost_names.any(candidate => candidate == bytes),
            span,
          )
          variables.push(variable)
          variable
        }
      }
      @logic.Pattern::variable(variable.view().pure_symbol)
    }
    PPas(inner, name, _) => {
      let inner = build_program_pattern(
        context, inner, ity, ghost_names, variables, span,
      )
      let variable_pattern = build_program_pattern(
        context,
        PPvar(name, false),
        ity,
        ghost_names,
        variables,
        span,
      )
      guard variable_pattern.view() is Pvar(variable) else {
        abort("program pattern variable construction invariant failed")
      }
      @logic.Pattern::as_pattern(inner, variable, span)
    }
    PPor(left, right) =>
      @logic.Pattern::or(
        build_program_pattern(context, left, ity, ghost_names, variables, span),
        build_program_pattern(context, right, ity, ghost_names, variables, span),
        span,
      )
    PPapp(symbol, arguments) => {
      let (logic_symbol, _) = prepattern_constructor_arity(symbol, span)
      let cty = symbol.view().cty.view()
      if cty.arguments.length() != arguments.length() {
        fail_mlw(
          InvalidProgramDeclaration,
          span,
          "constructor pattern has the wrong arity",
        )
      }
      let mut substitution = cty.freeze
      substitution = substitution.match_ity(cty.result, ity, span)
      let built : Array[@logic.Pattern] = []
      for index = 0; index < arguments.length(); index = index + 1 {
        built.push(
          build_program_pattern(
            context,
            arguments[index],
            substitution.instantiate(cty.arguments[index].view().ity, span),
            ghost_names,
            variables,
            span,
          ),
        )
      }
      @logic.Pattern::app(logic_symbol, built, ity.to_ty(span), span)
    }
  }
}

///|
pub fn ProgramPattern::new(
  context : @identity.CompilationContext,
  pattern : PrePattern,
  ity : Ity,
  mask : ProgramMask,
  span : @identity.SourceSpan?,
) -> ProgramPattern raise {
  if !context.contains(ity.context_anchor()) {
    fail_mlw(MlwContextMismatch, span, "pattern belongs to another context")
  }
  let mask = mask.validate_for_ity(ity, span)
  let ghost_names : Array[Bytes] = []
  let failure = Ref(PGnone)
  scan_prepattern_ghosts(pattern, PGlast, mask, ghost_names, failure, span)
  let variables : Array[PVariable] = []
  let pure_pattern = build_program_pattern(
    context, pattern, ity, ghost_names, variables, span,
  )
  { pattern: pure_pattern, ity, mask, failure: failure.val, variables }
}

///|
pub fn ForBounds::new(
  first : PVariable,
  direction : ForDirection,
  last : PVariable,
  span : @identity.SourceSpan?,
) -> ForBounds raise MlwError {
  require_mlw_context(first.semantic_id(), last.semantic_id(), span)
  if first.view().ity != last.view().ity {
    fail_mlw(
      ProgramTypeMismatch,
      span,
      "for-loop bounds have different program types",
    )
  }
  { first, direction, last }
}

///|
pub fn ForBounds::view(self : ForBounds) -> ForBoundsView {
  { first: self.first, direction: self.direction, last: self.last }
}

///|
pub fn ProgramVariant::new(
  term : @logic.Term,
  relation : @logic.LSymbol?,
  span : @identity.SourceSpan?,
) -> ProgramVariant raise MlwError {
  guard term.ty() is Some(term_type) else {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "termination variant must be a value term",
    )
  }
  if relation is Some(symbol) {
    let view = symbol.view()
    if view.result_type is Some(_) ||
      view.argument_types.length() != 2 ||
      view.argument_types[0] != term_type ||
      view.argument_types[1] != term_type {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "variant relation must be a binary predicate over the variant type",
      )
    }
  }
  { term, relation }
}

///|
pub fn ProgramVariant::view(self : ProgramVariant) -> ProgramVariantView {
  { term: self.term, relation: self.relation }
}

///|
pub fn Assignment::new(
  region : PVariable,
  field : RoutineSymbol,
  value : PVariable,
  span : @identity.SourceSpan?,
) -> Assignment raise MlwError {
  require_mlw_context(region.semantic_id(), field.semantic_id(), span)
  require_mlw_context(region.semantic_id(), value.semantic_id(), span)
  if field.view().field is None {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "assignment routine is not a record projection",
    )
  }
  { region, field, value }
}

///|
pub fn Assignment::view(self : Assignment) -> AssignmentView {
  { region: self.region, field: self.field, value: self.value }
}

///|
pub fn Cexp::view(self : Cexp) -> CexpView {
  match self.node {
    CallCexp(symbol, arguments) => Capp(symbol, arguments[:])
    PureCexp(symbol, arguments) => Cpur(symbol, arguments[:])
    FunctionCexp(body) => Cfun(body)
    AnyCexp => Cany
  }
}

///|
pub fn Cexp::cty(self : Cexp) -> Cty {
  self.cty
}

///|
/// Rebuilds a validated computation node during module cloning while
/// preserving the already translated computation type exactly.
pub fn Cexp::trusted_new(
  view : CexpView,
  cty : Cty,
  span : @identity.SourceSpan?,
) -> Cexp raise MlwError {
  let node = match view {
    Capp(symbol, arguments) => {
      require_mlw_context(cty.context_anchor(), symbol.semantic_id(), span)
      for argument in arguments {
        require_mlw_context(cty.context_anchor(), argument.semantic_id(), span)
      }
      CallCexp(symbol, arguments.to_owned())
    }
    Cpur(symbol, arguments) => {
      require_mlw_context(cty.context_anchor(), symbol.semantic_id(), span)
      for argument in arguments {
        require_mlw_context(cty.context_anchor(), argument.semantic_id(), span)
      }
      PureCexp(symbol, arguments.to_owned())
    }
    Cfun(body) => {
      require_mlw_context(cty.context_anchor(), body.context_anchor(), span)
      FunctionCexp(body)
    }
    Cany => AnyCexp
  }
  { node, cty }
}

///|
pub fn Cexp::any(cty : Cty) -> Cexp {
  { node: AnyCexp, cty }
}

///|
pub fn Cexp::function(
  cty : Cty,
  body : Expr,
  span : @identity.SourceSpan?,
) -> Cexp raise MlwError {
  require_mlw_context(cty.context_anchor(), body.context_anchor(), span)
  if cty.view().result != body.ity() {
    fail_mlw(
      InvalidComputationType,
      span,
      "function body and computation type have different result types",
    )
  }
  { node: FunctionCexp(body), cty }
}

///|
pub fn Cexp::call(
  symbol : RoutineSymbol,
  arguments : ArrayView[PVariable],
  remaining_types : ArrayView[Ity],
  result : Ity,
  span : @identity.SourceSpan?,
) -> Cexp raise {
  let arguments = arguments.to_owned()
  let mut cty = symbol.view().cty.apply(
    symbol.compilation_context(),
    arguments,
    remaining_types,
    result,
    span,
  )
  if remaining_types.is_empty() &&
    symbol.view().origin
    .attributes()
    .any(attribute => attribute == b"why3:builtin:tuple-constructor") {
    cty = cty.tuple_application(arguments, span)
  }
  { node: CallCexp(symbol, arguments), cty }
}

///|
pub fn Cexp::pure_application(
  context : @identity.CompilationContext,
  symbol : @logic.LSymbol,
  arguments : ArrayView[PVariable],
  result : Ity,
  equality : @logic.LSymbol,
  boolean_true : @logic.LSymbol,
  span : @identity.SourceSpan?,
) -> Cexp raise {
  require_mlw_context(result.context_anchor(), symbol.semantic_id(), span)
  require_mlw_context(result.context_anchor(), equality.semantic_id(), span)
  require_mlw_context(result.context_anchor(), boolean_true.semantic_id(), span)
  if !result.is_pure() {
    fail_mlw(
      InvalidComputationType,
      span,
      "pure logic application has an impure program result type",
    )
  }
  let arguments = arguments.to_owned()
  for argument in arguments {
    require_mlw_context(result.context_anchor(), argument.semantic_id(), span)
  }
  let result_type = match symbol.view().result_type {
    Some(_) => Some(result.to_ty(span))
    None => {
      match result.to_ty(span).view() {
        TyApp(type_symbol, _) if type_symbol.builtin_kind()
          is Some(BuiltinBoolean) => ()
        _ =>
          fail_mlw(
            ProgramTypeMismatch,
            span,
            "predicate application does not have boolean program type",
          )
      }
      None
    }
  }
  let application = @logic.Term::elaborated_apply(
    symbol,
    [
      for argument in arguments => {
        @logic.Term::variable(argument.view().pure_symbol)
      }
    ],
    result_type,
    None,
  )
  let result_symbol = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", None, []),
    result.to_ty(span),
    None,
  )
  let result_term = @logic.Term::variable(result_symbol)
  let formula = match symbol.view().result_type {
    Some(_) =>
      @logic.Term::elaborated_apply(
        equality,
        [result_term, application],
        None,
        None,
      )
    None => {
      let true_term = @logic.Term::elaborated_apply(
        boolean_true,
        [],
        boolean_true.view().result_type,
        None,
      )
      let result_is_true = @logic.Term::elaborated_apply(
        equality,
        [result_term, true_term],
        None,
        None,
      )
      @logic.Term::binary(Iff, result_is_true, application, None)
    }
  }
  let postcondition = Postcondition::trusted_new(result_symbol, formula, None)
  let cty = Cty::new_with_variables(
    arguments,
    [],
    [],
    [postcondition],
    [],
    [],
    Effect::pure(true).spoil(result),
    result,
    span,
  )
  { node: PureCexp(symbol, arguments), cty }
}

///|
pub fn LetDefinition::view(self : LetDefinition) -> LetDefinitionView {
  match self.definition_node {
    VariableDefinition(variable, value) => LDvar(variable, value)
    SymbolDefinition(symbol, computation) => LDsym(symbol, computation)
    RecursiveDefinitions(definitions) => LDrec(definitions[:])
  }
}

///|
pub fn LetDefinition::variable(
  variable : PVariable,
  value : Expr,
  span : @identity.SourceSpan?,
) -> LetDefinition raise MlwError {
  require_mlw_context(variable.semantic_id(), value.context_anchor(), span)
  if variable.view().ity != value.ity() {
    fail_mlw(
      ProgramTypeMismatch,
      span,
      "let binder and value have different program types",
    )
  }
  { definition_node: VariableDefinition(variable, value) }
}

///|
pub fn LetDefinition::symbol(
  symbol : RoutineSymbol,
  computation : Cexp,
  span : @identity.SourceSpan?,
) -> LetDefinition raise MlwError {
  symbol.refresh_definition_cty(computation.cty(), span)
  require_mlw_context(
    symbol.semantic_id(),
    computation.cty().context_anchor(),
    span,
  )
  { definition_node: SymbolDefinition(symbol, computation) }
}

///|
fn recursive_symbol_member(
  symbols : ArrayView[RoutineSymbol],
  symbol : RoutineSymbol,
) -> Bool {
  symbols.any(candidate => candidate == symbol)
}

///|
fn Cexp::refresh_recursive_calls(
  self : Cexp,
  symbols : ArrayView[RoutineSymbol],
  span : @identity.SourceSpan?,
) -> Bool raise MlwError {
  let previous = self.cty.view().effect
  match self.node {
    CallCexp(symbol, arguments) if recursive_symbol_member(symbols, symbol) => {
      let view = self.cty.view()
      let refreshed = Cexp::call(
        symbol,
        arguments,
        view.arguments.map(argument => argument.view().ity),
        view.result,
        span,
      ) catch {
        MlwError(diagnostic) => raise MlwError(diagnostic)
        _ =>
          fail_mlw(
            InvalidComputationType,
            span,
            "recursive call refinement failed",
          )
      }
      self.cty = refreshed.cty
    }
    FunctionCexp(body) => {
      ignore(body.refresh_recursive_calls(symbols, span))
      let view = self.cty.view()
      self.cty = Cty::new_with_variables(
        view.program_variables,
        view.arguments,
        view.preconditions,
        view.postconditions,
        view.exceptional_postconditions,
        view.oldies,
        body.effect(),
        view.result,
        span,
        mask=view.mask,
      )
    }
    CallCexp(_, _) | PureCexp(_, _) | AnyCexp => ()
  }
  previous != self.cty.view().effect
}

///|
fn Expr::refresh_recursive_calls(
  self : Expr,
  symbols : ArrayView[RoutineSymbol],
  span : @identity.SourceSpan?,
) -> Bool raise MlwError {
  let previous = self.effect
  match self.node {
    ExecuteExpr(computation, execution) =>
      if computation.refresh_recursive_calls(symbols, span) {
        let refreshed = computation.cty()
        if refreshed.view().arguments.is_empty() {
          self.node = ExecuteExpr(computation, refreshed)
          self.effect = refreshed.view().effect
        } else {
          self.effect = execution.view().effect.union_parallel(
            refreshed.view().effect,
            span,
          )
        }
      }
    LetExpr(definition, body) => {
      match definition.definition_node {
        VariableDefinition(_, value) =>
          ignore(value.refresh_recursive_calls(symbols, span))
        SymbolDefinition(_, computation) =>
          ignore(computation.refresh_recursive_calls(symbols, span))
        RecursiveDefinitions(nested) =>
          stabilize_recursive_definitions(nested, span)
      }
      ignore(body.refresh_recursive_calls(symbols, span))
      self.effect = match definition.definition_node {
        VariableDefinition(variable, value) =>
          value.effect().union_sequential(body.effect().bind([variable]), span)
        SymbolDefinition(symbol, computation) =>
          bind_routine_mapping(symbol, body.effect()).read_pre(
            computation.cty().reads(),
            span,
          )
        RecursiveDefinitions(definitions) => {
          let mut effect = body.effect()
          let reads : Array[PVariable] = []
          for definition in definitions {
            effect = bind_routine_mapping(definition.symbol, effect)
            for read in definition.internal_symbol.view().cty.reads() {
              append_expression_variable(reads, read)
            }
          }
          effect.read_pre(reads, span)
        }
      }
    }
    IfExpr(condition, consequent, alternative) => {
      ignore(condition.refresh_recursive_calls(symbols, span))
      ignore(consequent.refresh_recursive_calls(symbols, span))
      ignore(alternative.refresh_recursive_calls(symbols, span))
      let branches = consequent
        .effect()
        .union_parallel(alternative.effect(), span)
      let effect = condition.effect().union_sequential(branches, span)
      let ghost = condition.mask().is_ghost() &&
        !consequent.is_absurd() &&
        !alternative.is_absurd()
      self.effect = effect.ghostify(ghost, span)
    }
    MatchExpr(scrutinee, regular, exceptional) => {
      ignore(scrutinee.refresh_recursive_calls(symbols, span))
      for branch in regular {
        ignore(branch.body.refresh_recursive_calls(symbols, span))
      }
      for branch in exceptional {
        ignore(branch.body.refresh_recursive_calls(symbols, span))
      }
      let mut branch_effect = Effect::pure(false)
      for branch in regular {
        branch_effect = branch_effect.union_parallel(
          branch.body.effect().bind(branch.pattern.variables),
          span,
        )
      }
      for branch in exceptional {
        branch_effect = branch_effect.union_parallel(
          branch.body.effect().bind(branch.variables),
          span,
        )
      }
      let mut scrutinee_effect = scrutinee.effect()
      for branch in exceptional {
        scrutinee_effect = scrutinee_effect.catch_exception(branch.exception)
      }
      let effect = scrutinee_effect.union_sequential(branch_effect, span)
      let ghost = regular_match_is_ghost(regular) ||
        (scrutinee.effect().view().ghost && !exceptional.is_empty())
      self.effect = effect.ghostify(ghost, span)
    }
    WhileExpr(condition, _, variants, body) => {
      ignore(condition.refresh_recursive_calls(symbols, span))
      ignore(body.refresh_recursive_calls(symbols, span))
      let mut effect = body.effect().read_pre(previous.view().reads, span)
      effect = condition.effect().union_sequential(effect, span)
      effect = effect.ghostify(condition.mask().is_ghost(), span)
      if variants.is_empty() {
        effect = effect.diverge(span)
      }
      ignore(effect.union_sequential(effect, span))
      self.effect = effect
    }
    ForExpr(variable, bounds, internal, _, body) => {
      ignore(body.refresh_recursive_calls(symbols, span))
      let bounds = bounds.view()
      let mut effect = body.effect().read_pre(previous.view().reads, span)
      let ghost = variable.view().ghost ||
        bounds.first.view().ghost ||
        bounds.last.view().ghost
      effect = effect.ghostify(ghost, span)
      ignore(effect.union_sequential(effect, span))
      effect = effect.bind([variable, internal])
      effect = effect.read_pre([bounds.last], span)
      self.effect = effect.read_pre([bounds.first], span)
    }
    RaiseExpr(_, payload) => {
      ignore(payload.refresh_recursive_calls(symbols, span))
      self.effect = previous.union_parallel(payload.effect(), span)
    }
    ExceptionExpr(_, body) => {
      ignore(body.refresh_recursive_calls(symbols, span))
      self.effect = body.effect()
    }
    GhostExpr(body) => {
      ignore(body.refresh_recursive_calls(symbols, span))
      self.effect = body.effect().ghostify(true, span)
    }
    VariableExpr(_)
    | ConstantExpr(_)
    | AssignmentExpr(_)
    | AssertionExpr(_, _)
    | PureExpr(_)
    | AbsurdExpr => ()
  }
  previous != self.effect
}

///|
fn recursive_decrease_precondition(
  definition : RecursiveDefinition,
  span : @identity.SourceSpan?,
) -> @logic.Term raise MlwError {
  guard definition.internal_symbol.view().cty.view().preconditions
    is [first, ..] &&
    first.view() is Tapp(symbol, _, _) else {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "recursive internal symbol lost its decrease precondition",
    )
  }
  @logic.Term::apply_predicate(
    symbol,
    definition.variants.map(variant => variant.term),
    span,
  ) catch {
    @logic.TypeError(diagnostic) =>
      fail_mlw(InvalidProgramDeclaration, span, diagnostic.message)
  }
}

///|
fn rebuild_recursive_cty(
  template : Cty,
  effect : Effect,
  span : @identity.SourceSpan?,
) -> Cty raise MlwError {
  let view = template.view()
  Cty::new_with_variables(
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
fn stabilize_recursive_definitions(
  definitions : ArrayView[RecursiveDefinition],
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  let symbols = definitions.map(definition => definition.internal_symbol)
  let external_templates = definitions.map(definition => {
    definition.symbol.view().cty
  })
  let start_diverges = definitions[0].variants.is_empty() &&
    definitions.any(definition => definition.symbol.kind() is RKnone)
  for definition in definitions {
    let decrease_variables = definition.internal_symbol.view().cty.view().program_variables
    let mut effect = Effect::pure(false)
    if start_diverges {
      effect = effect.diverge(span)
    }
    effect = effect.ghostify(definition.symbol.is_ghost(), span)
    definition.internal_symbol.cty = rebuild_recursive_cty(
      definition.function_.cty(),
      effect,
      span,
    ).add_preconditions_with_variables(
      decrease_variables,
      [recursive_decrease_precondition(definition, span)],
      span,
    )
  }
  let limit = definitions.length() * 2 + 4
  for iteration = 0; iteration < limit; iteration = iteration + 1 {
    let mut changed = false
    for definition in definitions {
      if definition.function_.refresh_recursive_calls(symbols, span) {
        changed = true
      }
    }
    for index, definition in definitions {
      let function_cty = definition.function_.cty()
      let decrease_variables = definition.internal_symbol.view().cty.view().program_variables
      let internal_cty = function_cty.add_preconditions_with_variables(
        decrease_variables,
        [recursive_decrease_precondition(definition, span)],
        span,
      )
      if internal_cty.view().effect !=
        definition.internal_symbol.view().cty.view().effect {
        changed = true
      }
      definition.internal_symbol.cty = internal_cty
      let public_effect = function_cty
        .read_pre(internal_cty.reads(), span)
        .view().effect
      definition.symbol.cty = rebuild_recursive_cty(
        external_templates[index],
        public_effect,
        span,
      )
    }
    if !changed {
      return
    }
  }
  fail_mlw(
    InvalidProgramDeclaration,
    span,
    "recursive effect refinement did not converge",
  )
}

///|
pub fn LetDefinition::recursive(
  definitions : ArrayView[RecursiveDefinition],
  span : @identity.SourceSpan?,
) -> LetDefinition raise MlwError {
  let definitions = definitions.to_owned()
  if definitions.is_empty() {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "recursive definition group cannot be empty",
    )
  }
  let anchor = definitions[0].symbol.semantic_id()
  for definition in definitions {
    require_mlw_context(anchor, definition.symbol.semantic_id(), span)
    require_mlw_context(anchor, definition.internal_symbol.semantic_id(), span)
  }
  stabilize_recursive_definitions(definitions, span)
  { definition_node: RecursiveDefinitions(definitions) }
}

///|
pub fn RecursiveDefinition::new(
  symbol : RoutineSymbol,
  internal_symbol : RoutineSymbol,
  function_ : Cexp,
  variants : ArrayView[ProgramVariant],
  span : @identity.SourceSpan?,
) -> RecursiveDefinition raise MlwError {
  require_mlw_context(symbol.semantic_id(), internal_symbol.semantic_id(), span)
  require_mlw_context(
    symbol.semantic_id(),
    function_.cty().context_anchor(),
    span,
  )
  if !(function_.view() is Cfun(_)) {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "recursive routine body must be a function computation",
    )
  }
  { symbol, internal_symbol, function_, variants: variants.to_owned() }
}

///|
pub fn RecursiveDefinition::view(
  self : RecursiveDefinition,
) -> RecursiveDefinitionView {
  {
    symbol: self.symbol,
    internal_symbol: self.internal_symbol,
    function_: self.function_,
    variants: self.variants[:],
  }
}

///|
pub fn RegularBranch::new(
  pattern : ProgramPattern,
  body : Expr,
  span : @identity.SourceSpan?,
) -> RegularBranch raise MlwError {
  require_mlw_context(pattern.ity.context_anchor(), body.context_anchor(), span)
  { pattern, body }
}

///|
pub fn RegularBranch::view(self : RegularBranch) -> RegularBranchView {
  { pattern: self.pattern, body: self.body }
}

///|
pub fn ExceptionalBranch::new(
  exception : XSymbol,
  variables : ArrayView[PVariable],
  body : Expr,
  span : @identity.SourceSpan?,
) -> ExceptionalBranch raise MlwError {
  let variables = variables.to_owned()
  require_mlw_context(exception.semantic_id(), body.context_anchor(), span)
  for variable in variables {
    require_mlw_context(exception.semantic_id(), variable.semantic_id(), span)
  }
  { exception, variables, body }
}

///|
pub fn ExceptionalBranch::view(
  self : ExceptionalBranch,
) -> ExceptionalBranchView {
  { exception: self.exception, variables: self.variables[:], body: self.body }
}

///|
pub fn Expr::variable(
  variable : PVariable,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
) -> Expr {
  make_expr(
    VariableExpr(variable),
    variable.view().ity,
    origin,
    attributes,
    Effect::from_reads([variable], variable.view().ghost),
    ProgramMask::of_variable(variable),
  )
}

///|
pub fn Expr::constant(
  constant : @logic.Constant,
  ity : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
) -> Expr raise {
  ignore(@logic.Term::constant(constant, ity.to_ty(None), None))
  make_expr(
    ConstantExpr(constant),
    ity,
    origin,
    attributes,
    Effect::pure(false),
    Visible,
  )
}

///|
pub fn Expr::execute(
  computation : Cexp,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  let cty = computation.cty()
  if !cty.view().arguments.is_empty() {
    fail_mlw(
      InvalidComputationType,
      span,
      "computation with remaining parameters cannot be directly executed",
    )
  }
  make_expr(
    ExecuteExpr(computation, cty),
    cty.view().result,
    origin,
    attributes,
    cty.view().effect,
    cty.view().mask,
  )
}

///|
pub fn Expr::execute_function_value(
  computation : Cexp,
  context : @identity.CompilationContext,
  function_type : ProgramTypeSymbol,
  application : @logic.LSymbol,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise {
  let executable = computation
    .cty()
    .execute_as_function(context, function_type, application, span)
  make_expr(
    ExecuteExpr(computation, executable),
    executable.view().result,
    origin,
    attributes,
    executable.view().effect,
    executable.view().mask,
  )
}

///|
pub fn Expr::pure_application(
  context : @identity.CompilationContext,
  symbol : @logic.LSymbol,
  arguments : ArrayView[PVariable],
  result : Ity,
  equality : @logic.LSymbol,
  boolean_true : @logic.LSymbol,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise {
  Expr::execute(
    Cexp::pure_application(
      context, symbol, arguments, result, equality, boolean_true, span,
    ),
    origin,
    attributes,
    span,
  )
}

///|
pub fn Expr::routine_call(
  symbol : RoutineSymbol,
  arguments : ArrayView[PVariable],
  result : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise {
  Expr::execute(
    Cexp::call(symbol, arguments, [], result, span),
    origin,
    attributes,
    span,
  )
}

///|
fn bind_routine_mapping(symbol : RoutineSymbol, effect : Effect) -> Effect {
  match symbol.view().logic {
    RLpv(variable) => effect.bind([variable])
    RLnone | RLlemma => effect
    RLls(_) => effect
  }
}

///|
pub fn Expr::let_definition(
  definition : LetDefinition,
  body : Expr,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  let effect = match definition.view() {
    LDvar(variable, value) =>
      value.effect().union_sequential(body.effect().bind([variable]), span)
    LDsym(symbol, computation) =>
      bind_routine_mapping(symbol, body.effect()).read_pre(
        computation.cty().reads(),
        span,
      )
    LDrec(definitions) => {
      let mut body_effect = body.effect()
      let reads : Array[PVariable] = []
      for definition in definitions {
        body_effect = bind_routine_mapping(definition.symbol, body_effect)
        for read in definition.internal_symbol.view().cty.reads() {
          append_expression_variable(reads, read)
        }
      }
      body_effect.read_pre(reads, span)
    }
  }
  make_expr(
    LetExpr(definition, body),
    body.ity(),
    origin,
    attributes,
    effect,
    body.mask(),
  )
}

///|
pub fn Expr::let_in(
  binder : PVariable,
  value : Expr,
  body : Expr,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  Expr::let_definition(
    LetDefinition::variable(binder, value, span),
    body,
    origin,
    attributes,
    span,
  )
}

///|
fn Expr::is_absurd(self : Expr) -> Bool {
  self.node is AbsurdExpr
}

///|
pub fn Expr::if_then_else(
  condition : Expr,
  consequent : Expr,
  alternative : Expr,
  boolean : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  require_mlw_context(
    consequent.context_anchor(),
    condition.context_anchor(),
    span,
  )
  require_mlw_context(
    consequent.context_anchor(),
    alternative.context_anchor(),
    span,
  )
  if condition.ity() != boolean {
    fail_mlw(ProgramTypeMismatch, span, "if condition is not boolean")
  }
  if consequent.ity() != alternative.ity() {
    fail_mlw(ProgramTypeMismatch, span, "if branch types differ")
  }
  let branches = consequent.effect().union_parallel(alternative.effect(), span)
  let mut effect = condition.effect().union_sequential(branches, span)
  let ghost = condition.mask().is_ghost() &&
    !consequent.is_absurd() &&
    !alternative.is_absurd()
  effect = effect.ghostify(ghost, span)
  make_expr(
    IfExpr(condition, consequent, alternative),
    consequent.ity(),
    origin,
    attributes,
    effect,
    consequent.mask().union(alternative.mask(), span),
  )
}

///|
pub fn Expr::view(self : Expr) -> ExprView {
  match self.node {
    VariableExpr(variable) => Evar(variable)
    ConstantExpr(constant) => Econst(constant)
    ExecuteExpr(computation, cty) => Eexec(computation, cty)
    AssignmentExpr(assignments) => Eassign(assignments[:])
    LetExpr(definition, body) => Elet(definition, body)
    IfExpr(condition, consequent, alternative) =>
      Eif(condition, consequent, alternative)
    MatchExpr(scrutinee, regular, exceptional) =>
      Ematch(scrutinee, regular[:], exceptional[:])
    WhileExpr(condition, invariants, variants, body) =>
      Ewhile(condition, invariants[:], variants[:], body)
    ForExpr(variable, bounds, internal, invariants, body) =>
      Efor(variable, bounds, internal, invariants[:], body)
    RaiseExpr(exception, payload) => Eraise(exception, payload)
    ExceptionExpr(exception, body) => Eexn(exception, body)
    AssertionExpr(kind, formula) => Eassert(kind, formula)
    GhostExpr(body) => Eghost(body)
    PureExpr(term) => Epure(term)
    AbsurdExpr => Eabsurd
  }
}

///|
/// Rebuilds a translated expression graph while retaining the exact
/// translated type, effect, mask, origin, and attributes.
pub fn Expr::trusted_new(
  view : ExprView,
  ity : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  effect : Effect,
  mask : ProgramMask,
  span : @identity.SourceSpan?,
) -> Expr {
  let node = match view {
    Evar(variable) => VariableExpr(variable)
    Econst(constant) => ConstantExpr(constant)
    Eexec(computation, cty) => ExecuteExpr(computation, cty)
    Eassign(assignments) => AssignmentExpr(assignments.to_owned())
    Elet(definition, body) => LetExpr(definition, body)
    Eif(condition, consequent, alternative) =>
      IfExpr(condition, consequent, alternative)
    Ematch(scrutinee, regular, exceptional) =>
      MatchExpr(scrutinee, regular.to_owned(), exceptional.to_owned())
    Ewhile(condition, invariants, variants, body) =>
      WhileExpr(condition, invariants.to_owned(), variants.to_owned(), body)
    Efor(variable, bounds, internal, invariants, body) =>
      ForExpr(variable, bounds, internal, invariants.to_owned(), body)
    Eraise(exception, payload) => RaiseExpr(exception, payload)
    Eexn(exception, body) => ExceptionExpr(exception, body)
    Eassert(kind, formula) => AssertionExpr(kind, formula)
    Eghost(body) => GhostExpr(body)
    Epure(term) => PureExpr(term)
    Eabsurd => AbsurdExpr
  }
  ignore(span)
  make_expr(node, ity, origin, attributes, effect, mask)
}

///|
pub fn Expr::ity(self : Expr) -> Ity {
  self.ity
}

///|
pub fn Expr::context_anchor(self : Expr) -> @identity.SemanticId {
  self.ity.context_anchor()
}

///|
pub fn Expr::origin(self : Expr) -> @identity.Origin {
  self.origin
}

///|
pub fn Expr::attributes(self : Expr) -> ArrayView[Bytes] {
  self.attributes.items()
}

///|
pub fn Expr::effect(self : Expr) -> Effect {
  self.effect
}

///|
pub fn Expr::mask(self : Expr) -> ProgramMask {
  self.mask
}
