// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
pub fn Cexp::function_with_specification(
  program_variables : ArrayView[PVariable],
  arguments : ArrayView[PVariable],
  preconditions : ArrayView[@logic.Term],
  postconditions : ArrayView[Postcondition],
  exceptional_postconditions : ArrayView[ExceptionalPostconditions],
  oldies : ArrayView[OldSnapshot],
  body : Expr,
  span : @identity.SourceSpan?,
  mask? : ProgramMask = Visible,
) -> Cexp raise MlwError {
  let mask = mask.union(body.mask(), span)
  let cty = Cty::new_with_variables(
    program_variables,
    arguments,
    preconditions,
    postconditions,
    exceptional_postconditions,
    oldies,
    body.effect(),
    body.ity(),
    span,
    mask~,
  )
  { node: FunctionCexp(body), cty }
}

///|
pub fn Cexp::is_ghost(self : Cexp) -> Bool {
  self.cty.is_ghost()
}

///|
pub fn Expr::assignment(
  assignments : ArrayView[Assignment],
  unit : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  let assignments = assignments.to_owned()
  let effect_assignments : Array[(PVariable, PVariable, PVariable)] = []
  for assignment in assignments {
    guard assignment.field.view().field is Some(field) else {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "assignment routine is not a record projection",
      )
    }
    effect_assignments.push((assignment.region, field, assignment.value))
  }
  make_expr(
    AssignmentExpr(assignments),
    unit,
    origin,
    attributes,
    Effect::assign(effect_assignments, span),
    Visible,
  )
}

///|
fn append_expression_term_reads(
  reads : Array[PVariable],
  term : @logic.Term,
  variables : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> Unit raise MlwError {
  for variable in expression_term_reads(term, variables, span) {
    append_expression_variable(reads, variable)
  }
}

///|
fn variant_reads(
  variants : ArrayView[ProgramVariant],
  variables : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> Array[PVariable] raise MlwError {
  let reads : Array[PVariable] = []
  for variant in variants {
    append_expression_term_reads(reads, variant.term, variables, span)
  }
  reads
}

///|
fn specification_reads(
  invariants : ArrayView[@logic.Term],
  variants : ArrayView[ProgramVariant],
  variables : ArrayView[PVariable],
  span : @identity.SourceSpan?,
) -> Array[PVariable] raise MlwError {
  let reads = variant_reads(variants, variables, span)
  for invariant in invariants {
    if !invariant.is_formula() {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "loop invariant must be a formula",
      )
    }
    append_expression_term_reads(reads, invariant, variables, span)
  }
  reads
}

///|
pub fn Expr::while_loop(
  condition : Expr,
  invariants : ArrayView[@logic.Term],
  variants : ArrayView[ProgramVariant],
  body : Expr,
  boolean : Ity,
  unit : Ity,
  program_variables : ArrayView[PVariable],
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  require_mlw_context(condition.context_anchor(), body.context_anchor(), span)
  if condition.ity() != boolean {
    fail_mlw(ProgramTypeMismatch, span, "while condition is not boolean")
  }
  if body.ity() != unit {
    fail_mlw(ProgramTypeMismatch, span, "while body does not return unit")
  }
  let invariants = invariants.to_owned()
  let variants = variants.to_owned()
  let reads = specification_reads(invariants, variants, program_variables, span)
  let mut effect = body.effect().read_pre(reads, span)
  effect = condition.effect().union_sequential(effect, span)
  effect = effect.ghostify(condition.mask().is_ghost(), span)
  if variants.is_empty() {
    effect = effect.diverge(span)
  }
  ignore(effect.union_sequential(effect, span))
  make_expr(
    WhileExpr(condition, invariants, variants, body),
    unit,
    origin,
    attributes,
    effect,
    Visible,
  )
}

///|
fn is_integer_loop_type(ity : Ity, integer : Ity) -> Bool {
  if ity == integer {
    return true
  }
  match ity.view() {
    ItyApp(symbol, _, _) => symbol.view().definition is ProgramRange(_, _)
    ItyVar(_) | ItyReg(_) => false
  }
}

///|
pub fn Expr::for_loop(
  variable : PVariable,
  bounds : ForBounds,
  internal_variable : PVariable,
  invariants : ArrayView[@logic.Term],
  body : Expr,
  integer : Ity,
  unit : Ity,
  program_variables : ArrayView[PVariable],
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  let bounds_view = bounds.view()
  require_mlw_context(variable.semantic_id(), body.context_anchor(), span)
  if bounds_view.first.view().ity != variable.view().ity ||
    bounds_view.last.view().ity != variable.view().ity {
    fail_mlw(
      ProgramTypeMismatch,
      span,
      "for-loop bounds and index have different program types",
    )
  }
  if internal_variable.view().ity != integer {
    fail_mlw(
      ProgramTypeMismatch,
      span,
      "internal for-loop index does not have integer type",
    )
  }
  if body.ity() != unit {
    fail_mlw(ProgramTypeMismatch, span, "for-loop body does not return unit")
  }
  let invariants = invariants.to_owned()
  if variable != internal_variable {
    if !internal_variable.view().ghost {
      fail_mlw(
        InvalidProgramDeclaration,
        span,
        "internal for-loop index must be ghost",
      )
    }
    for invariant in invariants {
      if invariant
        .free_variables()
        .any(symbol => symbol == variable.view().pure_symbol) {
        fail_mlw(
          InvalidProgramDeclaration,
          span,
          "external for-loop index occurs in an invariant",
        )
      }
    }
    if !is_integer_loop_type(variable.view().ity, integer) {
      fail_mlw(
        ProgramTypeMismatch,
        span,
        "for-loop bounds must have integer or range type",
      )
    }
  }
  let reads = specification_reads(invariants, [], program_variables, span)
  let mut effect = body.effect().read_pre(reads, span)
  let ghost = variable.view().ghost ||
    bounds_view.first.view().ghost ||
    bounds_view.last.view().ghost
  effect = effect.ghostify(ghost, span)
  ignore(effect.union_sequential(effect, span))
  effect = effect.bind([variable, internal_variable])
  effect = effect.read_pre([bounds_view.last], span)
  effect = effect.read_pre([bounds_view.first], span)
  make_expr(
    ForExpr(variable, bounds, internal_variable, invariants, body),
    unit,
    origin,
    attributes,
    effect,
    Visible,
  )
}

///|
fn exception_branch_payload(
  branch : ExceptionalBranch,
  unit : Ity,
  span : @identity.SourceSpan?,
) -> (Ity, ProgramMask) raise MlwError {
  match branch.variables {
    [] => (unit, Visible)
    [variable] => (variable.view().ity, ProgramMask::of_variable(variable))
    variables => {
      let payload = branch.exception.view().ity
      guard payload.view() is ItyApp(_, arguments, _) &&
        arguments.length() == variables.length() else {
        fail_mlw(
          ProgramTypeMismatch,
          span,
          "exception branch destructuring does not match its payload",
        )
      }
      for index = 0; index < variables.length(); index = index + 1 {
        if arguments[index] != variables[index].view().ity {
          fail_mlw(
            ProgramTypeMismatch,
            span,
            "exception branch variable has the wrong payload type",
          )
        }
      }
      (
        payload,
        Tuple(
          [
            for variable in variables => ProgramMask::of_variable(variable)
          ],
        ).reduce(),
      )
    }
  }
}

///|
fn regular_match_is_ghost(branches : ArrayView[RegularBranch]) -> Bool {
  let mut last = false
  for branch in branches {
    if branch.body.is_absurd() {
      continue
    }
    match branch.pattern.failure {
      PGnone => if last { return true }
      PGlast => {
        if last {
          return true
        }
        last = true
      }
      PGfail => return true
    }
  }
  false
}

///|
pub fn Expr::match_with(
  scrutinee : Expr,
  regular_branches : ArrayView[RegularBranch],
  exceptional_branches : ArrayView[ExceptionalBranch],
  unit : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  let regular = regular_branches.to_owned()
  let exceptional = exceptional_branches.to_owned()
  let result = if regular.is_empty() {
    scrutinee.ity()
  } else {
    regular[0].body.ity()
  }
  for index, branch in regular {
    if branch.pattern.ity != scrutinee.ity() {
      fail_mlw(
        ProgramTypeMismatch,
        span,
        "match pattern and scrutinee have different program types",
      )
    }
    if result != unit && scrutinee.mask().spills_into(branch.pattern.mask) {
      fail_mlw(
        InvalidProgramMask,
        span,
        "non-ghost pattern occurs in a ghost position",
      )
    }
    if branch.body.ity() != result {
      fail_mlw(
        ProgramTypeMismatch,
        span,
        "match branch \{index} type differs: \{result.diagnostic_shape()} vs \{branch.body.ity().diagnostic_shape()}",
      )
    }
  }
  for branch in exceptional {
    let (payload, mask) = exception_branch_payload(branch, unit, span)
    let exception_view = branch.exception.view()
    if exception_view.ity != payload {
      fail_mlw(
        ProgramTypeMismatch,
        span,
        "exception branch payload type differs from its exception",
      )
    }
    if result != unit && exception_view.mask.spills_into(mask) {
      fail_mlw(
        InvalidProgramMask,
        span,
        "non-ghost exception pattern occurs in a ghost position",
      )
    }
    if branch.body.ity() != result {
      fail_mlw(ProgramTypeMismatch, span, "exception branch types differ")
    }
  }
  let mut mask = if regular.is_empty() { scrutinee.mask() } else { Visible }
  for branch in regular {
    mask = mask.union(branch.body.mask(), span)
  }
  for branch in exceptional {
    mask = mask.union(branch.body.mask(), span)
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
  let mut effect = scrutinee_effect.union_sequential(branch_effect, span)
  let ghost = regular_match_is_ghost(regular) ||
    (scrutinee.effect().view().ghost && !exceptional.is_empty())
  effect = effect.ghostify(ghost, span)
  make_expr(
    MatchExpr(scrutinee, regular, exceptional),
    result,
    origin,
    attributes,
    effect,
    mask,
  )
}

///|
pub fn Expr::raise_exception(
  exception : XSymbol,
  payload : Expr,
  result : Ity,
  unit : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  let exception_view = exception.view()
  if !exception_view.ity.same_skeleton(payload.ity(), span) {
    fail_mlw(
      ProgramTypeMismatch,
      span,
      "raised expression has the wrong exception payload type",
    )
  }
  require_mlw_context(result.context_anchor(), exception.semantic_id(), span)
  let ghost = payload.ity() != unit &&
    payload.mask().spills_into(exception_view.mask)
  let raised = Effect::pure(false)
    .raise_exception(exception)
    .ghostify(ghost, span)
  let effect = payload.effect().union_sequential(raised, span)
  make_expr(
    RaiseExpr(exception, payload),
    result,
    origin,
    attributes,
    effect,
    Visible,
  )
}

///|
pub fn Expr::exception_scope(
  exception : XSymbol,
  body : Expr,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  if body.effect().view().raises.any(raised => raised == exception) {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "locally declared exception escapes its scope",
    )
  }
  make_expr(
    ExceptionExpr(exception, body),
    body.ity(),
    origin,
    attributes,
    body.effect(),
    body.mask(),
  )
}

///|
pub fn Expr::ghostify(
  self : Expr,
  ghost : Bool,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  if !ghost {
    return self
  }
  make_expr(
    GhostExpr(self),
    self.ity(),
    origin,
    attributes,
    self.effect().ghostify(true, span),
    self.mask(),
  )
}

///|
pub fn Expr::pure_term(
  term : @logic.Term,
  result : Ity,
  program_variables : ArrayView[PVariable],
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise {
  match term.ty() {
    Some(ty) =>
      if ty != result.to_ty(span) {
        fail_mlw(
          ProgramTypeMismatch,
          span,
          "pure term and program expression have different types",
        )
      }
    None =>
      match result.to_ty(span).view() {
        TyApp(symbol, _) if symbol.builtin_kind() is Some(BuiltinBoolean) => ()
        _ =>
          fail_mlw(
            ProgramTypeMismatch,
            span,
            "formula-valued pure expression does not have boolean type",
          )
      }
  }
  let reads = expression_term_reads(term, program_variables, span)
  let mut effect = Effect::from_reads(reads, true)
  if !(term.view() is Tvar(_)) {
    effect = effect.spoil(result)
  }
  make_expr(PureExpr(term), result, origin, attributes, effect, Ghost)
}

///|
pub fn Expr::assertion(
  kind : AssertionKind,
  formula : @logic.Term,
  reads : ArrayView[PVariable],
  unit : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  if !formula.is_formula() {
    fail_mlw(InvalidProgramDeclaration, span, "assertion is not a formula")
  }
  for read in reads {
    require_mlw_context(unit.context_anchor(), read.semantic_id(), span)
  }
  make_expr(
    AssertionExpr(kind, formula),
    unit,
    origin,
    attributes,
    Effect::from_reads(reads, false),
    Visible,
  )
}

///|
pub fn Expr::assertion_with_variables(
  kind : AssertionKind,
  formula : @logic.Term,
  program_variables : ArrayView[PVariable],
  unit : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  Expr::assertion(
    kind,
    formula,
    expression_term_reads(formula, program_variables, span),
    unit,
    origin,
    attributes,
    span,
  )
}

///|
pub fn Expr::assert_formula(
  formula : @logic.Term,
  reads : ArrayView[PVariable],
  unit : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  Expr::assertion(Assert, formula, reads, unit, origin, attributes, span)
}

///|
pub fn Expr::assume_formula(
  formula : @logic.Term,
  reads : ArrayView[PVariable],
  unit : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  Expr::assertion(Assume, formula, reads, unit, origin, attributes, span)
}

///|
pub fn Expr::absurd(
  result : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
) -> Expr {
  make_expr(
    AbsurdExpr,
    result,
    origin,
    attributes,
    Effect::pure(false),
    Visible,
  )
}
