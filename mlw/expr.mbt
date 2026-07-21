// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
priv enum ExprNode {
  VariableExpr(PVariable)
  ConstantExpr(@logic.Constant)
  PureApplicationExpr(@logic.LSymbol, Array[PVariable])
  RoutineCallExpr(RoutineSymbol, Array[PVariable])
  LetExpr(PVariable, Expr, Expr)
  IfExpr(Expr, Expr, Expr)
  AssertExpr(@logic.Term)
  AssumeExpr(@logic.Term)
}

///|
/// The node view includes the result Ity exactly where canonical schema v2
/// records it. Decoration is exposed by the accessors below.
pub(all) enum ExprView {
  Evar(PVariable, Ity)
  Econst(@logic.Constant, Ity)
  EpureApp(@logic.LSymbol, ArrayView[PVariable], Ity)
  EroutineCall(RoutineSymbol, ArrayView[PVariable], Ity)
  Elet(PVariable, Expr, Expr, Ity)
  Eif(Expr, Expr, Expr, Ity)
  Eassert(@logic.Term)
  Eassume(@logic.Term)
}

///|
/// A compact ANF-like expression. Calls consume program variables, so
/// non-variable arguments are made explicit through Elet proxy binders just
/// as Why3 1.7.2 does in Dexpr/Expr.
struct Expr {
  node : ExprNode
  ity : Ity
  origin : @identity.Origin
  attributes : @identity.SemanticAttributes
  effect : Effect
  mask : ProgramMask
}

///|
fn make_expr(
  node : ExprNode,
  ity : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  effect : Effect,
) -> Expr {
  {
    node,
    ity,
    origin,
    attributes: @identity.SemanticAttributes::from_array(attributes),
    effect,
    mask: Visible,
  }
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
  )
}

///|
pub fn Expr::constant(
  constant : @logic.Constant,
  ity : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
) -> Expr {
  make_expr(
    ConstantExpr(constant),
    ity,
    origin,
    attributes,
    Effect::pure(false),
  )
}

///|
pub fn Expr::pure_application(
  symbol : @logic.LSymbol,
  arguments : ArrayView[PVariable],
  result : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  let arguments = arguments.to_owned()
  for argument in arguments {
    require_mlw_context(result.context_anchor(), argument.semantic_id(), span)
  }
  require_mlw_context(result.context_anchor(), symbol.semantic_id(), span)
  make_expr(
    PureApplicationExpr(symbol, arguments),
    result,
    origin,
    attributes,
    Effect::from_reads(arguments, true),
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
) -> Expr raise MlwError {
  let arguments = arguments.to_owned()
  for argument in arguments {
    require_mlw_context(result.context_anchor(), argument.semantic_id(), span)
  }
  require_mlw_context(result.context_anchor(), symbol.semantic_id(), span)
  let callee_effect = symbol.view().cty.view().effect
  make_expr(
    RoutineCallExpr(symbol, arguments),
    result,
    origin,
    attributes,
    Effect::from_reads(arguments, callee_effect.view().ghost).union(
      callee_effect,
    ),
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
  require_mlw_context(body.context_anchor(), binder.semantic_id(), span)
  require_mlw_context(body.context_anchor(), value.context_anchor(), span)
  if binder.view().ity != value.ity() {
    fail_mlw(
      InvalidProgramDeclaration,
      span,
      "let binder and value have different program types",
    )
  }
  make_expr(
    LetExpr(binder, value, body),
    body.ity(),
    origin,
    attributes,
    value.effect.union(body.effect.without(binder)),
  )
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
    fail_mlw(InvalidProgramDeclaration, span, "if condition is not boolean")
  }
  if consequent.ity() != alternative.ity() {
    fail_mlw(InvalidProgramDeclaration, span, "if branch types differ")
  }
  make_expr(
    IfExpr(condition, consequent, alternative),
    consequent.ity(),
    origin,
    attributes,
    condition.effect.union(consequent.effect).union(alternative.effect),
  )
}

///|
fn Expr::assertion(
  formula : @logic.Term,
  reads : ArrayView[PVariable],
  is_assumption : Bool,
  unit : Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Expr raise MlwError {
  if !formula.is_formula() {
    fail_mlw(InvalidProgramDeclaration, span, "assertion is not a formula")
  }
  make_expr(
    if is_assumption {
      AssumeExpr(formula)
    } else {
      AssertExpr(formula)
    },
    unit,
    origin,
    attributes,
    Effect::from_reads(reads, false),
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
  Expr::assertion(formula, reads, false, unit, origin, attributes, span)
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
  Expr::assertion(formula, reads, true, unit, origin, attributes, span)
}

///|
pub fn Expr::view(self : Expr) -> ExprView {
  match self.node {
    VariableExpr(variable) => Evar(variable, self.ity)
    ConstantExpr(constant) => Econst(constant, self.ity)
    PureApplicationExpr(symbol, arguments) =>
      EpureApp(symbol, arguments[:], self.ity)
    RoutineCallExpr(symbol, arguments) =>
      EroutineCall(symbol, arguments[:], self.ity)
    LetExpr(binder, value, body) => Elet(binder, value, body, self.ity)
    IfExpr(condition, consequent, alternative) =>
      Eif(condition, consequent, alternative, self.ity)
    AssertExpr(formula) => Eassert(formula)
    AssumeExpr(formula) => Eassume(formula)
  }
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
