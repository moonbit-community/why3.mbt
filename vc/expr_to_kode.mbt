// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
let control_attributes : Array[Bytes] = [
  b"vc:sp", b"vc:wp", b"vc:white_box", b"vc:keep_precondition", b"vc:divergent",
]

///|
fn is_control_attribute(attribute : BytesView) -> Bool {
  control_attributes.any(candidate => candidate[:] == attribute)
}

///|
fn ordinary_expression_attributes(
  expression : @mlw.Expr,
) -> Array[Bytes] raise VcError {
  for attribute in expression.attributes() {
    if is_control_attribute(attribute) {
      fail_vc(
        UnsupportedControlAttribute,
        expression.origin().source_span(),
        "VC control attributes are outside the classical MVP",
      )
    }
  }
  expression.attributes().to_owned()
}

///|
fn expression_span(expression : @mlw.Expr) -> @identity.SourceSpan? {
  expression.origin().source_span()
}

///|
fn make_program_variable(
  context : @identity.CompilationContext,
  name : BytesView,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
  ity : @mlw.Ity,
) -> @mlw.PVariable raise {
  @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(name, attributes, span),
    ity,
    false,
    span,
  )
}

///|
fn result_variable(
  context : @identity.CompilationContext,
  cty : @mlw.Cty,
  span : @identity.SourceSpan?,
) -> @mlw.PVariable raise {
  let cty_view = cty.view()
  if !cty_view.postconditions.is_empty() {
    let result = cty_view.postconditions[0].view().result.view()
    return make_program_variable(
      context,
      result.name,
      result.origin.attributes(),
      span,
      cty_view.result,
    )
  }
  make_program_variable(context, b"result", [], span, cty_view.result)
}

///|
fn proxy_variable(
  context : @identity.CompilationContext,
  expression : @mlw.Expr,
) -> @mlw.PVariable raise {
  make_program_variable(
    context,
    b"o",
    [proxy_attribute],
    expression_span(expression),
    expression.ity(),
  )
}

///|
fn traced_result_variable(
  context : @identity.CompilationContext,
  name : BytesView,
  expression : @mlw.Expr,
) -> @mlw.PVariable raise {
  make_program_variable(
    context,
    append_bytes(name, b"'result"),
    [b"model_trace:result"],
    expression_span(expression),
    expression.ity(),
  )
}

///|
fn tagged_expression_term(
  expression : @mlw.Expr,
  term : @logic.Term,
  attributes : ArrayView[Bytes],
) -> @logic.Term {
  term.source_decorate(expression_span(expression), attributes)
}

///|
fn pvariable_term(variable : @mlw.PVariable) -> @logic.Term {
  @logic.Term::variable(variable.view().pure_symbol)
}

///|
fn expression_application(
  environment : VcEnvironment,
  expression : @mlw.Expr,
  symbol : @logic.LSymbol,
  arguments : ArrayView[@mlw.PVariable],
  attributes : ArrayView[Bytes],
) -> @logic.Term raise {
  let applied = @logic.Term::elaborated_apply(
    symbol,
    [
      for argument in arguments => pvariable_term(argument)
    ],
    if symbol.view().result_type is Some(_) {
      Some(expression.ity().to_ty(expression_span(expression)))
    } else {
      None
    },
    None,
  )
  let value = if applied.is_formula() {
    @logic.Term::if_then_else(
      applied,
      environment.boolean_true,
      environment.boolean_false,
      None,
    )
  } else {
    applied
  }
  tagged_expression_term(expression, value, attributes)
}

///|
fn contract_substitution(
  formals : ArrayView[@mlw.PVariable],
  actuals : ArrayView[@mlw.PVariable],
  span : @identity.SourceSpan?,
) -> @logic.TermSubstitution raise {
  if formals.length() != actuals.length() {
    fail_vc(
      InvariantFailure,
      span,
      "routine call and computation type have different arities",
    )
  }
  let mut substitution = @logic.TermSubstitution::new()
  for index = 0; index < formals.length(); index = index + 1 {
    substitution = substitution.bind(
      formals[index].view().pure_symbol,
      pvariable_term(actuals[index]),
      span,
    )
  }
  substitution
}

///|
fn instantiate_preconditions(
  context : @identity.CompilationContext,
  substitution : @logic.TermSubstitution,
  preconditions : ArrayView[@logic.Term],
  span : @identity.SourceSpan?,
) -> Array[@logic.Term] raise {
  [
    for precondition in preconditions => {
      substitution.apply(context, precondition, span)
    }
  ]
}

///|
fn instantiate_postconditions(
  context : @identity.CompilationContext,
  substitution : @logic.TermSubstitution,
  postconditions : ArrayView[@mlw.Postcondition],
  result : @mlw.PVariable,
  span : @identity.SourceSpan?,
) -> Array[@logic.Term] raise {
  let formulas : Array[@logic.Term] = []
  for postcondition in postconditions {
    let view = postcondition.view()
    let formula = substitution.apply(context, view.formula, span)
    let opened = @logic.TermSubstitution::new()
      .bind(view.result, pvariable_term(result), span)
      .apply(context, formula, span)
    formulas.push(opened)
  }
  formulas
}

///|
fn premise_of_preconditions(
  preconditions : ArrayView[@logic.Term],
) -> @logic.Term raise {
  conjunction(
    [
      for precondition in preconditions => {
        push_stop(precondition, [], b"expl:precondition")
      }
    ],
  )
}

///|
fn goal_of_preconditions(
  preconditions : ArrayView[@logic.Term],
  attributes : ArrayView[Bytes],
) -> @logic.Term raise {
  asymmetric_conjunction(
    [
      for precondition in preconditions => {
        vc_explanation(precondition, attributes, b"expl:precondition")
      }
    ],
  )
}

///|
fn premise_of_postconditions(
  postconditions : ArrayView[@logic.Term],
  attributes : ArrayView[Bytes],
) -> @logic.Term raise {
  conjunction(
    [
      for postcondition in postconditions => {
        push_stop(postcondition, attributes, b"expl:postcondition")
      }
    ],
  )
}

///|
fn goal_of_postconditions(
  postconditions : ArrayView[@logic.Term],
) -> @logic.Term raise {
  asymmetric_conjunction(
    [
      for postcondition in postconditions => {
        vc_explanation(postcondition, [], b"expl:postcondition")
      }
    ],
  )
}

///|
fn simplified_conjunction_with_decoration(
  decoration : @logic.Term,
  left : @logic.Term,
  right : @logic.Term,
) -> @logic.Term raise {
  let combined = if is_true(left) {
    right
  } else if is_true(right) {
    left
  } else if is_false(left) || is_false(right) {
    @logic.Term::false_formula()
  } else {
    plain_and(left, right)
  }
  copy_term_decoration(decoration, combined)
}

///|
fn term_of_postcondition(
  environment : VcEnvironment,
  result : @logic.VSymbol,
  formula : @logic.Term,
) -> (@logic.Term, @logic.Term)? raise {
  match formula.view() {
    Tapp(symbol, _, arguments) if is_builtin_equality(symbol) &&
      arguments.length() == 2 &&
      arguments[0].view() is Tvar(variable) &&
      variable == result &&
      term_occurrences(arguments[1], result) == 0 =>
      Some((arguments[1], @logic.Term::true_formula()))
    Tbinop(Iff, left, right) if left.view() is Tapp(symbol, _, arguments) &&
      is_builtin_equality(symbol) &&
      arguments.length() == 2 &&
      arguments[0].view() is Tvar(variable) &&
      variable == result &&
      arguments[1] == environment.boolean_true &&
      term_occurrences(right, result) == 0 =>
      Some(
        (
          copy_term_decoration(
            right,
            @logic.Term::if_then_else(
              right,
              environment.boolean_true,
              environment.boolean_false,
              None,
            ),
          ),
          @logic.Term::true_formula(),
        ),
      )
    Tbinop(And, left, right) =>
      match term_of_postcondition(environment, result, left) {
        Some((value, residual)) =>
          Some(
            (
              value,
              simplified_conjunction_with_decoration(formula, residual, right),
            ),
          )
        None => None
      }
    _ => None
  }
}

///|
fn postcondition_kode(
  environment : VcEnvironment,
  context : @identity.CompilationContext,
  expression : @mlw.Expr,
  result : @mlw.PVariable,
  postcondition : @logic.Term,
  trace_name : BytesView,
  attributes : ArrayView[Bytes],
) -> Kode raise {
  let definition = match
    term_of_postcondition(environment, result.view().pure_symbol, postcondition) {
    Some((value, residual)) =>
      klet(
        result,
        tagged_expression_term(expression, value, attributes),
        residual,
      )
    None => kval([result], postcondition)
  }
  let trace = traced_result_variable(context, trace_name, expression)
  kseq(
    definition,
    0,
    klet(trace, pvariable_term(result), @logic.Term::true_formula()),
  )
}

///|
fn lower_expression(
  environment : VcEnvironment,
  expression : @mlw.Expr,
  result : @mlw.PVariable,
) -> Kode raise {
  let attributes = ordinary_expression_attributes(expression)
  match expression.view() {
    Evar(variable, _) =>
      klet(
        result,
        tagged_expression_term(expression, pvariable_term(variable), attributes),
        @logic.Term::true_formula(),
      )
    Econst(constant, ity) =>
      klet(
        result,
        tagged_expression_term(
          expression,
          @logic.Term::constant(
            constant,
            ity.to_ty(expression_span(expression)),
            None,
          ),
          attributes,
        ),
        @logic.Term::true_formula(),
      )
    EpureApp(symbol, arguments, _) => {
      let definition = klet(
        result,
        expression_application(
          environment, expression, symbol, arguments, attributes,
        ),
        @logic.Term::true_formula(),
      )
      let trace = traced_result_variable(
        environment.context,
        symbol.view().name,
        expression,
      )
      kseq(
        definition,
        0,
        klet(trace, pvariable_term(result), @logic.Term::true_formula()),
      )
    }
    EroutineCall(symbol, arguments, _) => {
      let cty = symbol.view().cty.view()
      let substitution = contract_substitution(
        cty.arguments,
        arguments,
        expression_span(expression),
      )
      let preconditions = instantiate_preconditions(
        environment.context,
        substitution,
        cty.preconditions,
        expression_span(expression),
      )
      let postconditions = instantiate_postconditions(
        environment.context,
        substitution,
        cty.postconditions,
        result,
        expression_span(expression),
      )
      let post = premise_of_postconditions(postconditions, attributes)
      let body = postcondition_kode(
        environment,
        environment.context,
        expression,
        result,
        post,
        symbol.view().name,
        attributes,
      )
      if preconditions.is_empty() {
        body
      } else {
        kpar(kstop(goal_of_preconditions(preconditions, attributes)), body)
      }
    }
    Elet(binder, value, body, _) =>
      kseq(
        lower_expression(environment, value, binder),
        0,
        lower_expression(environment, body, result),
      )
    Eif(condition, consequent, alternative, _) => {
      let branches = fn(variable) -> Kode raise {
        kif(
          variable,
          lower_expression(environment, consequent, result),
          lower_expression(environment, alternative, result),
        )
      }
      match condition.view() {
        Evar(variable, _) => branches(variable)
        _ => {
          let proxy = proxy_variable(environment.context, condition)
          kseq(
            lower_expression(environment, condition, proxy),
            0,
            branches(proxy),
          )
        }
      }
    }
    Eassert(formula) => {
      let annotated = vc_explanation(formula, attributes, b"expl:assertion")
      kseq(kcut(annotated), 0, kval([result], @logic.Term::true_formula()))
    }
    Eassume(formula) =>
      kval([result], vc_explanation(formula, attributes, b"expl:assumption"))
  }
}

///|
fn routine_kode(
  environment : VcEnvironment,
  cty : @mlw.Cty,
  body : @mlw.Expr,
) -> Kode raise {
  let result = result_variable(environment.context, cty, expression_span(body))
  let cty_view = cty.view()
  let postconditions = instantiate_postconditions(
    environment.context,
    @logic.TermSubstitution::new(),
    cty_view.postconditions,
    result,
    expression_span(body),
  )
  kseq(
    kval(cty_view.arguments, premise_of_preconditions(cty_view.preconditions)),
    0,
    kseq(
      lower_expression(environment, body, result),
      0,
      kstop(goal_of_postconditions(postconditions)),
    ),
  )
}
