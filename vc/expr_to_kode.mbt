// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
let control_attributes : Array[Bytes] = [
  b"vc:sp", b"vc:wp", b"vc:white_box", b"vc:keep_precondition", b"vc:divergent",
  b"vc:do_not_keep_trace",
]

///|
priv struct ExceptionContinuation {
  exception : @mlw.XSymbol
  index : Int
  payload : @mlw.PVariable
}

///|
fn find_exception_continuation(
  continuations : ArrayView[ExceptionContinuation],
  exception : @mlw.XSymbol,
) -> ExceptionContinuation? {
  for continuation in continuations {
    if continuation.exception == exception {
      return Some(continuation)
    }
  }
  None
}

///|
fn overlay_exception_continuation(
  continuations : ArrayView[ExceptionContinuation],
  replacement : ExceptionContinuation,
) -> Array[ExceptionContinuation] {
  let result = [
    for continuation in continuations if continuation.exception !=
    replacement.exception => continuation
  ]
  result.push(replacement)
  result
}

///|
fn is_control_attribute(attribute : BytesView) -> Bool {
  control_attributes.any(candidate => candidate[:] == attribute)
}

///|
fn ordinary_expression_attributes(expression : @mlw.Expr) -> Array[Bytes] {
  let attributes : Array[Bytes] = []
  for attribute in expression.attributes() {
    if !is_control_attribute(attribute) {
      attributes.push(attribute)
    }
  }
  attributes
}

///|
fn add_source_location_attribute(
  context : @identity.CompilationContext,
  attributes : ArrayView[Bytes],
  label : BytesView,
  span : @identity.SourceSpan?,
) -> Array[Bytes] {
  let result = attributes.to_owned()
  guard span is Some(span) else { return result }
  let view = span.view()
  let buffer = @buffer.Buffer()
  buffer.write_bytes(label)
  buffer.write_byte(b':')
  buffer.write_bytes(context.source_display_path(view.relative_path))
  buffer.write_byte(b':')
  buffer.write_string_utf8(view.start_line.to_string())
  buffer.write_byte(b':')
  buffer.write_string_utf8(view.start_column.to_string())
  buffer.write_byte(b':')
  buffer.write_string_utf8(view.end_line.to_string())
  buffer.write_byte(b':')
  buffer.write_string_utf8(view.end_column.to_string())
  let attribute = buffer.to_bytes()
  if !result.any(existing => existing == attribute) {
    result.push(attribute)
  }
  result
}

///|
fn prepend_typeinv_marker_checks(
  markers : ArrayView[@logic.Term],
  continuation : Kode,
) -> Kode raise {
  let mut result = continuation
  for index = markers.length() - 1; index >= 0; index = index - 1 {
    let marker = markers[index]
    result = kpar(
      kstop(vc_explanation(marker, [], b"expl:type invariant")),
      kseq(kval([], push_stop(marker, [], b"expl:type invariant")), 0, result),
    )
  }
  result
}

///|
fn prepend_typeinv_term_checks(
  environment : VcEnvironment,
  terms : ArrayView[@logic.Term],
  continuation : Kode,
) -> Kode raise {
  prepend_typeinv_marker_checks(
    typeinv_inspect_terms(environment, terms),
    continuation,
  )
}

///|
fn prepend_typeinv_value_checks(
  environment : VcEnvironment,
  values : ArrayView[@logic.Term],
  continuation : Kode,
) -> Kode raise {
  prepend_typeinv_marker_checks(
    typeinv_require_values(environment, values),
    continuation,
  )
}

///|
fn expression_span(expression : @mlw.Expr) -> @identity.SourceSpan? {
  expression.origin().source_span()
}

///|
fn expression_requests_divergence(expression : @mlw.Expr) -> Bool {
  expression.attributes().any(attribute => attribute == b"vc:divergent")
}

///|
fn expression_is_boolean_true(
  environment : VcEnvironment,
  expression : @mlw.Expr,
) -> Bool {
  guard expression.view() is Eexec(computation, _) else { return false }
  let symbol = match computation.view() {
    Capp(routine, arguments) if arguments.is_empty() =>
      match routine.view().logic {
        RLls(symbol) => symbol
        RLnone | RLpv(_) | RLlemma => return false
      }
    Cpur(symbol, arguments) if arguments.is_empty() => symbol
    Capp(_, _) | Cpur(_, _) | Cfun(_) | Cany => return false
  }
  environment.boolean_true.view() is Tapp(true_symbol, _, arguments) &&
  arguments.is_empty() &&
  symbol == true_symbol
}

///|
fn check_expression_divergence(
  environment : VcEnvironment,
  expression : @mlw.Expr,
  attributes : ArrayView[Bytes],
  continuation : Kode,
) -> Kode {
  if expression.effect().view().termination.diverges() && !environment.divergent {
    kpar(
      kstop(
        vc_explanation(
          @logic.Term::false_formula(),
          attributes,
          b"expl:termination",
        ),
      ),
      continuation,
    )
  } else {
    continuation
  }
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
    let result_span = match span {
      Some(_) => span
      None => result.origin.source_span()
    }
    return make_program_variable(
      context,
      result.name,
      result.origin.attributes(),
      result_span,
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
fn exception_payload_variable(
  environment : VcEnvironment,
  exception : @mlw.XSymbol,
  postconditions : ArrayView[@mlw.Postcondition],
  span : @identity.SourceSpan?,
) -> @mlw.PVariable raise {
  if !postconditions.is_empty() {
    let result = postconditions[0].view().result.view()
    let result_span = match span {
      Some(_) => span
      None => result.origin.source_span()
    }
    return make_program_variable(
      environment.context,
      result.name,
      result.origin.attributes(),
      result_span,
      exception.view().ity,
    )
  }
  let name = exception.view().name.view()
  make_program_variable(
    environment.context,
    append_bytes(name.name, b"'payload"),
    name.attributes,
    span,
    exception.view().ity,
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
  let applied = tagged_expression_term(expression, applied, attributes)
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
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  asymmetric_conjunction(
    [
      for precondition in preconditions => {
        vc_explanation(precondition, attributes, b"expl:precondition", span~)
      }
    ],
  )
}

///|
fn premise_of_postconditions(
  postconditions : ArrayView[@logic.Term],
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  conjunction(
    [
      for postcondition in postconditions => {
        push_stop(postcondition, attributes, b"expl:postcondition", span~)
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
fn goal_of_exceptional_postconditions(
  postconditions : ArrayView[@logic.Term],
) -> @logic.Term raise {
  asymmetric_conjunction(
    [
      for postcondition in postconditions => {
        vc_explanation(postcondition, [], b"expl:exceptional postcondition")
      }
    ],
  )
}

///|
fn premise_of_exceptional_postconditions(
  postconditions : ArrayView[@logic.Term],
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  conjunction(
    [
      for postcondition in postconditions => {
        push_stop(
          postcondition,
          attributes,
          b"expl:exceptional postcondition",
          span~,
        )
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
fn is_builtin_function_type(ty : @logic.Ty) -> Bool {
  guard ty.view() is TyApp(symbol, arguments) && arguments.length() == 2 else {
    return false
  }
  symbol
  .origin()
  .attributes()
  .any(attribute => attribute == b"why3:builtin:function-type")
}

///|
fn is_builtin_function_application(
  environment : VcEnvironment,
  symbol : @logic.LSymbol,
) -> Bool {
  match environment.higher_order_apply {
    Some(application) if application == symbol => true
    _ =>
      symbol
      .view()
      .origin
      .attributes()
      .any(attribute => attribute == b"why3:builtin:function-application")
  }
}

///|
fn function_postcondition_value(
  environment : VcEnvironment,
  result : @logic.VSymbol,
  formula : @logic.Term,
) -> @logic.Term? raise {
  guard is_builtin_function_type(result.ty()) &&
    formula.view()
    is Tquant(ForallQuantifier, binders, _, defining_formula) &&
    !binders.is_empty() else {
    return None
  }
  let (initial_head, value) = match defining_formula.view() {
    Tapp(symbol, _, [head, value]) if is_builtin_equality(symbol) =>
      (head, value)
    Tbinop(Iff, equality, value) =>
      match equality.view() {
        Tapp(symbol, _, [head, truth]) if is_builtin_equality(symbol) &&
          truth == environment.boolean_true =>
          (head, value)
        _ => return None
    }
    _ => return None
  }
  let mut head = initial_head
  if term_occurrences(value, result) != 0 {
    return None
  }
  for index = binders.length() - 1; index >= 0; index = index - 1 {
    guard head.view() is Tapp(application, _, [prefix, argument]) &&
      is_builtin_function_application(environment, application) &&
      argument.view() is Tvar(variable) &&
      variable == binders[index] else {
      return None
    }
    head = prefix
  }
  guard head.view() is Tvar(variable) && variable == result else {
    return None
  }
  Some(
    copy_term_decoration(
      formula,
      @logic.Term::epsilon(result, formula, formula.source_span()),
    ),
  )
}

///|
fn term_of_postcondition(
  environment : VcEnvironment,
  result : @logic.VSymbol,
  formula : @logic.Term,
  span : @identity.SourceSpan?,
) -> (@logic.Term, @logic.Term)? raise {
  match function_postcondition_value(environment, result, formula) {
    Some(value) => return Some((value, @logic.Term::true_formula()))
    None => ()
  }
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
      term_occurrences(right, result) == 0 => {
      let right = if right.source_span() is Some(_) {
        right
      } else {
        right.source_decorate(span, right.attributes())
      }
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
    }
    Tbinop(And, left, right) =>
      match term_of_postcondition(environment, result, left, span) {
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
  trace_result : Bool,
  attributes : ArrayView[Bytes],
) -> Kode raise {
  let definition = match
    term_of_postcondition(
      environment,
      result.view().pure_symbol,
      postcondition,
      expression_span(expression),
    ) {
    Some((value, residual)) =>
      klet(
        result,
        tagged_expression_term(expression, value, attributes),
        residual,
      )
    None => kval([result], postcondition)
  }
  if environment.keep_trace && trace_result {
    let trace = traced_result_variable(context, trace_name, expression)
    kseq(
      definition,
      0,
      klet(trace, pvariable_term(result), @logic.Term::true_formula()),
    )
  } else {
    definition
  }
}

///|
fn find_exceptional_postconditions(
  cty : @mlw.Cty,
  exception : @mlw.XSymbol,
) -> Array[@mlw.Postcondition] {
  for entry in cty.view().exceptional_postconditions {
    let view = entry.view()
    if view.exception == exception {
      return view.postconditions.to_owned()
    }
  }
  []
}

///|
fn append_exceptional_call_outcomes(
  environment : VcEnvironment,
  expression : @mlw.Expr,
  cty : @mlw.Cty,
  old_substitution : @logic.TermSubstitution,
  attributes : ArrayView[Bytes],
  continuations : ArrayView[ExceptionContinuation],
  initial : Kode,
  trace_result : Bool,
) -> Kode raise {
  let mut result = initial
  for exception in cty.view().effect.view().raises {
    guard find_exception_continuation(continuations, exception)
      is Some(continuation) else {
      continue
    }
    let postconditions = instantiate_postconditions(
      environment.context,
      old_substitution,
      find_exceptional_postconditions(cty, exception),
      continuation.payload,
      expression_span(expression),
    )
    let post = wp_and(
      value_type_invariant_premise(
        environment,
        pvariable_term(continuation.payload),
        attributes,
      ),
      premise_of_exceptional_postconditions(
        postconditions,
        attributes,
        expression_span(expression),
      ),
    )
    let outcome = postcondition_kode(
      environment,
      environment.context,
      expression,
      continuation.payload,
      post,
      exception.view().name.view().name,
      trace_result,
      attributes,
    )
    result = kpar(result, kseq(outcome, 0, kcont(continuation.index)))
  }
  result
}

///|
fn renew_old_snapshots(
  environment : VcEnvironment,
  snapshots : ArrayView[@mlw.OldSnapshot],
  span : @identity.SourceSpan?,
) -> (Array[@mlw.OldSnapshot], @logic.TermSubstitution) raise {
  let renewed : Array[@mlw.OldSnapshot] = []
  let mut substitution = @logic.TermSubstitution::new()
  for entry in snapshots {
    let view = entry.view()
    let snapshot = view.original.trusted_old_snapshot(environment.context, span)
    renewed.push(@mlw.OldSnapshot::new(snapshot, view.original, span))
    substitution = substitution.bind(
      view.snapshot.view().pure_symbol,
      pvariable_term(snapshot),
      span,
    )
  }
  (renewed, substitution)
}

///|
fn bind_old_snapshots(
  snapshots : ArrayView[@mlw.OldSnapshot],
  continuation : Kode,
) -> Kode {
  let mut result = continuation
  for index = snapshots.length() - 1; index >= 0; index = index - 1 {
    let view = snapshots[index].view()
    result = kseq(
      klet(
        view.snapshot,
        pvariable_term(view.original),
        @logic.Term::true_formula(),
      ),
      0,
      result,
    )
  }
  result
}

///|
fn lower_abstract_computation(
  environment : VcEnvironment,
  expression : @mlw.Expr,
  result : @mlw.PVariable,
  cty : @mlw.Cty,
  trace_name : BytesView,
  attributes : ArrayView[Bytes],
  continuations : ArrayView[ExceptionContinuation],
  trusted_type_invariants : Bool,
  trace_result : Bool,
  drop_first_precondition? : Bool = false,
  leading_precondition? : @logic.Term? = None,
  check_termination? : Bool = false,
  renew_oldies? : Bool = false,
) -> Kode raise {
  let cty_view = cty.view()
  let (old_snapshots, old_substitution) = if renew_oldies {
    renew_old_snapshots(
      environment,
      cty_view.oldies,
      expression_span(expression),
    )
  } else {
    (cty_view.oldies.to_owned(), @logic.TermSubstitution::new())
  }
  let source_preconditions = if drop_first_precondition &&
    !cty_view.preconditions.is_empty() {
    cty_view.preconditions[1:]
  } else {
    cty_view.preconditions
  }
  let preconditions = instantiate_preconditions(
    environment.context,
    @logic.TermSubstitution::new(),
    source_preconditions,
    expression_span(expression),
  )
  let postconditions = instantiate_postconditions(
    environment.context,
    old_substitution,
    cty_view.postconditions,
    result,
    expression_span(expression),
  )
  let post = wp_and(
    value_type_invariant_premise(
      environment,
      pvariable_term(result),
      attributes,
    ),
    premise_of_postconditions(
      postconditions,
      attributes,
      expression_span(expression),
    ),
  )
  let normal = postcondition_kode(
    environment,
    environment.context,
    expression,
    result,
    post,
    trace_name,
    trace_result,
    attributes,
  )
  let outcomes = append_exceptional_call_outcomes(
    environment, expression, cty, old_substitution, attributes, continuations, normal,
    trace_result,
  )
  let affected = [
    for variable in cty_view.effect.view().reads if cty_view.effect.affected(
      variable.view().ity,
    ) => variable
  ]
  let after_havoc = lower_havoc(
    environment,
    cty_view.effect.view().reads,
    effect_havoc_writes(cty_view.effect),
    if affected.is_empty() {
      []
    } else {
      [variables_type_invariant_premise(environment, affected)]
    },
    outcomes,
    expression_span(expression),
  )
  let body = bind_old_snapshots(old_snapshots, after_havoc)
  let body = if check_termination {
    check_expression_divergence(environment, expression, attributes, body)
  } else {
    body
  }
  let precondition_goal = goal_of_preconditions(
    preconditions,
    attributes,
    expression_span(expression),
  )
  let precondition_goal = match leading_precondition {
    Some(leading) => wp_and(leading, precondition_goal)
    None => precondition_goal
  }
  let checked = if preconditions.is_empty() && leading_precondition is None {
    body
  } else if expression
    .attributes()
    .any(attribute => attribute == b"vc:keep_precondition") {
    kseq(kcut(precondition_goal), 0, body)
  } else {
    kpar(kstop(precondition_goal), body)
  }
  if trusted_type_invariants {
    checked
  } else {
    prepend_typeinv_term_checks(
      environment,
      preconditions,
      prepend_typeinv_value_checks(
        environment,
        cty_view.effect.view().reads.map(pvariable_term),
        checked,
      ),
    )
  }
}

///|
fn white_box_formula(
  formulas : ArrayView[@logic.Term],
  attributes : ArrayView[Bytes],
  explanation : BytesView,
) -> @logic.Term raise {
  asymmetric_conjunction(
    formulas.map(formula => vc_explanation(formula, attributes, explanation)),
  )
}

///|
fn white_box_cut(
  environment : VcEnvironment,
  formulas : ArrayView[@logic.Term],
  attributes : ArrayView[Bytes],
  explanation : BytesView,
) -> Kode raise {
  let formula = white_box_formula(formulas, attributes, explanation)
  prepend_typeinv_term_checks(
    environment,
    [formula],
    if is_false(formula) {
      kstop(formula)
    } else {
      kcut(formula)
    },
  )
}

///|
fn lower_white_box(
  environment : VcEnvironment,
  expression : @mlw.Expr,
  body : @mlw.Expr,
  result : @mlw.PVariable,
  cty : @mlw.Cty,
  attributes : ArrayView[Bytes],
  continuations : ArrayView[ExceptionContinuation],
) -> Kode raise {
  let view = cty.view()
  let preconditions = instantiate_preconditions(
    environment.context,
    @logic.TermSubstitution::new(),
    view.preconditions,
    expression_span(expression),
  )
  let postconditions = instantiate_postconditions(
    environment.context,
    @logic.TermSubstitution::new(),
    view.postconditions,
    result,
    expression_span(expression),
  )
  let mut caught = continuations.to_owned()
  let handlers : Array[(Int, Kode)] = []
  for exception in body.effect().view().raises {
    let exceptional = find_exceptional_postconditions(cty, exception)
    let passes = expression.effect().view().raises.any(candidate => {
      candidate == exception
    })
    if passes {
      guard find_exception_continuation(continuations, exception) is Some(outer) else {
        continue
      }
      if exceptional.is_empty() {
        continue
      }
      let formulas = instantiate_postconditions(
        environment.context,
        @logic.TermSubstitution::new(),
        exceptional,
        outer.payload,
        expression_span(expression),
      )
      handlers.push(
        (
          outer.index,
          kseq(
            white_box_cut(
              environment, formulas, attributes, b"expl:exceptional postcondition",
            ),
            0,
            kcont(outer.index),
          ),
        ),
      )
    } else if !exceptional.is_empty() {
      let payload = exception_payload_variable(
        environment,
        exception,
        exceptional,
        expression_span(expression),
      )
      let index = environment.fresh_exception_index()
      caught = overlay_exception_continuation(caught, {
        exception,
        index,
        payload,
      })
      let formulas = instantiate_postconditions(
        environment.context,
        @logic.TermSubstitution::new(),
        exceptional,
        payload,
        expression_span(expression),
      )
      handlers.push(
        (
          index,
          kseq(
            white_box_cut(
              environment, formulas, attributes, b"expl:exceptional postcondition",
            ),
            0,
            kstop(
              vc_explanation(
                @logic.Term::false_formula(),
                attributes,
                b"expl:unreachable point",
              ),
            ),
          ),
        ),
      )
    }
  }
  let mut kode = kseq(
    lower_expression(environment, body, result, caught),
    0,
    white_box_cut(
      environment, postconditions, attributes, b"expl:postcondition",
    ),
  )
  for handler in handlers {
    kode = kseq(kode, handler.0, handler.1)
  }
  kode = bind_old_snapshots(view.oldies, kode)
  if expression_requests_divergence(body) {
    kode = check_expression_divergence(
      environment, expression, attributes, kode,
    )
  }
  if preconditions.is_empty() {
    kode
  } else {
    kseq(
      white_box_cut(
        environment, preconditions, attributes, b"expl:precondition",
      ),
      0,
      kode,
    )
  }
}

///|
fn exception_handler_payload(
  environment : VcEnvironment,
  exception : @mlw.XSymbol,
  variables : ArrayView[@mlw.PVariable],
  handler : Kode,
  span : @identity.SourceSpan?,
) -> (@mlw.PVariable, Kode) raise {
  match variables {
    [] =>
      (exception_payload_variable(environment, exception, [], span), handler)
    [variable] => (variable, handler)
    _ => {
      let payload = exception_payload_variable(environment, exception, [], span)
      let payload_type = exception.view().ity.to_ty(span)
      guard type_constructors(environment, payload_type) is [data_constructor] &&
        data_constructor.view().symbol.view().argument_types.length() ==
        variables.length() else {
        fail_vc(
          InvariantFailure,
          span,
          "tuple-shaped exception payload has no matching constructor",
        )
      }
      let pattern = @logic.Pattern::app(
        data_constructor.view().symbol,
        variables.map(variable => {
          @logic.Pattern::variable(variable.view().pure_symbol)
        }),
        payload_type,
        span,
      )
      (payload, kcase(payload, [(pattern, handler)]))
    }
  }
}

///|
fn add_havoc_write(
  writes : Array[VcHavocWrite],
  region : @mlw.Region,
  fields : ArrayView[@mlw.PVariable],
) -> Unit {
  for index = 0; index < writes.length(); index = index + 1 {
    if writes[index].region == region {
      let merged = writes[index].fields.copy()
      for field in fields {
        if !merged.any(candidate => candidate == field) {
          merged.push(field)
        }
      }
      writes[index] = { region, fields: merged }
      return
    }
  }
  writes.push({ region, fields: fields.to_owned() })
}

///|
fn effect_havoc_writes(effect : @mlw.Effect) -> Array[VcHavocWrite] {
  let result = []
  for write in effect.view().writes {
    let view = write.view()
    add_havoc_write(result, view.region, view.fields)
  }
  result
}

///|
fn havoc_write_for_region(
  writes : ArrayView[VcHavocWrite],
  region : @mlw.Region,
) -> VcHavocWrite? {
  for write in writes {
    if write.region == region {
      return Some(write)
    }
  }
  None
}

///|
fn havoc_affects_ity(writes : ArrayView[VcHavocWrite], ity : @mlw.Ity) -> Bool {
  ity
  .reachable_regions()
  .any(region => writes.any(write => write.region == region))
}

///|
fn havoc_projection(
  environment : VcEnvironment,
  owner : @logic.Term,
  field : @mlw.PVariable,
  field_ity : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let routine = environment.program_space.find_projection_by_field(field, span)
  guard routine.view().logic is RLls(projection) else {
    fail_vc(InvariantFailure, span, "program field lost its logical projection")
  }
  @logic.Term::elaborated_apply(
    projection,
    [owner],
    Some(field_ity.to_ty(span)),
    span,
  )
}

///|
fn fresh_havoc_symbol(
  environment : VcEnvironment,
  name : BytesView,
  ity : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> @logic.VSymbol raise {
  let ty = ity.to_ty(span)
  @logic.VSymbol::new(
    environment.context,
    name,
    @identity.Origin::generated(@identity.Wp, name, span, []),
    ty,
    span,
  )
}

///|
fn constructor_argument_ities(
  routine : @mlw.RoutineSymbol,
  owner : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> Array[@mlw.Ity] raise {
  let view = routine.view().cty.view()
  let substitution = @mlw.ItySubstitution::empty().match_ity(
    view.result,
    owner,
    span,
  )
  view.arguments.map(argument => {
    substitution.instantiate(argument.view().ity, span)
  })
}

///|
fn havoc_constructor_pattern(
  symbol : @logic.LSymbol,
  variables : ArrayView[@logic.VSymbol],
  owner_type : @logic.Ty,
  span : @identity.SourceSpan?,
) -> @logic.Pattern raise {
  @logic.Pattern::app(
    symbol,
    variables.map(@logic.Pattern::variable),
    owner_type,
    span,
  )
}

///|
fn havoc_wild_constructor_pattern(
  symbol : @logic.LSymbol,
  arguments : ArrayView[@mlw.Ity],
  owner_type : @logic.Ty,
  span : @identity.SourceSpan?,
) -> @logic.Pattern raise {
  @logic.Pattern::app(
    symbol,
    arguments.map(argument => @logic.Pattern::wild(argument.to_ty(span))),
    owner_type,
    span,
  )
}

///|
fn havoc_value_relation(
  environment : VcEnvironment,
  writes : ArrayView[VcHavocWrite],
  old_value : @logic.Term,
  new_value : @logic.Term,
  ity : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  if !havoc_affects_ity(writes, ity) {
    return @logic.Term::elaborated_apply(
      environment.equality,
      [new_value, old_value],
      None,
      span,
    )
  }
  let (symbol, direct_write) = match ity.view() {
    ItyReg(region) =>
      (region.view().symbol, havoc_write_for_region(writes, region))
    ItyApp(symbol, _, _) => (symbol, None)
    ItyVar(_) => return @logic.Term::true_formula()
  }
  let symbol_view = symbol.view()
  let fields = symbol_view.mutable_fields.to_owned() +
    symbol_view.immutable_fields.to_owned()
  let constructors = type_constructors(environment, ity.to_ty(span))
  if constructors.length() <= 1 && !fields.is_empty() {
    if direct_write is Some(write) && write.fields.is_empty() {
      return @logic.Term::true_formula()
    }
    let constraints = []
    for field in fields {
      if direct_write is Some(write) &&
        write.fields.any(written => written == field) {
        continue
      }
      let field_ity = ity.member_ity(field, span)
      constraints.push(
        havoc_value_relation(
          environment,
          writes,
          havoc_projection(environment, old_value, field, field_ity, span),
          havoc_projection(environment, new_value, field, field_ity, span),
          field_ity,
          span,
        ),
      )
    }
    return conjunction(constraints)
  }
  if constructors.is_empty() {
    return @logic.Term::true_formula()
  }
  let owner_type = ity.to_ty(span)
  let constructor_routines = constructors.map(data_constructor => {
    environment.program_space.find_routine_by_logic(
      data_constructor.view().symbol,
      span,
    )
  })
  let argument_ities = constructor_routines.map(routine => {
    constructor_argument_ities(routine, ity, span)
  })
  let outer_branches : Array[(@logic.Pattern, @logic.Term)] = []
  for constructor_index = 0
      constructor_index < constructors.length()
      constructor_index = constructor_index + 1 {
    let constructor_symbol = constructors[constructor_index].view().symbol
    let ities = argument_ities[constructor_index]
    let old_variables = ities.map(argument => {
      fresh_havoc_symbol(environment, b"old_field", argument, span)
    })
    let matching_old = havoc_constructor_pattern(
      constructor_symbol, old_variables, owner_type, span,
    )
    let inner_branches : Array[(@logic.Pattern, @logic.Term)] = []
    for candidate_index = 0
        candidate_index < constructors.length()
        candidate_index = candidate_index + 1 {
      let candidate = constructors[candidate_index].view().symbol
      let candidate_ities = argument_ities[candidate_index]
      if candidate_index == constructor_index {
        let new_variables = candidate_ities.map(argument => {
          fresh_havoc_symbol(environment, b"new_field", argument, span)
        })
        let relations = []
        for argument_index = 0
            argument_index < ities.length()
            argument_index = argument_index + 1 {
          relations.push(
            havoc_value_relation(
              environment,
              writes,
              @logic.Term::variable(old_variables[argument_index]),
              @logic.Term::variable(new_variables[argument_index]),
              ities[argument_index],
              span,
            ),
          )
        }
        inner_branches.push(
          (
            havoc_constructor_pattern(
              candidate, new_variables, owner_type, span,
            ),
            conjunction(relations),
          ),
        )
      } else {
        inner_branches.push(
          (
            havoc_wild_constructor_pattern(
              candidate, candidate_ities, owner_type, span,
            ),
            @logic.Term::false_formula(),
          ),
        )
      }
    }
    outer_branches.push(
      (matching_old, @logic.Term::case(new_value, inner_branches, span)),
    )
  }
  @logic.Term::case(old_value, outer_branches, span)
}

///|
fn lower_havoc(
  _environment : VcEnvironment,
  variables : ArrayView[@mlw.PVariable],
  writes : ArrayView[VcHavocWrite],
  additional_constraints : ArrayView[@logic.Term],
  continuation : Kode,
  span : @identity.SourceSpan?,
) -> Kode raise {
  let affected : Array[@mlw.PVariable] = []
  for variable in variables {
    if havoc_affects_ity(writes, variable.view().ity) &&
      !affected.any(candidate => candidate == variable) {
      affected.push(variable)
    }
  }
  if affected.is_empty() {
    if additional_constraints.is_empty() {
      return continuation
    }
    return kseq(kval([], conjunction(additional_constraints)), 0, continuation)
  }
  let tail = if additional_constraints.is_empty() {
    continuation
  } else {
    kseq(kval([], conjunction(additional_constraints)), 0, continuation)
  }
  kseq(khavoc(affected, writes, span), 0, tail)
}

///|
fn lower_assignment(
  environment : VcEnvironment,
  assignments : ArrayView[@mlw.Assignment],
  result : @mlw.PVariable,
  span : @identity.SourceSpan?,
) -> Kode raise {
  let regions : Array[@mlw.PVariable] = []
  let writes : Array[VcHavocWrite] = []
  let constraints : Array[@logic.Term] = []
  for assignment in assignments {
    let view = assignment.view()
    if !regions.any(region => region == view.region) {
      regions.push(view.region)
    }
    guard view.region.view().ity.view() is ItyReg(region) else {
      fail_vc(
        InvariantFailure,
        None,
        "assignment target is not backed by a mutable region",
      )
    }
    guard view.field.view().field is Some(field) else {
      fail_vc(
        InvariantFailure,
        None,
        "assignment projection lost its program field",
      )
    }
    add_havoc_write(writes, region, [field])
    guard view.field.view().logic is RLls(projection) else {
      fail_vc(
        InvariantFailure,
        None,
        "assignment field lost its logical projection",
      )
    }
    let selected = @logic.Term::elaborated_apply(
      projection,
      [pvariable_term(view.region)],
      Some(view.value.view().ity.to_ty(None)),
      None,
    )
    constraints.push(
      @logic.Term::elaborated_apply(
        environment.equality,
        [selected, pvariable_term(view.value)],
        None,
        None,
      ),
    )
  }
  lower_havoc(
    environment,
    regions,
    writes,
    constraints,
    kval([result], @logic.Term::true_formula()),
    span,
  )
}

///|
priv struct OldLoopSnapshot {
  snapshot : @mlw.PVariable
  original : @mlw.PVariable
}

///|
priv struct OldLoopVariant {
  old : @logic.Term
  current : @mlw.ProgramVariant
}

///|
priv struct OldLoopVariants {
  snapshots : Array[OldLoopSnapshot]
  variants : Array[OldLoopVariant]
}

///|
fn old_loop_variants(
  environment : VcEnvironment,
  variants : ArrayView[@mlw.ProgramVariant],
  candidates : ArrayView[@mlw.PVariable],
  span : @identity.SourceSpan?,
) -> OldLoopVariants raise {
  let snapshots : Array[OldLoopSnapshot] = []
  let mut substitution = @logic.TermSubstitution::new()
  for candidate in candidates {
    let view = candidate.view()
    if view.ity.is_pure() ||
      snapshots.any(entry => entry.original == candidate) ||
      !variants.any(variant => {
        variant.view().term
        .free_variables()
        .any(symbol => symbol == view.pure_symbol)
      }) {
      continue
    }
    let snapshot = candidate.trusted_old_snapshot(environment.context, span)
    snapshots.push({ snapshot, original: candidate })
    substitution = substitution.bind(
      view.pure_symbol,
      pvariable_term(snapshot),
      span,
    )
  }
  let old_variants = variants.map(variant => {
    let term = variant.view().term
    {
      old: if snapshots.is_empty() {
        term
      } else {
        substitution.apply(environment.context, term, span)
      },
      current: variant,
    }
  })
  { snapshots, variants: old_variants }
}

///|
fn simplified_or(
  left : @logic.Term,
  right : @logic.Term,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  if is_false(left) {
    right
  } else if is_false(right) {
    left
  } else if is_true(left) || is_true(right) {
    @logic.Term::true_formula()
  } else {
    @logic.Term::binary(Or, left, right, span)
  }
}

///|
fn algebraic_variant_decrease(
  environment : VcEnvironment,
  old : @logic.Term,
  current : @logic.Term,
  old_type : @logic.Ty,
  current_type : @logic.Ty,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let constructors = type_constructors(environment, old_type)
  if constructors.is_empty() {
    fail_vc(
      UnsupportedComputation,
      span,
      "termination variant type has no default order",
    )
  }
  let branches = constructors.map(data_constructor => {
    let symbol = data_constructor.view().symbol
    guard symbol.view().result_type is Some(formal_result) else {
      abort("data constructor lost its value result")
    }
    let substitution = @logic.TySubstitution::new().match_type(
      formal_result, old_type, span,
    )
    let reversed_patterns : Array[@logic.Pattern] = []
    let mut branch = @logic.Term::false_formula()
    let argument_types = symbol.view().argument_types
    for index = argument_types.length() - 1; index >= 0; index = index - 1 {
      let argument_type = argument_types[index]
      let argument_type = substitution.apply(argument_type, span)
      if argument_type == current_type {
        let variable = @logic.VSymbol::new(
          environment.context,
          b"f",
          @identity.Origin::generated(@identity.Wp, b"f", span, []),
          argument_type,
          span,
        )
        reversed_patterns.push(@logic.Pattern::variable(variable))
        branch = simplified_or(
          @logic.Term::elaborated_apply(
            environment.equality,
            [@logic.Term::variable(variable), current],
            None,
            span,
          ),
          branch,
          span,
        )
      } else {
        reversed_patterns.push(@logic.Pattern::wild(argument_type))
      }
    }
    let patterns : Array[@logic.Pattern] = []
    for index = reversed_patterns.length() - 1; index >= 0; index = index - 1 {
      patterns.push(reversed_patterns[index])
    }
    let branch = branch.source_decorate(
      current.source_span(),
      branch.attributes(),
    )
    (@logic.Pattern::app(symbol, patterns, old_type, span), branch)
  })
  copy_term_decoration(current, @logic.Term::case(old, branches, span))
}

///|
fn default_variant_decrease(
  environment : VcEnvironment,
  old : @logic.Term,
  current : @logic.Term,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  guard old.ty() is Some(old_type) && current.ty() is Some(current_type) else {
    abort("validated termination variant lost its value type")
  }
  if old_type == current_type && current_type.view() is TyApp(symbol, _) {
    if symbol.builtin_kind() is Some(BuiltinInteger) {
      let zero = @logic.Term::constant(
        @logic.Constant::integer(@literal.ILitUnk, BigInt::from_int(0)),
        current_type,
        span,
      )
      guard environment.integer_le is Some(integer_le) &&
        environment.integer_lt is Some(integer_lt) else {
        fail_vc(
          InvariantFailure,
          span,
          "integer variant requires the VC int.Int support theory",
        )
      }
      return copy_term_decoration(
        current,
        plain_and(
          @logic.Term::elaborated_apply(integer_le, [zero, old], None, span),
          @logic.Term::elaborated_apply(integer_lt, [current, old], None, span),
        ),
      )
    }
    if environment.pure_theory.range_projection(symbol) is Some(projection) {
      guard environment.integer_lt is Some(integer_lt) else {
        fail_vc(
          InvariantFailure,
          span,
          "range variant requires the VC int.Int support theory",
        )
      }
      let projected_current = @logic.Term::elaborated_apply(
        projection,
        [current],
        None,
        span,
      )
      let projected_old = @logic.Term::elaborated_apply(
        projection,
        [old],
        None,
        span,
      )
      return copy_term_decoration(
        current,
        @logic.Term::elaborated_apply(
          integer_lt,
          [projected_current, projected_old],
          None,
          span,
        ),
      )
    }
  }
  algebraic_variant_decrease(
    environment, old, current, old_type, current_type, span,
  )
}

///|
fn relation_closure(
  environment : VcEnvironment,
  relation : @logic.LSymbol,
  ty : @logic.Ty,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  guard environment.function_type is Some(function_type) &&
    environment.higher_order_apply is Some(application) &&
    environment.boolean_true.ty() is Some(boolean_type) else {
    fail_vc(
      InvariantFailure,
      span,
      "custom variant relation requires the VC WellFounded support theory",
    )
  }
  let unary_type = @logic.Ty::app(function_type, [ty, boolean_type], span)
  let binary_type = @logic.Ty::app(function_type, [ty, unary_type], span)
  let closure = @logic.VSymbol::new(
    environment.context,
    b"relation",
    @identity.Origin::generated(@identity.Wp, b"relation", span, []),
    binary_type,
    span,
  )
  let left = @logic.VSymbol::new(
    environment.context,
    b"x",
    @identity.Origin::generated(@identity.Wp, b"x", span, []),
    ty,
    span,
  )
  let right = @logic.VSymbol::new(
    environment.context,
    b"y",
    @identity.Origin::generated(@identity.Wp, b"y", span, []),
    ty,
    span,
  )
  let partial = @logic.Term::elaborated_apply(
    application,
    [@logic.Term::variable(closure), @logic.Term::variable(left)],
    Some(unary_type),
    span,
  )
  let applied = @logic.Term::elaborated_apply(
    application,
    [partial, @logic.Term::variable(right)],
    Some(boolean_type),
    span,
  )
  let applied_is_true = @logic.Term::elaborated_apply(
    environment.equality,
    [applied, environment.boolean_true],
    None,
    span,
  )
  let relation_formula = @logic.Term::elaborated_apply(
    relation,
    [@logic.Term::variable(left), @logic.Term::variable(right)],
    None,
    span,
  )
  @logic.Term::epsilon(
    closure,
    @logic.Term::quantify(
      ForallQuantifier,
      [left, right],
      [],
      @logic.Term::binary(Iff, applied_is_true, relation_formula, span),
      span,
    ),
    span,
  )
}

///|
fn custom_relation_decrease(
  environment : VcEnvironment,
  relation : @logic.LSymbol,
  old : @logic.Term,
  current : @logic.Term,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let decrease = @logic.Term::elaborated_apply(
    relation,
    [current, old],
    None,
    span,
  )
  if environment.pure_theory.proved_wf(relation) is Some((_, proof_symbol)) &&
    environment.well_founded is Some(well_founded) &&
    proof_symbol == well_founded {
    return copy_term_decoration(current, decrease)
  }
  guard old.ty() is Some(ty) && environment.accessibility is Some(accessibility) else {
    fail_vc(
      InvariantFailure,
      span,
      "unproved custom variant relation requires the VC WellFounded support theory",
    )
  }
  copy_term_decoration(
    current,
    plain_and(
      decrease,
      @logic.Term::elaborated_apply(
        accessibility,
        [relation_closure(environment, relation, ty, span), old],
        None,
        span,
      ),
    ),
  )
}

///|
fn find_recursive_target(
  environment : VcEnvironment,
  symbol : @mlw.RoutineSymbol,
) -> RecursiveVcTarget? {
  for target in environment.recursive_targets {
    if target.internal_symbol == symbol {
      return Some(target)
    }
  }
  None
}

///|
fn find_recursive_call_target(
  environment : VcEnvironment,
  symbol : @mlw.RoutineSymbol,
  cty : @mlw.Cty,
) -> (RecursiveVcTarget, Array[@logic.Term])? {
  guard cty.view().preconditions is [first, ..] &&
    first.view() is Tapp(decrease, _, variants) else {
    return None
  }
  for target in environment.recursive_targets {
    if target.decrease_symbol == decrease {
      return Some((target, variants.to_owned()))
    }
  }
  match find_recursive_target(environment, symbol) {
    Some(target) => Some((target, variants.to_owned()))
    None => None
  }
}

///|
fn recursive_variant_decrease_from(
  environment : VcEnvironment,
  old_variants : ArrayView[RecursiveEntryVariant],
  new_variants : ArrayView[(@logic.Term, @logic.LSymbol?)],
  index : Int,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  if index >= old_variants.length() {
    return if index >= new_variants.length() {
      @logic.Term::true_formula()
    } else {
      @logic.Term::false_formula()
    }
  }
  if index >= new_variants.length() {
    return @logic.Term::true_formula()
  }
  let old_variant = old_variants[index]
  let old = old_variant.initial
  let current = new_variants[index].0
  if old == current {
    return recursive_variant_decrease_from(
      environment,
      old_variants,
      new_variants,
      index + 1,
      span,
    )
  }
  let decrease = match (old_variant.relation, new_variants[index].1) {
    (Some(old_relation), Some(new_relation)) if old_relation == new_relation =>
      custom_relation_decrease(environment, new_relation, old, current, span)
    (None, None) => default_variant_decrease(environment, old, current, span)
    _ => @logic.Term::false_formula()
  }
  if index + 1 >= old_variants.length() {
    return copy_term_decoration(current, decrease)
  }
  let equal = @logic.Term::elaborated_apply(
    environment.equality,
    [old, current],
    None,
    span,
  )
  copy_term_decoration(
    current,
    @logic.Term::binary(
      Or,
      decrease,
      plain_and(
        equal,
        recursive_variant_decrease_from(
          environment,
          old_variants,
          new_variants,
          index + 1,
          span,
        ),
      ),
      span,
    ),
  )
}

///|
fn recursive_call_decrease(
  environment : VcEnvironment,
  target : RecursiveVcTarget,
  variant_terms : ArrayView[@logic.Term],
  span : @identity.SourceSpan?,
) -> @logic.Term? raise {
  if target.variants.length() != variant_terms.length() {
    return None
  }
  let variants : Array[(@logic.Term, @logic.LSymbol?)] = []
  for index, term in variant_terms {
    variants.push((term, target.variants[index].view().relation))
  }
  if target.entry_variants.is_empty() && variants.is_empty() {
    return None
  }
  Some(
    recursive_variant_decrease_from(
      environment,
      target.entry_variants,
      variants,
      0,
      span,
    ),
  )
}

///|
fn require_integer_loop_symbols(
  environment : VcEnvironment,
  span : @identity.SourceSpan?,
) -> (
  @logic.LSymbol,
  @logic.LSymbol,
  @logic.LSymbol,
  @logic.LSymbol,
  @logic.LSymbol,
  @logic.LSymbol,
) raise {
  guard environment.integer_le is Some(le) &&
    environment.integer_lt is Some(lt) &&
    environment.integer_ge is Some(ge) &&
    environment.integer_gt is Some(gt) &&
    environment.integer_plus is Some(plus) &&
    environment.integer_minus is Some(minus) else {
    fail_vc(
      InvariantFailure,
      span,
      "integer loop requires int.Int in the module use closure",
    )
  }
  (le, lt, ge, gt, plus, minus)
}

///|
fn integer_term_of_program_variable(
  environment : VcEnvironment,
  variable : @mlw.PVariable,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let value = pvariable_term(variable)
  let ty = variable.view().ity.to_ty(span)
  guard ty.view() is TyApp(symbol, _) else {
    fail_vc(UnsupportedComputation, span, "loop bound has a type-variable type")
  }
  if symbol.builtin_kind() is Some(BuiltinInteger) {
    return value
  }
  guard environment.pure_theory.range_projection(symbol) is Some(projection) else {
    fail_vc(
      UnsupportedComputation,
      span,
      "for-loop bound is neither int nor a registered range type",
    )
  }
  @logic.Term::elaborated_apply(projection, [value], None, span)
}

///|
fn integer_one(
  ty : @logic.Ty,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  @logic.Term::constant(
    @logic.Constant::integer(@literal.ILitUnk, BigInt::from_int(1)),
    ty,
    span,
  )
}

///|
fn apply_integer_binary(
  symbol : @logic.LSymbol,
  left : @logic.Term,
  right : @logic.Term,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  @logic.Term::elaborated_apply(
    symbol,
    [left, right],
    symbol.view().result_type,
    span,
  )
}

///|
fn substitute_loop_invariants(
  environment : VcEnvironment,
  invariants : ArrayView[@logic.Term],
  variable : @mlw.PVariable,
  replacement : @logic.Term,
  span : @identity.SourceSpan?,
) -> Array[@logic.Term] raise {
  let substitution = @logic.TermSubstitution::new().bind(
    variable.view().pure_symbol,
    replacement,
    span,
  )
  invariants.map(invariant => {
    substitution.apply(environment.context, invariant, span)
  })
}

///|
fn loop_variant_decrease(
  environment : VcEnvironment,
  variants : ArrayView[OldLoopVariant],
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  if variants.is_empty() {
    return @logic.Term::true_formula()
  }
  let first = variants[0]
  let view = first.current.view()
  let old = first.old
  let current = view.term
  let decrease = match view.relation {
    Some(relation) =>
      custom_relation_decrease(environment, relation, old, current, span)
    None => default_variant_decrease(environment, old, current, span)
  }
  if variants.length() == 1 {
    return decrease
  }
  let equal = @logic.Term::elaborated_apply(
    environment.equality,
    [old, current],
    None,
    span,
  )
  let remaining = []
  for index = 1; index < variants.length(); index = index + 1 {
    remaining.push(variants[index])
  }
  @logic.Term::binary(
    Or,
    decrease,
    plain_and(equal, loop_variant_decrease(environment, remaining, span)),
    span,
  )
}

///|
fn affected_loop_variables(effect : @mlw.Effect) -> Array[@mlw.PVariable] {
  let variables : Array[@mlw.PVariable] = []
  for variable in effect.view().reads {
    if effect.affected(variable.view().ity) {
      variables.push(variable)
    }
  }
  variables
}

///|
fn loop_invariant_premise(
  invariants : ArrayView[@logic.Term],
  attributes : ArrayView[Bytes],
  explanation : BytesView,
) -> @logic.Term raise {
  conjunction(
    [
      for invariant in invariants => {
        push_stop(invariant, attributes, explanation)
      }
    ],
  )
}

///|
fn loop_invariant_goal(
  invariants : ArrayView[@logic.Term],
  attributes : ArrayView[Bytes],
  explanation : BytesView,
) -> @logic.Term raise {
  asymmetric_conjunction(
    [
      for invariant in invariants => {
        vc_explanation(invariant, attributes, explanation)
      }
    ],
  )
}

///|
fn bind_old_loop_variants(
  snapshots : ArrayView[OldLoopSnapshot],
  continuation : Kode,
) -> Kode {
  let mut result = continuation
  for entry in snapshots {
    result = kseq(
      klet(
        entry.snapshot,
        pvariable_term(entry.original),
        @logic.Term::true_formula(),
      ),
      0,
      result,
    )
  }
  result
}

///|
fn bind_recursive_entry_variants(
  environment : VcEnvironment,
  continuation : Kode,
) -> Kode {
  let mut result = continuation
  for oldie in environment.current_variant_oldies {
    let view = oldie.view()
    result = kseq(
      klet(
        view.snapshot,
        pvariable_term(view.original),
        @logic.Term::true_formula(),
      ),
      0,
      result,
    )
  }
  result
}

///|
fn scan_kode_term_definition(
  environment : VcEnvironment,
  result : @mlw.PVariable,
  kode : Kode,
  bindings : Array[(@mlw.PVariable, @logic.Term?)],
) -> (
  Array[(@mlw.PVariable, @logic.Term?)],
  (@logic.Term, @logic.Term)?,
  Int,
  Kode,
)? raise {
  match kode.view() {
    Klet(variable, value, constraint) if variable == result =>
      Some((bindings, Some((value, constraint)), 0, kcont(0)))
    Klet(variable, value, _) => {
      let bindings = bindings.copy()
      bindings.push((variable, Some(value)))
      Some((bindings, None, 0, kode))
    }
    Kval(variables, _) => {
      let bindings = bindings.copy()
      guard environment.unit_value.ty() is Some(unit_type) else {
        abort("validated unit value is untyped")
      }
      for variable in variables {
        let value = if variable.view().ity.to_ty(None) == unit_type {
          Some(environment.unit_value)
        } else {
          None
        }
        bindings.push((variable, value))
      }
      Some((bindings, None, 0, kode))
    }
    Kcut(_) => Some((bindings, None, 0, kode))
    Kcont(index) => Some((bindings, None, index, kode))
    Kseq(first, index, second) => {
      guard scan_kode_term_definition(environment, result, first, bindings)
        is Some((bindings, definition, outcome, first)) else {
        return None
      }
      if index != outcome {
        return Some((bindings, definition, outcome, kseq(first, index, second)))
      }
      if definition is Some(_) {
        return None
      }
      guard scan_kode_term_definition(environment, result, second, bindings)
        is Some((bindings, definition, outcome, second)) else {
        return None
      }
      Some((bindings, definition, outcome, kseq(first, index, second)))
    }
    Koff(explanation, inner) =>
      match scan_kode_term_definition(environment, result, inner, bindings) {
        Some((bindings, definition, outcome, inner)) =>
          Some((bindings, definition, outcome, koff(explanation, inner)))
        None => None
      }
    Kmode(mode, inner) =>
      match scan_kode_term_definition(environment, result, inner, bindings) {
        Some((bindings, definition, outcome, inner)) =>
          Some((bindings, definition, outcome, kmode(mode, inner)))
        None => None
      }
    Kout(outcomes, inner) =>
      match scan_kode_term_definition(environment, result, inner, bindings) {
        Some((bindings, definition, outcome, inner)) =>
          Some((bindings, definition, outcome, kout(outcomes, inner)))
        None => None
      }
    Kpush(closed, inner) =>
      match scan_kode_term_definition(environment, result, inner, bindings) {
        Some((bindings, definition, outcome, inner)) =>
          Some((bindings, definition, outcome, kpush(closed, inner)))
        None => None
      }
    Kpar(left, right) =>
      match left.view() {
        Kstop(_) =>
          match
            scan_kode_term_definition(environment, result, right, bindings) {
            Some((bindings, definition, outcome, right)) =>
              Some((bindings, definition, outcome, kpar(left, right)))
            None => None
          }
        _ => None
      }
    Kif(_, _, _) | Kcase(_, _) | Khavoc(_, _, _) | Kstop(_) => None
  }
}

///|
fn unwind_kode_term_bindings(
  environment : VcEnvironment,
  bindings : ArrayView[(@mlw.PVariable, @logic.Term?)],
  term : @logic.Term,
) -> @logic.Term? raise {
  let mut result = term
  for reverse_index = 0
      reverse_index < bindings.length()
      reverse_index = reverse_index + 1 {
    let (variable, value) = bindings[bindings.length() - reverse_index - 1]
    let symbol = variable.view().pure_symbol
    match value {
      Some(value) =>
        result = let_simplified_symbol(
          environment.context,
          symbol,
          value,
          result,
          environment.keep_trace && relevant_for_counterexample(symbol),
        )
      None => if term_occurrences(result, symbol) > 0 { return None }
    }
  }
  Some(result)
}

///|
fn term_definition_of_kode(
  environment : VcEnvironment,
  result : @mlw.PVariable,
  kode : Kode,
) -> (@logic.Term, @logic.Term, Kode)? raise {
  guard scan_kode_term_definition(environment, result, kode, [])
    is Some((bindings, definition, 0, kode)) &&
    definition is Some((value, constraint)) else {
    return None
  }
  guard unwind_kode_term_bindings(environment, bindings, value) is Some(value) else {
    return None
  }
  let constraint = if constraint.free_variables().is_empty() {
    constraint
  } else {
    guard unwind_kode_term_bindings(environment, bindings, constraint)
      is Some(constraint) else {
      return None
    }
    constraint
  }
  Some((value, constraint, kode))
}

///|
fn lower_expression(
  environment : VcEnvironment,
  expression : @mlw.Expr,
  result : @mlw.PVariable,
  continuations : ArrayView[ExceptionContinuation],
) -> Kode raise {
  let attributes = ordinary_expression_attributes(expression)
  let kode = match expression.view() {
    Evar(variable) =>
      klet(
        result,
        tagged_expression_term(expression, pvariable_term(variable), attributes),
        @logic.Term::true_formula(),
      )
    Econst(constant) =>
      klet(
        result,
        tagged_expression_term(
          expression,
          @logic.Term::constant(
            constant,
            expression.ity().to_ty(expression_span(expression)),
            None,
          ),
          attributes,
        ),
        @logic.Term::true_formula(),
      )
    Eexec(computation, attached_cty) =>
      match computation.view() {
        Cpur(symbol, arguments) => {
          let applied = expression_application(
            environment, expression, symbol, arguments, attributes,
          )
          let definition = klet(result, applied, @logic.Term::true_formula())
          let fully_applied = attached_cty.view().arguments.is_empty()
          let trusted = typeinv_is_trusted_constructor(environment, symbol) ||
            typeinv_is_trusted_projection(
              environment,
              symbol,
              Some(expression.ity().to_ty(expression_span(expression))),
            )
          let trace_result = !fully_applied ||
            !(arguments.is_empty() || trusted)
          let definition = if environment.keep_trace && trace_result {
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
          } else {
            definition
          }
          prepend_typeinv_term_checks(environment, [applied], definition)
        }
        Capp(symbol, arguments) => {
          let recursive_call = find_recursive_call_target(
            environment, symbol, attached_cty,
          )
          let recursive_decrease = match recursive_call {
            Some((target, variants)) =>
              recursive_call_decrease(
                environment,
                target,
                variants,
                expression_span(expression),
              )
            None => None
          }
          let recursive = recursive_call is Some(_)
          let fully_applied = attached_cty.view().arguments.is_empty()
          let trusted_application = match symbol.view().logic {
            RLls(logic_symbol) =>
              typeinv_is_trusted_constructor(environment, logic_symbol) ||
              typeinv_is_trusted_projection(
                environment,
                logic_symbol,
                Some(expression.ity().to_ty(expression_span(expression))),
              )
            RLnone | RLlemma | RLpv(_) => false
          }
          let trusted_type_invariants = fully_applied && trusted_application
          let trace_result = match symbol.view().logic {
            RLls(_) =>
              !fully_applied || !(arguments.is_empty() || trusted_application)
            RLnone | RLlemma | RLpv(_) => true
          }
          let call = lower_abstract_computation(
            environment,
            expression,
            result,
            attached_cty,
            symbol.view().name,
            attributes,
            continuations,
            trusted_type_invariants,
            trace_result,
            drop_first_precondition=recursive,
            leading_precondition=recursive_decrease.map(decrease => {
              vc_explanation(
                decrease,
                attributes,
                b"expl:variant decrease",
                span=expression_span(expression),
              )
            }),
            check_termination=true,
            renew_oldies=recursive,
          )
          call
        }
        Cfun(function_body) =>
          if attached_cty.view().arguments.is_empty() &&
            expression
            .attributes()
            .any(attribute => attribute == b"vc:white_box") {
            lower_white_box(
              environment, expression, function_body, result, attached_cty, attributes,
              continuations,
            )
          } else {
            let call = lower_abstract_computation(
              environment,
              expression,
              result,
              attached_cty,
              b"anonymous",
              attributes,
              continuations,
              false,
              true,
              check_termination=expression_requests_divergence(function_body),
            )
            kpar(
              routine_kode(environment, computation.cty(), function_body),
              call,
            )
          }
        Cany => {
          let call = lower_abstract_computation(
            environment,
            expression,
            result,
            attached_cty,
            b"any",
            attributes,
            continuations,
            false,
            true,
            check_termination=true,
          )
          call
        }
      }
    Eassign(assignments) =>
      lower_assignment(
        environment,
        assignments,
        result,
        expression_span(expression),
      )
    Elet(definition, body) =>
      match definition.view() {
        LDvar(binder, value) =>
          kseq(
            lower_expression(environment, value, binder, continuations),
            0,
            lower_expression(environment, body, result, continuations),
          )
        LDsym(symbol, computation) => {
          let continuation = lower_expression(
            environment, body, result, continuations,
          )
          let continuation = match symbol.view().logic {
            RLpv(variable) =>
              kseq(
                kval([variable], @logic.Term::true_formula()),
                0,
                continuation,
              )
            RLnone | RLls(_) | RLlemma => continuation
          }
          match computation.view() {
            Cfun(function_body) =>
              kpar(
                lower_havoc(
                  environment,
                  body.effect().view().reads,
                  effect_havoc_writes(body.effect()),
                  [],
                  routine_kode(environment, computation.cty(), function_body),
                  expression_span(body),
                ),
                continuation,
              )
            Capp(_, _) | Cpur(_, _) | Cany => continuation
          }
        }
        LDrec(definitions) => {
          let mut continuation = lower_expression(
            environment, body, result, continuations,
          )
          let function_variables = []
          let recursive_context = environment.recursive_context()
          for definition in definitions {
            let view = definition.view()
            if view.symbol.view().logic is RLpv(variable) {
              function_variables.push(variable)
            }
            if view.function_.view() is Cfun(function_body) {
              environment.restore_recursive_context(recursive_context)
              environment.configure_recursive_context(definitions, definition)
              continuation = kpar(
                lower_havoc(
                  environment,
                  body.effect().view().reads,
                  effect_havoc_writes(body.effect()),
                  [],
                  routine_kode(environment, view.function_.cty(), function_body),
                  expression_span(body),
                ),
                continuation,
              )
            }
          }
          environment.restore_recursive_context(recursive_context)
          if function_variables.is_empty() {
            continuation
          } else {
            kseq(
              kval(function_variables, @logic.Term::true_formula()),
              0,
              continuation,
            )
          }
        }
      }
    Eif(condition, consequent, alternative) => {
      let branches = fn(variable) -> Kode raise {
        let pure_branches = consequent.effect().is_pure() &&
          alternative.effect().is_pure()
        let consequent_kode = lower_expression(
          environment, consequent, result, continuations,
        )
        let alternative_kode = lower_expression(
          environment, alternative, result, continuations,
        )
        let conditional = kif(variable, consequent_kode, alternative_kode)
        if pure_branches {
          guard expression.ity().to_ty(None) ==
            environment.boolean_true.ty().unwrap() &&
            !expression.ity().is_fragile() &&
            term_definition_of_kode(environment, result, consequent_kode)
            is Some(
              (consequent_value, consequent_constraint, simplified_consequent)
            ) &&
            term_definition_of_kode(environment, result, alternative_kode)
            is Some(
              (alternative_value, alternative_constraint, simplified_alternative
              )
            ) else {
            return kmode(EfficientSp, conditional)
          }
          let condition_formula = environment.boolean_test(variable)
          let value = if_simplified(
            condition_formula, consequent_value, alternative_value,
          )
          let constraint = pure_sp_if(
            condition_formula, consequent_constraint, alternative_constraint,
          )
          let decoration = @logic.Term::true_formula().source_decorate(
            expression_span(expression),
            [],
          )
          kseq(
            kmode(
              EfficientSp,
              kif(variable, simplified_consequent, simplified_alternative),
            ),
            0,
            klet(
              result,
              copy_term_decoration(decoration, value),
              copy_term_decoration(decoration, constraint),
            ),
          )
        } else {
          conditional
        }
      }
      match condition.view() {
        Evar(variable) => branches(variable)
        _ => {
          let proxy = proxy_variable(environment.context, condition)
          kseq(
            lower_expression(environment, condition, proxy, continuations),
            0,
            branches(proxy),
          )
        }
      }
    }
    Ematch(scrutinee, regular, exceptional) => {
      let handlers : Array[(Int, Kode)] = []
      let mut caught = continuations.to_owned()
      for branch in exceptional {
        let view = branch.view()
        let handler = lower_expression(
          environment,
          view.body,
          result,
          continuations,
        )
        let (payload, handler) = exception_handler_payload(
          environment,
          view.exception,
          view.variables,
          handler,
          expression_span(view.body),
        )
        let continuation = {
          exception: view.exception,
          index: environment.fresh_exception_index(),
          payload,
        }
        handlers.push((continuation.index, handler))
        caught = overlay_exception_continuation(caught, continuation)
      }
      let regular_kode = if regular.is_empty() {
        lower_expression(environment, scrutinee, result, caught)
      } else {
        let branches = regular.map(branch => {
          let view = branch.view()
          (
            view.pattern.view().pattern,
            lower_expression(environment, view.body, result, continuations),
          )
        })
        let branches_kode = fn(variable) {
          let case_ = kcase(variable, branches)
          if regular.all(branch => branch.view().body.effect().is_pure()) {
            kmode(EfficientSp, case_)
          } else {
            case_
          }
        }
        match scrutinee.view() {
          Evar(variable) => branches_kode(variable)
          _ => {
            let proxy = proxy_variable(environment.context, scrutinee)
            kseq(
              lower_expression(environment, scrutinee, proxy, caught),
              0,
              branches_kode(proxy),
            )
          }
        }
      }
      let mut kode = regular_kode
      for handler in handlers {
        kode = kseq(kode, handler.0, handler.1)
      }
      kode
    }
    Eraise(exception, payload) => {
      guard find_exception_continuation(continuations, exception)
        is Some(continuation) else {
        fail_vc(
          InvariantFailure,
          expression_span(expression),
          "raised exception has no enclosing continuation",
        )
      }
      kseq(
        lower_expression(
          environment,
          payload,
          continuation.payload,
          continuations,
        ),
        0,
        kcont(continuation.index),
      )
    }
    Eexn(_, body) => lower_expression(environment, body, result, continuations)
    Eassert(Assert, formula) => {
      let annotated = vc_explanation(formula, attributes, b"expl:assertion")
      prepend_typeinv_term_checks(
        environment,
        [formula],
        kseq(kcut(annotated), 0, kval([result], @logic.Term::true_formula())),
      )
    }
    Eassert(Check, formula) => {
      let annotated = vc_explanation(formula, attributes, b"expl:check")
      prepend_typeinv_term_checks(
        environment,
        [formula],
        kpar(kstop(annotated), kval([result], @logic.Term::true_formula())),
      )
    }
    Eassert(Assume, formula) =>
      prepend_typeinv_term_checks(
        environment,
        [formula],
        kval([result], vc_explanation(formula, attributes, b"expl:assumption")),
      )
    Eghost(body) => lower_expression(environment, body, result, continuations)
    Epure(term) => {
      let value = if term.is_value() {
        term
      } else {
        @logic.Term::if_then_else(
          term,
          environment.boolean_true,
          environment.boolean_false,
          None,
        )
      }
      prepend_typeinv_term_checks(
        environment,
        [value],
        klet(
          result,
          tagged_expression_term(expression, value, attributes),
          @logic.Term::true_formula(),
        ),
      )
    }
    Eabsurd =>
      kstop(
        vc_explanation(
          @logic.Term::false_formula(),
          attributes,
          b"expl:unreachable point",
          span=expression_span(expression),
        ),
      )
    Ewhile(condition, invariants, variants, loop_body) => {
      let span = expression_span(expression)
      let variant_span = if variants.is_empty() {
        span
      } else {
        match variants[0].view().term.source_span() {
          Some(source) => Some(source)
          None => span
        }
      }
      let loop_attributes = add_source_location_attribute(
        environment.context,
        attributes,
        b"loop",
        span,
      )
      let old_variants = old_loop_variants(
        environment,
        variants,
        expression.effect().view().reads,
        span,
      )
      let invariant_terms = invariants.to_owned()
      for variant in variants {
        invariant_terms.push(variant.view().term)
      }
      let invariant_markers = typeinv_inspect_terms(
        environment, invariant_terms,
      )
      let invariant_marker_premise = conjunction(
        invariant_markers.map(marker => {
          push_stop(marker, loop_attributes, b"expl:type invariant")
        }),
      )
      let init = loop_invariant_goal(
        invariants, loop_attributes, b"expl:loop invariant init",
      )
      let premise = loop_invariant_premise(
        invariants, loop_attributes, b"expl:loop invariant init",
      )
      let keep = wp_and(
        vc_explanation(
          loop_variant_decrease(
            environment,
            old_variants.variants,
            variant_span,
          ),
          loop_attributes,
          b"expl:loop variant decrease",
          span=variant_span,
        ),
        loop_invariant_goal(
          invariants, loop_attributes, b"expl:loop invariant preservation",
        ),
      )
      let iteration = kseq(
        lower_expression(environment, loop_body, result, continuations),
        0,
        prepend_typeinv_marker_checks(invariant_markers, kstop(keep)),
      )
      let branch = if expression_is_boolean_true(environment, condition) {
        iteration
      } else {
        match condition.view() {
          Evar(variable) =>
            kif(
              variable,
              iteration,
              kval([result], @logic.Term::true_formula()),
            )
          _ => {
            let proxy = proxy_variable(environment.context, condition)
            kseq(
              lower_expression(environment, condition, proxy, continuations),
              0,
              kif(proxy, iteration, kval([result], @logic.Term::true_formula())),
            )
          }
        }
      }
      let preservation = lower_havoc(
        environment,
        expression.effect().view().reads,
        effect_havoc_writes(expression.effect()),
        [wp_and(invariant_marker_premise, premise)],
        bind_old_loop_variants(old_variants.snapshots, branch),
        span,
      )
      check_expression_divergence(
        environment,
        expression,
        loop_attributes,
        kpar(
          prepend_typeinv_marker_checks(invariant_markers, kstop(init)),
          preservation,
        ),
      )
    }
    Efor(index, bounds, internal, invariants, loop_body) => {
      let span = expression_span(expression)
      let loop_attributes = add_source_location_attribute(
        environment.context,
        attributes,
        b"loop",
        span,
      )
      let invariant_markers = typeinv_inspect_terms(environment, invariants)
      let invariant_marker_premise = conjunction(
        invariant_markers.map(marker => {
          push_stop(marker, loop_attributes, b"expl:type invariant")
        }),
      )
      let integer_symbols = require_integer_loop_symbols(environment, span)
      let bound_view = bounds.view()
      let first = integer_term_of_program_variable(
        environment,
        bound_view.first,
        span,
      )
      let last = integer_term_of_program_variable(
        environment,
        bound_view.last,
        span,
      )
      let current = pvariable_term(internal)
      guard current.ty() is Some(integer_type) else {
        abort("for-loop internal index lost its value type")
      }
      let one = integer_one(integer_type, span)
      let (inside, outside, step) = match bound_view.direction {
        To => (integer_symbols.0, integer_symbols.3, integer_symbols.4)
        DownTo => (integer_symbols.2, integer_symbols.1, integer_symbols.5)
      }
      let next = apply_integer_binary(step, current, one, span)
      let past_last = apply_integer_binary(step, last, one, span)
      let bounds_formula = plain_and(
        apply_integer_binary(inside, first, current, span),
        apply_integer_binary(inside, current, last, span),
      )
      let init_invariants = substitute_loop_invariants(
        environment, invariants, internal, first, span,
      )
      let next_invariants = substitute_loop_invariants(
        environment, invariants, internal, next, span,
      )
      let exit_invariants = substitute_loop_invariants(
        environment, invariants, internal, past_last, span,
      )
      let init = loop_invariant_goal(
        init_invariants, loop_attributes, b"expl:loop invariant init",
      )
      let premise = loop_invariant_premise(
        invariants, loop_attributes, b"expl:loop invariant init",
      )
      let keep = loop_invariant_goal(
        next_invariants, loop_attributes, b"expl:loop invariant preservation",
      )
      let iteration = kseq(
        lower_expression(environment, loop_body, result, continuations),
        0,
        prepend_typeinv_marker_checks(invariant_markers, kstop(keep)),
      )
      let indexed_iteration = if index == internal {
        kseq(kval([index], plain_and(bounds_formula, premise)), 0, iteration)
      } else {
        kseq(
          kval([index], @logic.Term::true_formula()),
          0,
          kseq(
            klet(
              internal,
              integer_term_of_program_variable(environment, index, span),
              plain_and(bounds_formula, premise),
            ),
            0,
            iteration,
          ),
        )
      }
      let exit = kval(
        [result],
        loop_invariant_premise(
          exit_invariants, loop_attributes, b"expl:loop invariant init",
        ),
      )
      let preservation = kpar(indexed_iteration, exit)
      let affected = [
        for variable in affected_loop_variables(expression.effect()) if variable !=
        index &&
        variable != internal => variable
      ]
      let preservation = lower_havoc(
        environment,
        affected,
        effect_havoc_writes(expression.effect()),
        if invariant_markers.is_empty() {
          []
        } else {
          [invariant_marker_premise]
        },
        preservation,
        span,
      )
      let core = kpar(
        prepend_typeinv_marker_checks(invariant_markers, kstop(init)),
        preservation,
      )
      check_expression_divergence(
        environment,
        expression,
        loop_attributes,
        kpar(
          kseq(
            kval(
              [],
              vc_explanation(
                apply_integer_binary(inside, first, past_last, span),
                loop_attributes,
                b"expl:loop bounds",
                span~,
              ),
            ),
            0,
            core,
          ),
          kseq(
            kval(
              [result],
              vc_explanation(
                apply_integer_binary(outside, first, past_last, span),
                loop_attributes,
                b"expl:loop bounds",
                span~,
              ),
            ),
            0,
            koff(b"expl:out of loop bounds", kcont(0)),
          ),
        ),
      )
    }
  }
  if expression.attributes().any(attribute => attribute == b"vc:sp") {
    kmode(EfficientSp, kode)
  } else if expression.attributes().any(attribute => attribute == b"vc:wp") {
    kmode(ClassicalWp, kode)
  } else {
    kode
  }
}

///|
fn routine_exception_continuations(
  environment : VcEnvironment,
  cty : @mlw.Cty,
  body : @mlw.Expr,
) -> Array[ExceptionContinuation] raise {
  let result = []
  for exception in body.effect().view().raises {
    let postconditions = find_exceptional_postconditions(cty, exception)
    result.push({
      exception,
      index: environment.fresh_exception_index(),
      payload: exception_payload_variable(
        environment,
        exception,
        postconditions,
        expression_span(body),
      ),
    })
  }
  result
}

///|
fn routine_exceptional_goal(
  environment : VcEnvironment,
  cty : @mlw.Cty,
  continuation : ExceptionContinuation,
  body : @mlw.Expr,
) -> @logic.Term raise {
  goal_of_exceptional_postconditions(
    instantiate_postconditions(
      environment.context,
      @logic.TermSubstitution::new(),
      find_exceptional_postconditions(cty, continuation.exception),
      continuation.payload,
      expression_span(body),
    ),
  )
}

///|
fn routine_affected_variables(cty : @mlw.Cty) -> Array[@mlw.PVariable] {
  let view = cty.view()
  let result = []
  let candidates = view.arguments.to_owned() +
    view.effect.view().reads.to_owned()
  for variable in candidates {
    if view.effect.affected(variable.view().ity) &&
      !result.any(existing => existing == variable) {
      result.push(variable)
    }
  }
  result
}

///|
fn routine_kode(
  environment : VcEnvironment,
  cty : @mlw.Cty,
  body : @mlw.Expr,
) -> Kode raise {
  let outer_divergent = environment.divergent
  environment.divergent = outer_divergent ||
    expression_requests_divergence(body)
  let result = result_variable(environment.context, cty, expression_span(body))
  let cty_view = cty.view()
  let postconditions = instantiate_postconditions(
    environment.context,
    @logic.TermSubstitution::new(),
    cty_view.postconditions,
    result,
    expression_span(body),
  )
  let continuations = routine_exception_continuations(environment, cty, body)
  let affected = routine_affected_variables(cty)
  let normal_values = [pvariable_term(result)]
  for variable in affected {
    normal_values.push(pvariable_term(variable))
  }
  let mut execution = kseq(
    lower_expression(environment, body, result, continuations),
    0,
    prepend_typeinv_value_checks(
      environment,
      normal_values,
      kstop(goal_of_postconditions(postconditions)),
    ),
  )
  for continuation in continuations {
    let exceptional_values = [pvariable_term(continuation.payload)]
    for variable in affected {
      exceptional_values.push(pvariable_term(variable))
    }
    execution = kseq(
      execution,
      continuation.index,
      prepend_typeinv_value_checks(
        environment,
        exceptional_values,
        kstop(routine_exceptional_goal(environment, cty, continuation, body)),
      ),
    )
  }
  let kode = kseq(
    kval(
      cty_view.arguments,
      wp_and(
        variables_type_invariant_premise(environment, cty_view.arguments),
        premise_of_preconditions(cty_view.preconditions),
      ),
    ),
    0,
    bind_recursive_entry_variants(
      environment,
      bind_old_snapshots(cty_view.oldies, execution),
    ),
  )
  environment.divergent = outer_divergent
  kode
}
