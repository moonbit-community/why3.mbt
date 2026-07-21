// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
let asym_split_attribute : Bytes = b"asym_split"

///|
let case_split_attribute : Bytes = b"case_split"

///|
let stop_split_attribute : Bytes = b"stop_split"

///|
let annotation_attribute : Bytes = b"vc:annotation"

///|
let proxy_attribute : Bytes = b"mlw:proxy_symbol"

///|
fn bytes_have_prefix(value : BytesView, prefix : BytesView) -> Bool {
  value.length() >= prefix.length() && value[:prefix.length()] == prefix
}

///|
fn append_bytes(left : BytesView, right : BytesView) -> Bytes {
  let buffer = @buffer.Buffer(size_hint=left.length() + right.length())
  buffer.write_bytes(left)
  buffer.write_bytes(right)
  buffer.to_bytes()
}

///|
fn merged_attributes(
  left : ArrayView[Bytes],
  right : ArrayView[Bytes],
) -> Array[Bytes] {
  let result = left.to_owned()
  for attribute in right {
    result.push(attribute)
  }
  result
}

///|
fn copy_term_decoration(
  source : @logic.Term,
  replacement : @logic.Term,
) -> @logic.Term {
  let attributes = merged_attributes(
    source.attributes(),
    replacement.attributes(),
  )
  let span = match replacement.source_span() {
    Some(span) => Some(span)
    None => source.source_span()
  }
  let result = replacement.source_decorate(span, attributes)
  match replacement.origin() {
    Some(origin) => result.decorate(origin, attributes)
    None =>
      match source.origin() {
        Some(origin) => result.decorate(origin, attributes)
        None => result
      }
  }
}

///|
fn is_true(term : @logic.Term) -> Bool {
  term.view() is Ttrue
}

///|
fn is_false(term : @logic.Term) -> Bool {
  term.view() is Tfalse
}

///|
fn can_simplify_true(term : @logic.Term) -> Bool {
  is_true(term) &&
  !term.attributes().any(attribute => attribute == annotation_attribute)
}

///|
fn has_explanation(attributes : ArrayView[Bytes]) -> Bool {
  attributes.any(attribute => bytes_have_prefix(attribute, b"expl:"))
}

///|
fn vc_explanation(
  term : @logic.Term,
  attributes : ArrayView[Bytes],
  explanation : BytesView,
) -> @logic.Term {
  let additions = attributes.to_owned()
  additions.push(stop_split_attribute)
  additions.push(annotation_attribute)
  if !has_explanation(merged_attributes(term.attributes(), additions)) {
    additions.push(explanation.to_owned())
  }
  term.add_attributes(additions)
}

///|
fn plain_and(left : @logic.Term, right : @logic.Term) -> @logic.Term raise {
  @logic.Term::binary(And, left, right, None)
}

///|
fn asymmetric_and(left : @logic.Term, right : @logic.Term) -> @logic.Term raise {
  plain_and(left.add_attributes([asym_split_attribute]), right)
}

///|
fn conjunction(terms : ArrayView[@logic.Term]) -> @logic.Term raise {
  if terms.is_empty() {
    return @logic.Term::true_formula()
  }
  let mut result = terms[terms.length() - 1]
  for index = terms.length() - 2; index >= 0; index = index - 1 {
    result = plain_and(terms[index], result)
  }
  result
}

///|
fn asymmetric_conjunction(terms : ArrayView[@logic.Term]) -> @logic.Term raise {
  if terms.is_empty() {
    return @logic.Term::true_formula()
  }
  let mut result = terms[terms.length() - 1]
  for index = terms.length() - 2; index >= 0; index = index - 1 {
    result = asymmetric_and(terms[index], result)
  }
  result
}

///|
fn push_stop(
  formula : @logic.Term,
  attributes : ArrayView[Bytes],
  explanation : BytesView,
) -> @logic.Term raise {
  match formula.view() {
    Tbinop(And, left, right) if !formula
      .attributes()
      .any(attribute => attribute == annotation_attribute) =>
      copy_term_decoration(
        formula,
        plain_and(
          push_stop(left, attributes, explanation),
          push_stop(right, attributes, explanation),
        ),
      )
    _ => vc_explanation(formula, attributes, explanation)
  }
}

///|
fn sp_implies(
  premise : @logic.Term,
  consequence : @logic.Term,
) -> @logic.Term raise {
  if is_true(premise) || is_true(consequence) {
    consequence
  } else {
    @logic.Term::binary(Implies, premise, consequence, None)
  }
}

///|
fn wp_and(left : @logic.Term, right : @logic.Term) -> @logic.Term raise {
  if can_simplify_true(left) {
    right
  } else if can_simplify_true(right) {
    left
  } else {
    plain_and(left, right)
  }
}

///|
fn wp_and_asymmetric(
  left : @logic.Term,
  right : @logic.Term,
) -> @logic.Term raise {
  if can_simplify_true(left) {
    right
  } else if can_simplify_true(right) {
    left
  } else {
    asymmetric_and(left, right)
  }
}

///|
fn not_simplified(term : @logic.Term) -> @logic.Term raise {
  match term.view() {
    Ttrue => copy_term_decoration(term, @logic.Term::false_formula())
    Tfalse => copy_term_decoration(term, @logic.Term::true_formula())
    Tnot(inner) => copy_term_decoration(term, inner)
    _ => @logic.Term::not(term, None)
  }
}

///|
fn wp_if(
  condition : @logic.Term,
  yes : @logic.Term,
  no : @logic.Term,
) -> @logic.Term raise {
  if is_true(condition) && can_simplify_true(no) {
    yes
  } else if is_false(condition) && can_simplify_true(yes) {
    no
  } else if can_simplify_true(no) {
    sp_implies(condition, yes)
  } else if can_simplify_true(yes) {
    sp_implies(not_simplified(condition), no)
  } else {
    @logic.Term::if_then_else(condition, yes, no, None)
  }
}

///|
fn term_occurrences(term : @logic.Term, target : @logic.VSymbol) -> Int {
  match term.view() {
    Tvar(variable) => if variable == target { 1 } else { 0 }
    Tconst(_) | Ttrue | Tfalse => 0
    Tapp(_, _, arguments) =>
      arguments.fold(init=0, fn(total, child) {
        total + term_occurrences(child, target)
      })
    Tif(condition, yes, no) =>
      term_occurrences(condition, target) +
      term_occurrences(yes, target) +
      term_occurrences(no, target)
    Tlet(_, value, body) =>
      term_occurrences(value, target) + term_occurrences(body, target)
    Tcase(scrutinee, branches) => {
      let mut total = term_occurrences(scrutinee, target)
      for branch in branches {
        total = total + term_occurrences(branch.view().body, target)
      }
      total
    }
    Teps(_, body) => term_occurrences(body, target)
    Tquant(_, _, triggers, body) => {
      let mut total = term_occurrences(body, target)
      for group in triggers {
        for trigger in group {
          total = total + term_occurrences(trigger, target)
        }
      }
      total
    }
    Tbinop(_, left, right) =>
      term_occurrences(left, target) + term_occurrences(right, target)
    Tnot(inner) => term_occurrences(inner, target)
  }
}

///|
fn is_small_value(term : @logic.Term) -> Bool {
  term.view() is Tvar(_) || term.view() is Tconst(_)
}

///|
fn relevant_for_counterexample(variable : @logic.VSymbol) -> Bool {
  let origin = variable.view().origin
  let attributes = origin.attributes()
  (
    origin.source_span() is Some(_) &&
    !attributes.any(attribute => attribute == proxy_attribute)
  ) ||
  attributes.any(attribute => {
    bytes_have_prefix(attribute, b"model_trace:") ||
    bytes_have_prefix(attribute, b"eid:") ||
    bytes_have_prefix(attribute, b"vc:written:") ||
    attribute == b"model_projected"
  })
}

///|
fn fresh_unused_variable(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
) -> @logic.VSymbol raise {
  let view = variable.view()
  let attributes = view.origin.attributes().to_owned()
  attributes.push(b"id:unused")
  if !attributes.any(attribute => bytes_have_prefix(attribute, b"model_trace:")) {
    attributes.push(append_bytes(b"model_trace:", view.name))
  }
  let name = append_bytes(view.name, b"'unused")
  @logic.VSymbol::new(
    context,
    name,
    @identity.Origin::generated(
      @identity.Wp,
      name,
      view.origin.source_span(),
      attributes,
    ),
    view.ty,
    view.origin.source_span(),
  )
}

///|
fn substitute_variable(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  value : @logic.Term,
  body : @logic.Term,
) -> @logic.Term raise {
  @logic.TermSubstitution::new()
  .bind(variable, value, None)
  .apply(context, body, None)
}

///|
fn let_simplified_symbol(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  value : @logic.Term,
  body : @logic.Term,
  keep : Bool,
) -> @logic.Term raise {
  let occurrences = term_occurrences(body, variable)
  if occurrences == 0 {
    if keep {
      @logic.Term::let_in(
        fresh_unused_variable(context, variable),
        value,
        body,
        None,
      )
    } else {
      body
    }
  } else if occurrences == 1 || is_small_value(value) {
    let substituted = substitute_variable(context, variable, value, body)
    if keep {
      @logic.Term::let_in(
        fresh_unused_variable(context, variable),
        value,
        substituted,
        None,
      )
    } else {
      substituted
    }
  } else {
    @logic.Term::let_in(variable, value, body, None)
  }
}

///|
fn wp_let(
  environment : VcEnvironment,
  variable : @mlw.PVariable,
  value : @logic.Term,
  body : @logic.Term,
) -> @logic.Term raise {
  let symbol = variable.view().pure_symbol
  if variable.view().ity.to_ty(None) == environment.unit_value.ty().unwrap() {
    substitute_variable(
      environment.context,
      symbol,
      environment.unit_value,
      body,
    )
  } else {
    let_simplified_symbol(
      environment.context,
      symbol,
      value,
      body,
      relevant_for_counterexample(symbol),
    )
  }
}

///|
fn forall_simplified(
  binders : ArrayView[@logic.VSymbol],
  body : @logic.Term,
) -> @logic.Term raise {
  let free = body.free_variables()
  let retained = [
    for binder in binders if free.any(variable => variable == binder) => binder
  ]
  @logic.Term::quantify(ForallQuantifier, retained, [], body, None)
}

///|
fn is_builtin_equality(symbol : @logic.LSymbol) -> Bool {
  let view = symbol.view()
  view.name == b"infix =" &&
  view.result_type is None &&
  view.argument_types.length() == 2
}

///|
fn if_simplified(
  condition : @logic.Term,
  yes : @logic.Term,
  no : @logic.Term,
) -> @logic.Term raise {
  if is_true(condition) {
    yes
  } else if is_false(condition) {
    no
  } else if is_true(yes) {
    sp_implies(not_simplified(condition), no)
  } else if is_false(yes) {
    wp_and_asymmetric(not_simplified(condition), no)
  } else if is_true(no) {
    sp_implies(condition, yes)
  } else if is_false(no) {
    wp_and_asymmetric(condition, yes)
  } else if yes == no {
    yes
  } else {
    @logic.Term::if_then_else(condition, yes, no, None)
  }
}

///|
fn is_variable_term(term : @logic.Term, variable : @logic.VSymbol) -> Bool {
  term.view() is Tvar(candidate) && candidate == variable
}

///|
fn rewrite_boolean_tests(
  environment : VcEnvironment,
  term : @logic.Term,
  variable : @logic.VSymbol,
  predicate : @logic.Term,
) -> @logic.Term raise {
  let recurse = fn(child) -> @logic.Term raise {
    rewrite_boolean_tests(environment, child, variable, predicate)
  }
  let replacement = match term.view() {
    Tapp(symbol, _, arguments) if is_builtin_equality(symbol) &&
      arguments.length() == 2 &&
      (
        (
          is_variable_term(arguments[0], variable) &&
          arguments[1] == environment.boolean_true
        ) ||
        (
          is_variable_term(arguments[1], variable) &&
          arguments[0] == environment.boolean_true
        )
      ) => predicate
    Tapp(symbol, _, arguments) if is_builtin_equality(symbol) &&
      arguments.length() == 2 &&
      (
        (
          is_variable_term(arguments[0], variable) &&
          arguments[1] == environment.boolean_false
        ) ||
        (
          is_variable_term(arguments[1], variable) &&
          arguments[0] == environment.boolean_false
        )
      ) => not_simplified(predicate)
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => term
    Tapp(symbol, _, arguments) =>
      @logic.Term::elaborated_apply(
        symbol,
        [
          for argument in arguments => recurse(argument)
        ],
        term.ty(),
        None,
      )
    Tif(condition, yes, no) =>
      @logic.Term::if_then_else(
        recurse(condition),
        recurse(yes),
        recurse(no),
        None,
      )
    Tlet(binder, value, body) =>
      @logic.Term::let_in(binder, recurse(value), recurse(body), None)
    Tcase(scrutinee, branches) =>
      @logic.Term::trusted_case(
        recurse(scrutinee),
        [
          for branch in branches => {
            let view = branch.view()
            (view.pattern, recurse(view.body))
          }
        ],
        None,
      )
    Teps(binder, body) =>
      @logic.Term::trusted_epsilon(binder, recurse(body), None)
    Tquant(quantifier, binders, triggers, body) =>
      @logic.Term::quantify(
        quantifier,
        binders,
        [
          for group in triggers => [ for trigger in group => recurse(trigger) ]
        ],
        recurse(body),
        None,
      )
    Tbinop(operator, left, right) =>
      @logic.Term::binary(operator, recurse(left), recurse(right), None)
    Tnot(inner) => @logic.Term::not(recurse(inner), None)
  }
  copy_term_decoration(term, replacement)
}

///|
fn eval_match_minimal(
  environment : VcEnvironment,
  term : @logic.Term,
) -> @logic.Term raise {
  let recurse = fn(child) -> @logic.Term raise {
    eval_match_minimal(environment, child)
  }
  let replacement = match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => term
    Tapp(symbol, _, arguments) if is_builtin_equality(symbol) &&
      arguments.length() == 2 => {
      let left = recurse(arguments[0])
      let right = recurse(arguments[1])
      if left == right {
        @logic.Term::true_formula()
      } else {
        @logic.Term::elaborated_apply(symbol, [left, right], term.ty(), None)
      }
    }
    Tapp(symbol, _, arguments) =>
      @logic.Term::elaborated_apply(
        symbol,
        [
          for argument in arguments => recurse(argument)
        ],
        term.ty(),
        None,
      )
    Tif(condition, yes, no) =>
      if_simplified(recurse(condition), recurse(yes), recurse(no))
    Tlet(variable, value, body) => {
      let value = recurse(value)
      let body = match value.view() {
        Tif(predicate, yes, no) if yes == environment.boolean_true &&
          no == environment.boolean_false =>
          rewrite_boolean_tests(environment, body, variable, predicate)
        _ => body
      }
      let_simplified_symbol(
        environment.context,
        variable,
        value,
        recurse(body),
        relevant_for_counterexample(variable),
      )
    }
    Tcase(scrutinee, branches) =>
      @logic.Term::trusted_case(
        recurse(scrutinee),
        [
          for branch in branches => {
            let view = branch.view()
            (view.pattern, recurse(view.body))
          }
        ],
        None,
      )
    Teps(variable, body) =>
      @logic.Term::trusted_epsilon(variable, recurse(body), None)
    Tquant(quantifier, binders, triggers, body) => {
      let body = recurse(body)
      let free = body.free_variables()
      let retained = []
      for binder in binders {
        if free.any(variable => variable == binder) {
          retained.push(binder)
        }
      }
      @logic.Term::quantify(
        quantifier,
        retained,
        [
          for group in triggers if group.all(trigger => {
            trigger
            .free_variables()
            .all(variable => {
              retained.any(binder => binder == variable) ||
              free.any(candidate => candidate == variable)
            })
          }) => [ for trigger in group => recurse(trigger) ]
        ],
        body,
        None,
      )
    }
    Tbinop(operator, left, right) =>
      @logic.Term::binary(operator, recurse(left), recurse(right), None)
    Tnot(inner) => @logic.Term::not(recurse(inner), None)
  }
  copy_term_decoration(term, replacement)
}

///|
fn contains_attribute(term : @logic.Term, wanted : BytesView) -> Bool {
  if term.attributes().any(attribute => attribute[:] == wanted) {
    return true
  }
  match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => false
    Tapp(_, _, arguments) =>
      arguments.any(argument => contains_attribute(argument, wanted))
    Tif(condition, yes, no) =>
      contains_attribute(condition, wanted) ||
      contains_attribute(yes, wanted) ||
      contains_attribute(no, wanted)
    Tlet(_, value, body) =>
      contains_attribute(value, wanted) || contains_attribute(body, wanted)
    Tcase(scrutinee, branches) =>
      contains_attribute(scrutinee, wanted) ||
      branches.any(branch => contains_attribute(branch.view().body, wanted))
    Teps(_, body) => contains_attribute(body, wanted)
    Tquant(_, _, triggers, body) =>
      triggers.any(group => {
        group.any(trigger => contains_attribute(trigger, wanted))
      }) ||
      contains_attribute(body, wanted)
    Tbinop(_, left, right) =>
      contains_attribute(left, wanted) || contains_attribute(right, wanted)
    Tnot(inner) => contains_attribute(inner, wanted)
  }
}

///|
fn is_structurally_trivial(term : @logic.Term) -> Bool {
  match term.view() {
    Ttrue => true
    Tlet(_, _, body) => is_structurally_trivial(body)
    Tquant(ForallQuantifier, _, _, body) => is_structurally_trivial(body)
    Tbinop(Implies, _, right) => is_structurally_trivial(right)
    Tbinop(And, left, right) =>
      is_structurally_trivial(left) && is_structurally_trivial(right)
    Tcase(_, branches) =>
      branches.all(branch => is_structurally_trivial(branch.view().body))
    Tif(_, yes, no) =>
      is_structurally_trivial(yes) && is_structurally_trivial(no)
    _ => false
  }
}
