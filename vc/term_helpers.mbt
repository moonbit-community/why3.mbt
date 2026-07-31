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
fn relocate_term_checked(
  term : @logic.Term,
  span : @identity.SourceSpan,
) -> @logic.Term raise {
  let recurse = fn(child : @logic.Term) -> @logic.Term raise {
    if child.ty() is Some(_) {
      child
    } else {
      relocate_term_checked(child, span)
    }
  }
  let replacement = match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => term
    Tapp(symbol, _, arguments) =>
      @logic.Term::elaborated_apply(
        symbol,
        arguments.map(recurse),
        term.ty(),
        Some(span),
      )
    Tif(condition, yes, no) =>
      @logic.Term::if_then_else(
        recurse(condition),
        recurse(yes),
        recurse(no),
        Some(span),
      )
    Tlet(variable, value, body) =>
      @logic.Term::let_in(variable, recurse(value), recurse(body), Some(span))
    Tcase(scrutinee, branches) =>
      @logic.Term::case(
        recurse(scrutinee),
        branches.map(branch => {
          let view = branch.view()
          (view.pattern, recurse(view.body))
        }),
        Some(span),
      )
    Teps(variable, body) =>
      @logic.Term::epsilon(variable, recurse(body), Some(span))
    Tquant(quantifier, binders, triggers, body) =>
      @logic.Term::quantify(
        quantifier,
        binders,
        triggers.map(group => group.map(recurse)),
        recurse(body),
        Some(span),
      )
    Tbinop(operator, left, right) =>
      @logic.Term::binary(operator, recurse(left), recurse(right), Some(span))
    Tnot(inner) => @logic.Term::not(recurse(inner), Some(span))
  }
  let relocated = replacement.source_decorate(Some(span), term.attributes())
  match term.origin() {
    Some(origin) => relocated.decorate(origin, term.attributes())
    None => relocated
  }
}

///|
fn relocate_term(
  term : @logic.Term,
  span : @identity.SourceSpan,
) -> @logic.Term {
  relocate_term_checked(term, span) catch {
    _ => abort("relocating a validated term changed its type")
  }
}

///|
fn vc_explanation(
  term : @logic.Term,
  attributes : ArrayView[Bytes],
  explanation : BytesView,
  span? : @identity.SourceSpan? = None,
) -> @logic.Term {
  let term = match span {
    Some(span) => relocate_term(term, span)
    None => term
  }
  let additions = attributes.to_owned()
  additions.push(stop_split_attribute)
  additions.push(annotation_attribute)
  if !has_explanation(merged_attributes(term.attributes(), additions)) {
    additions.push(explanation.to_owned())
  }
  term.add_attributes(additions)
}

///|
fn solder_explanation(
  formula : @logic.Term,
  explanation : BytesView,
) -> @logic.Term {
  if can_simplify_true(formula) {
    return formula
  }
  let additions = [stop_split_attribute]
  if !has_explanation(formula.attributes()) {
    additions.push(explanation.to_owned())
  }
  formula.add_attributes(additions)
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
  span? : @identity.SourceSpan? = None,
) -> @logic.Term raise {
  match formula.view() {
    Tbinop(And, left, right) if !formula
      .attributes()
      .any(attribute => attribute == annotation_attribute) =>
      copy_term_decoration(
        formula,
        plain_and(
          push_stop(left, attributes, explanation, span~),
          push_stop(right, attributes, explanation, span~),
        ),
      )
    _ => vc_explanation(formula, attributes, explanation, span~)
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
  match term.view() {
    Tvar(_) | Tconst(_) => true
    _ => false
  }
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
      @logic.Term::case(
        recurse(scrutinee),
        [
          for branch in branches => {
            let view = branch.view()
            (view.pattern, recurse(view.body))
          }
        ],
        None,
      )
    Teps(binder, body) => @logic.Term::epsilon(binder, recurse(body), None)
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
priv struct EvalMatchRow {
  patterns : Array[@logic.Pattern]
  body : @logic.Term
}

///|
priv struct EvalMatchConstructorRows {
  symbol : @logic.LSymbol
  argument_patterns : Array[@logic.Pattern]
  rows : Array[EvalMatchRow]
}

///|
fn is_constructor_symbol(symbol : @logic.LSymbol) -> Bool {
  symbol.view().role is Constructor(_)
}

///|
fn is_projection_symbol(symbol : @logic.LSymbol) -> Bool {
  symbol.view().role is Projection
}

///|
fn type_constructors(
  environment : VcEnvironment,
  ty : @logic.Ty,
) -> Array[@logic.DataConstructor] raise {
  match ty.view() {
    TyVar(_) => []
    TyApp(symbol, _) => environment.known.find_constructors(symbol, None)
  }
}

///|
fn find_constructor_declaration(
  environment : VcEnvironment,
  symbol : @logic.LSymbol,
) -> @logic.DataConstructor? raise {
  guard symbol.view().result_type is Some(result_type) else { return None }
  for data_constructor in type_constructors(environment, result_type) {
    if data_constructor.view().symbol == symbol {
      return Some(data_constructor)
    }
  }
  None
}

///|
fn select_constructor_projection(
  environment : VcEnvironment,
  constructor_symbol : @logic.LSymbol,
  projection : @logic.LSymbol,
  arguments : ArrayView[@logic.Term],
) -> @logic.Term? raise {
  guard find_constructor_declaration(environment, constructor_symbol)
    is Some(declaration) else {
    return None
  }
  let fields = declaration.view().projections
  for index, field in fields {
    if field is Some(candidate) && candidate == projection {
      return Some(arguments[index])
    }
  }
  None
}

///|
fn is_inlineable_logic_body(term : @logic.Term) -> Bool {
  match term.view() {
    Tvar(_) | Tconst(_) => true
    Tapp(_, _, [argument]) => argument.view() is Tvar(_)
    Tcase(scrutinee, [branch]) =>
      scrutinee.view() is Tvar(_) && branch.view().body.view() is Tvar(_)
    _ => false
  }
}

///|
fn eval_match_type_substitution(
  instantiations : ArrayView[(@logic.TyVarSymbol, @logic.Ty)],
) -> @logic.TySubstitution raise {
  let mut substitution = @logic.TySubstitution::new()
  for entry in instantiations {
    substitution = substitution.bind(entry.0, entry.1, None)
  }
  substitution
}

///|
fn instantiate_eval_match_variable(
  environment : VcEnvironment,
  substitution : @logic.TySubstitution,
  variable : @logic.VSymbol,
) -> @logic.VSymbol raise {
  let view = variable.view()
  @logic.VSymbol::new(
    environment.context,
    view.name,
    view.origin,
    substitution.apply(view.ty, None),
    None,
  )
}

///|
fn instantiate_eval_match_pattern(
  environment : VcEnvironment,
  substitution : @logic.TySubstitution,
  variables : Map[@logic.VSymbol, @logic.Term],
  pattern : @logic.Pattern,
) -> @logic.Pattern raise {
  match pattern.view() {
    Pwild(ty) => @logic.Pattern::wild(substitution.apply(ty, None))
    Pvar(variable) =>
      match variables.get(variable) {
        Some(replacement) =>
          match replacement.view() {
            Tvar(replacement) => @logic.Pattern::variable(replacement)
            _ => abort("bound pattern variable maps to a non-variable term")
          }
        None => abort("bound pattern variable has no instantiated symbol")
      }
    Papp(symbol, arguments, ty) =>
      @logic.Pattern::app(
        symbol,
        arguments.map(argument => {
          instantiate_eval_match_pattern(
            environment, substitution, variables, argument,
          )
        }),
        substitution.apply(ty, None),
        None,
      )
    Por(left, right, _) =>
      @logic.Pattern::or(
        instantiate_eval_match_pattern(
          environment, substitution, variables, left,
        ),
        instantiate_eval_match_pattern(
          environment, substitution, variables, right,
        ),
        None,
      )
    Pas(inner, variable, _) =>
      match variables.get(variable) {
        Some(replacement) =>
          match replacement.view() {
            Tvar(replacement) =>
              @logic.Pattern::as_pattern(
                instantiate_eval_match_pattern(
                  environment, substitution, variables, inner,
                ),
                replacement,
                None,
              )
            _ => abort("bound as-pattern variable maps to a non-variable term")
          }
        None => abort("bound as-pattern variable has no instantiated symbol")
      }
  }
}

///|
fn instantiate_eval_match_term(
  environment : VcEnvironment,
  substitution : @logic.TySubstitution,
  variables : Map[@logic.VSymbol, @logic.Term],
  term : @logic.Term,
) -> @logic.Term raise {
  let recurse = fn(child) -> @logic.Term raise {
    instantiate_eval_match_term(environment, substitution, variables, child)
  }
  let replacement = match term.view() {
    Tvar(variable) =>
      match variables.get(variable) {
        Some(replacement) => replacement
        None => {
          let replacement = instantiate_eval_match_variable(
            environment, substitution, variable,
          )
          variables[variable] = @logic.Term::variable(replacement)
          @logic.Term::variable(replacement)
        }
      }
    Tconst(constant) => {
      guard term.ty() is Some(ty) else {
        abort("constant term lost its value type")
      }
      @logic.Term::constant(constant, substitution.apply(ty, None), None)
    }
    Tapp(symbol, _, arguments) =>
      @logic.Term::elaborated_apply(
        symbol,
        arguments.map(recurse),
        match term.ty() {
          Some(ty) => Some(substitution.apply(ty, None))
          None => None
        },
        None,
      )
    Tif(condition, yes, no) =>
      @logic.Term::if_then_else(
        recurse(condition),
        recurse(yes),
        recurse(no),
        None,
      )
    Tlet(variable, value, body) => {
      let replacement = instantiate_eval_match_variable(
        environment, substitution, variable,
      )
      let body_variables = variables.copy()
      body_variables[variable] = @logic.Term::variable(replacement)
      @logic.Term::let_in(
        replacement,
        recurse(value),
        instantiate_eval_match_term(
          environment, substitution, body_variables, body,
        ),
        None,
      )
    }
    Tcase(scrutinee, branches) => {
      let rebuilt = []
      for branch in branches {
        let view = branch.view()
        let branch_variables = variables.copy()
        for variable in view.pattern.bound_variables() {
          branch_variables[variable] = @logic.Term::variable(
            instantiate_eval_match_variable(environment, substitution, variable),
          )
        }
        rebuilt.push(
          (
            instantiate_eval_match_pattern(
              environment,
              substitution,
              branch_variables,
              view.pattern,
            ),
            instantiate_eval_match_term(
              environment,
              substitution,
              branch_variables,
              view.body,
            ),
          ),
        )
      }
      @logic.Term::case(recurse(scrutinee), rebuilt, None)
    }
    Teps(variable, body) => {
      let replacement = instantiate_eval_match_variable(
        environment, substitution, variable,
      )
      let body_variables = variables.copy()
      body_variables[variable] = @logic.Term::variable(replacement)
      @logic.Term::epsilon(
        replacement,
        instantiate_eval_match_term(
          environment, substitution, body_variables, body,
        ),
        None,
      )
    }
    Tquant(quantifier, binders, triggers, body) => {
      let body_variables = variables.copy()
      let replacements = []
      for binder in binders {
        let replacement = instantiate_eval_match_variable(
          environment, substitution, binder,
        )
        replacements.push(replacement)
        body_variables[binder] = @logic.Term::variable(replacement)
      }
      @logic.Term::quantify(
        quantifier,
        replacements,
        triggers.map(group => {
          group.map(trigger => {
            instantiate_eval_match_term(
              environment, substitution, body_variables, trigger,
            )
          })
        }),
        instantiate_eval_match_term(
          environment, substitution, body_variables, body,
        ),
        None,
      )
    }
    Tbinop(operator, left, right) =>
      @logic.Term::binary(operator, recurse(left), recurse(right), None)
    Tnot(inner) => @logic.Term::not(recurse(inner), None)
    Ttrue => @logic.Term::true_formula()
    Tfalse => @logic.Term::false_formula()
  }
  copy_term_decoration(term, replacement)
}

///|
fn unfold_inlineable_logic_application(
  environment : VcEnvironment,
  symbol : @logic.LSymbol,
  instantiations : ArrayView[(@logic.TyVarSymbol, @logic.Ty)],
  arguments : ArrayView[@logic.Term],
) -> @logic.Term? raise {
  // Program-only symbols such as the private `DECR f` predicate belong to
  // Why3's program declaration map but intentionally have no pure
  // declaration to unfold. The portable module keeps only the pure known
  // map, so treat such symbols as opaque instead of reporting an unknown
  // pure dependency.
  if environment.known.find_declaration(@logic.LogicDependency(symbol)) is None {
    return None
  }
  guard environment.known.find_logic_definition(symbol, None)
    is Some(definition) else {
    return None
  }
  let view = definition.view()
  if !is_inlineable_logic_body(view.body) ||
    view.parameters.length() != arguments.length() {
    return None
  }
  let variables : Map[@logic.VSymbol, @logic.Term] = Map([])
  for index, parameter in view.parameters {
    variables[parameter] = arguments[index]
  }
  Some(
    instantiate_eval_match_term(
      environment,
      eval_match_type_substitution(instantiations),
      variables,
      view.body,
    ),
  )
}

///|
fn reverse_prepend_match_patterns(
  prefix : ArrayView[@logic.Pattern],
  suffix : ArrayView[@logic.Pattern],
) -> Array[@logic.Pattern] {
  let result = []
  for index = prefix.length() - 1; index >= 0; index = index - 1 {
    result.push(prefix[index])
  }
  for pattern in suffix {
    result.push(pattern)
  }
  result
}

///|
fn reverse_prepend_match_terms(
  prefix : ArrayView[@logic.Term],
  suffix : ArrayView[@logic.Term],
) -> Array[@logic.Term] {
  let result = []
  for index = prefix.length() - 1; index >= 0; index = index - 1 {
    result.push(prefix[index])
  }
  for term in suffix {
    result.push(term)
  }
  result
}

///|
fn drop_first_match_pattern(
  patterns : ArrayView[@logic.Pattern],
) -> Array[@logic.Pattern] {
  let result = []
  for index = 1; index < patterns.length(); index = index + 1 {
    result.push(patterns[index])
  }
  result
}

///|
fn drop_first_match_term(terms : ArrayView[@logic.Term]) -> Array[@logic.Term] {
  let result = []
  for index = 1; index < terms.length(); index = index + 1 {
    result.push(terms[index])
  }
  result
}

///|
fn find_match_constructor_rows(
  groups : ArrayView[EvalMatchConstructorRows],
  symbol : @logic.LSymbol,
) -> Int? {
  for index, group in groups {
    if group.symbol == symbol {
      return Some(index)
    }
  }
  None
}

///|
fn collect_match_constructor_rows(
  pattern : @logic.Pattern,
  groups : Array[EvalMatchConstructorRows],
) -> Unit {
  match pattern.view() {
    Pwild(_) | Pvar(_) => ()
    Papp(symbol, arguments, _) =>
      if find_match_constructor_rows(groups, symbol) is None {
        groups.push({
          symbol,
          argument_patterns: arguments.to_owned(),
          rows: [],
        })
      }
    Por(left, right, _) => {
      collect_match_constructor_rows(left, groups)
      collect_match_constructor_rows(right, groups)
    }
    Pas(inner, _, _) => collect_match_constructor_rows(inner, groups)
  }
}

///|
fn wildcard_constructor_arguments(
  group : EvalMatchConstructorRows,
) -> Array[@logic.Pattern] {
  group.argument_patterns.map(pattern => @logic.Pattern::wild(pattern.ty()))
}

///|
fn bind_match_pattern_variable(
  environment : VcEnvironment,
  variable : @logic.VSymbol,
  value : @logic.Term,
  body : @logic.Term,
) -> @logic.Term raise {
  let_simplified_symbol(environment.context, variable, value, body, false)
}

///|
fn dispatch_match_pattern(
  environment : VcEnvironment,
  scrutinee : @logic.Term,
  pattern : @logic.Pattern,
  remaining : ArrayView[@logic.Pattern],
  body : @logic.Term,
  groups : Array[EvalMatchConstructorRows],
  wild_rows : Array[EvalMatchRow],
) -> Unit raise {
  match pattern.view() {
    Papp(symbol, arguments, _) => {
      guard find_match_constructor_rows(groups, symbol) is Some(index) else {
        abort("pattern constructor was absent from its dispatch table")
      }
      groups[index].rows.push({
        patterns: reverse_prepend_match_patterns(arguments, remaining),
        body,
      })
    }
    Por(left, right, _) => {
      dispatch_match_pattern(
        environment, scrutinee, left, remaining, body, groups, wild_rows,
      )
      dispatch_match_pattern(
        environment, scrutinee, right, remaining, body, groups, wild_rows,
      )
    }
    Pas(inner, variable, _) =>
      dispatch_match_pattern(
        environment,
        scrutinee,
        inner,
        remaining,
        bind_match_pattern_variable(environment, variable, scrutinee, body),
        groups,
        wild_rows,
      )
    Pvar(variable) => {
      let body = bind_match_pattern_variable(
        environment, variable, scrutinee, body,
      )
      for group in groups {
        group.rows.push({
          patterns: reverse_prepend_match_patterns(
            wildcard_constructor_arguments(group),
            remaining,
          ),
          body,
        })
      }
      wild_rows.push({ patterns: remaining.to_owned(), body })
    }
    Pwild(_) => {
      for group in groups {
        group.rows.push({
          patterns: reverse_prepend_match_patterns(
            wildcard_constructor_arguments(group),
            remaining,
          ),
          body,
        })
      }
      wild_rows.push({ patterns: remaining.to_owned(), body })
    }
  }
}

///|
fn fresh_match_variable(
  environment : VcEnvironment,
  ty : @logic.Ty,
) -> @logic.VSymbol raise {
  @logic.VSymbol::new(
    environment.context,
    b"_match",
    @identity.Origin::generated(@identity.Wp, b"_match", None, []),
    ty,
    None,
  )
}

///|
fn compile_match_matrix(
  environment : VcEnvironment,
  terms : ArrayView[@logic.Term],
  rows : ArrayView[EvalMatchRow],
) -> @logic.Term? raise {
  if rows.is_empty() {
    return None
  }
  if terms.is_empty() {
    return Some(rows[0].body)
  }
  let scrutinee = terms[0]
  guard scrutinee.ty() is Some(scrutinee_type) else {
    abort("pattern matrix scrutinee is a formula")
  }
  let remaining_terms = drop_first_match_term(terms)
  let groups : Array[EvalMatchConstructorRows] = []
  for row in rows {
    if row.patterns.is_empty() {
      return Some(row.body)
    }
    collect_match_constructor_rows(row.patterns[0], groups)
  }
  let wild_rows : Array[EvalMatchRow] = []
  for row in rows {
    dispatch_match_pattern(
      environment,
      scrutinee,
      row.patterns[0],
      drop_first_match_pattern(row.patterns),
      row.body,
      groups,
      wild_rows,
    )
  }
  if groups.is_empty() {
    return compile_match_matrix(environment, remaining_terms, wild_rows)
  }
  match scrutinee.view() {
    Tapp(symbol, _, arguments) if is_constructor_symbol(symbol) =>
      match find_match_constructor_rows(groups, symbol) {
        Some(index) =>
          return compile_match_matrix(
            environment,
            reverse_prepend_match_terms(arguments, remaining_terms),
            groups[index].rows,
          )
        None =>
          return compile_match_matrix(environment, remaining_terms, wild_rows)
      }
    _ => ()
  }
  let branches : Array[(@logic.Pattern, @logic.Term)] = []
  for group in groups {
    let variables = group.argument_patterns.map(pattern => {
      fresh_match_variable(environment, pattern.ty())
    })
    let branch_terms = variables.map(@logic.Term::variable)
    guard compile_match_matrix(
        environment,
        reverse_prepend_match_terms(branch_terms, remaining_terms),
        group.rows,
      )
      is Some(body) else {
      return None
    }
    branches.push(
      (
        @logic.Pattern::app(
          group.symbol,
          variables.map(@logic.Pattern::variable),
          scrutinee_type,
          None,
        ),
        body,
      ),
    )
  }
  let complete = match groups[0].symbol.view().role {
    Constructor(count) => groups.length() == count
    Ordinary | Projection => false
  }
  if !complete {
    guard compile_match_matrix(environment, remaining_terms, wild_rows)
      is Some(body) else {
      return None
    }
    branches.push((@logic.Pattern::wild(scrutinee_type), body))
  }
  if branches.is_empty() {
    None
  } else {
    Some(@logic.Term::case(scrutinee, branches, None))
  }
}

///|
fn flatten_eval_match_case(
  environment : VcEnvironment,
  scrutinee : @logic.Term,
  branches : ArrayView[@logic.TermBranch],
) -> @logic.Term? raise {
  compile_match_matrix(
    environment,
    [scrutinee],
    branches.map(branch => {
      let view = branch.view()
      { patterns: [view.pattern], body: view.body }
    }),
  )
}

///|
fn dive_to_eval_match_constructor(
  environment : VcEnvironment,
  keep_trace : Bool,
  bindings : Map[@logic.VSymbol, @logic.Term],
  term : @logic.Term,
  callback : (
    Map[@logic.VSymbol, @logic.Term],
    @logic.Term,
    @logic.LSymbol,
    ArrayView[@logic.Term],
  ) -> @logic.Term? raise,
) -> @logic.Term? raise {
  let result = match term.view() {
    Tvar(variable) =>
      match bindings.get(variable) {
        Some(value) =>
          dive_to_eval_match_constructor(
            environment, keep_trace, bindings, value, callback,
          )
        None => None
      }
    Tlet(variable, value, body) => {
      let nested = bindings.copy()
      nested[variable] = value
      match
        dive_to_eval_match_constructor(
          environment, keep_trace, nested, body, callback,
        ) {
        Some(result) =>
          Some(
            let_simplified_symbol(
              environment.context,
              variable,
              value,
              result,
              keep_trace && relevant_for_counterexample(variable),
            ),
          )
        None => None
      }
    }
    Tcase(scrutinee, branches) => {
      let rebuilt : Array[(@logic.Pattern, @logic.Term)] = []
      let mut failed = false
      for branch in branches {
        let view = branch.view()
        match
          dive_to_eval_match_constructor(
            environment,
            keep_trace,
            bindings,
            view.body,
            callback,
          ) {
          Some(body) => rebuilt.push((view.pattern, body))
          None => failed = true
        }
      }
      if failed {
        None
      } else {
        Some(@logic.Term::case(scrutinee, rebuilt, None))
      }
    }
    Tif(condition, yes, no) =>
      match
        (
          dive_to_eval_match_constructor(
            environment, keep_trace, bindings, yes, callback,
          ),
          dive_to_eval_match_constructor(
            environment, keep_trace, bindings, no, callback,
          ),
        ) {
        (Some(yes), Some(no)) => Some(if_simplified(condition, yes, no))
        _ => None
      }
    Tapp(symbol, _, arguments) if is_constructor_symbol(symbol) =>
      callback(bindings, term, symbol, arguments)
    _ => None
  }
  match result {
    Some(result) => Some(copy_term_decoration(term, result))
    None => None
  }
}

///|
fn eval_constructor_equality(
  environment : VcEnvironment,
  keep_trace : Bool,
  bindings : Map[@logic.VSymbol, @logic.Term],
  left : @logic.Term,
  right : @logic.Term,
) -> @logic.Term raise {
  if left == right {
    return @logic.Term::true_formula()
  }
  let reduced = dive_to_eval_match_constructor(
    environment,
    keep_trace,
    bindings,
    left,
    (left_bindings, _, left_symbol, left_arguments) => {
      dive_to_eval_match_constructor(
        environment,
        keep_trace,
        left_bindings,
        right,
        (combined_bindings, _, right_symbol, right_arguments) => {
          if left_symbol != right_symbol {
            return Some(@logic.Term::false_formula())
          }
          if left_arguments.length() != right_arguments.length() {
            abort("equal constructors expose different arities")
          }
          Some(
            conjunction(
              [
                for index, argument in left_arguments => {
                  eval_constructor_equality(
                    environment,
                    keep_trace,
                    combined_bindings,
                    argument,
                    right_arguments[index],
                  )
                }
              ],
            ),
          )
        },
      )
    },
  )
  match reduced {
    Some(formula) => formula
    None =>
      @logic.Term::elaborated_apply(
        environment.equality,
        [left, right],
        None,
        None,
      )
  }
}

///|
fn is_tuple_constructor(symbol : @logic.LSymbol) -> Bool {
  symbol.view().origin
  .attributes()
  .any(attribute => attribute == b"why3:builtin:tuple-constructor")
}

///|
fn destructible_match_constructor(
  environment : VcEnvironment,
  ty : @logic.Ty,
) -> @logic.DataConstructor? raise {
  guard type_constructors(environment, ty) is [data_constructor] else {
    return None
  }
  let symbol = data_constructor.view().symbol
  let arity = symbol.view().argument_types.length()
  if arity <= 1 || is_tuple_constructor(symbol) {
    Some(data_constructor)
  } else {
    None
  }
}

///|
fn quantified_constructor_argument_types(
  data_constructor : @logic.DataConstructor,
  result_type : @logic.Ty,
) -> Array[@logic.Ty] raise {
  let symbol = data_constructor.view().symbol
  guard symbol.view().result_type is Some(formal_result) else {
    abort("data constructor lost its result type")
  }
  let substitution = @logic.TySubstitution::new().match_type(
    formal_result,
    result_type,
    None,
  )
  symbol.view().argument_types.map(argument => {
    substitution.apply(argument, None)
  })
}

///|
fn clone_eval_match_origin(
  origin : @identity.Origin,
  additions : ArrayView[Bytes],
) -> @identity.Origin {
  let attributes = origin.attributes().to_owned()
  for attribute in additions {
    attributes.push(attribute)
  }
  match origin.view() {
    UserOrigin(name, span, _) => @identity.Origin::user(name, span, attributes)
    GeneratedOrigin(stage, name, span, _) =>
      @identity.Origin::generated_with_identifier_source_span(
        stage,
        name,
        span,
        origin.identifier_source_span(),
        attributes,
      )
  }
}

///|
fn projection_model_trace_name(projection : @logic.LSymbol) -> Bytes {
  let view = projection.view()
  for attribute in view.origin.attributes() {
    if bytes_have_prefix(attribute, b"model_trace:") {
      let name = attribute[b"model_trace:".length():]
      if !name.is_empty() {
        return name.to_owned()
      }
    }
  }
  view.name
}

///|
fn model_trace_field_attribute(
  projection : @logic.LSymbol,
  depth : Int,
) -> Bytes {
  let digits : Array[Byte] = []
  let mut remaining = depth
  if remaining == 0 {
    digits.push(b'0')
  } else {
    while remaining > 0 {
      digits.push((b'0'.to_int() + remaining % 10).to_byte())
      remaining = remaining / 10
    }
  }
  let field = projection_model_trace_name(projection)
  let buffer = @buffer.Buffer(
    size_hint=b"field::".length() + digits.length() + field.length(),
  )
  buffer.write_bytes(b"field:")
  for index = digits.length() - 1; index >= 0; index = index - 1 {
    buffer.write_byte(digits[index])
  }
  buffer.write_byte(b':')
  buffer.write_bytes(field)
  buffer.to_bytes()
}

///|
fn quantified_match_variable(
  environment : VcEnvironment,
  source : @logic.VSymbol,
  projection : @logic.LSymbol?,
  depth : Int,
  add_field_attribute : Bool,
  ty : @logic.Ty,
) -> @logic.VSymbol raise {
  let view = source.view()
  let additions = match (add_field_attribute, projection) {
    (true, Some(projection)) => [model_trace_field_attribute(projection, depth)]
    _ => []
  }
  @logic.VSymbol::new(
    environment.context,
    view.name,
    clone_eval_match_origin(view.origin, additions),
    ty,
    None,
  )
}

///|
fn default_quantified_match_templates(
  variable : @logic.VSymbol,
  projections : ArrayView[@logic.LSymbol?],
) -> Array[(@logic.VSymbol, Bool)] {
  projections.map(_ => (variable, true))
}

///|
fn find_quantified_match_templates(
  variable : @logic.VSymbol,
  constructor_symbol : @logic.LSymbol,
  projections : ArrayView[@logic.LSymbol?],
  term : @logic.Term,
) -> Array[(@logic.VSymbol, Bool)]? {
  match term.view() {
    Tcase(scrutinee, [branch]) =>
      match scrutinee.view() {
        Tvar(candidate) if candidate == variable =>
          match branch.view().pattern.view() {
            Pvar(bound) =>
              Some(default_quantified_match_templates(bound, projections))
            Papp(symbol, patterns, _) if symbol == constructor_symbol => {
              let templates = []
              for pattern in patterns {
                match pattern.view() {
                  Pvar(bound) => templates.push((bound, false))
                  _ => templates.push((variable, true))
                }
              }
              Some(templates)
            }
            _ => None
          }
        _ =>
          match
            find_quantified_match_templates(
              variable, constructor_symbol, projections, scrutinee,
            ) {
            Some(templates) => Some(templates)
            None =>
              find_quantified_match_templates(
                variable,
                constructor_symbol,
                projections,
                branch.view().body,
              )
          }
      }
    Tcase(scrutinee, _) =>
      find_quantified_match_templates(
        variable, constructor_symbol, projections, scrutinee,
      )
    Tbinop(Implies, _, right) =>
      find_quantified_match_templates(
        variable, constructor_symbol, projections, right,
      )
    Tbinop(And, left, right) =>
      match
        find_quantified_match_templates(
          variable, constructor_symbol, projections, left,
        ) {
        Some(templates) => Some(templates)
        None =>
          find_quantified_match_templates(
            variable, constructor_symbol, projections, right,
          )
      }
    Tquant(_, _, _, body) =>
      find_quantified_match_templates(
        variable, constructor_symbol, projections, body,
      )
    _ => None
  }
}

///|
fn add_quantified_match_variable(
  environment : VcEnvironment,
  variable : @logic.VSymbol,
  triggers : ArrayView[Array[@logic.Term]],
  body : @logic.Term,
  depth : Int,
) -> (Array[@logic.VSymbol], Array[Array[@logic.Term]], @logic.Term) raise {
  guard destructible_match_constructor(environment, variable.ty())
    is Some(data_constructor) else {
    return ([variable], triggers.to_owned(), body)
  }
  let constructor_view = data_constructor.view()
  let argument_types = quantified_constructor_argument_types(
    data_constructor,
    variable.ty(),
  )
  let templates = match
    find_quantified_match_templates(
      variable,
      constructor_view.symbol,
      constructor_view.projections,
      body,
    ) {
    Some(templates) => templates
    None =>
      default_quantified_match_templates(variable, constructor_view.projections)
  }
  let variables = []
  for index, ty in argument_types {
    let template = templates[index]
    variables.push(
      quantified_match_variable(
        environment,
        template.0,
        constructor_view.projections[index],
        depth,
        template.1,
        ty,
      ),
    )
  }
  let constructor_term = @logic.Term::elaborated_apply(
    constructor_view.symbol,
    variables.map(@logic.Term::variable),
    Some(variable.ty()),
    None,
  )
  let substitution = @logic.TermSubstitution::new().bind(
    variable,
    constructor_term,
    None,
  )
  let mut current_triggers = triggers.map(group => {
    group.map(trigger => substitution.apply(environment.context, trigger, None))
  })
  let mut current_body = let_simplified_symbol(
    environment.context,
    variable,
    constructor_term,
    body,
    false,
  )
  let retained : Array[@logic.VSymbol] = []
  for nested in variables {
    let (nested_variables, nested_triggers, nested_body) = add_quantified_match_variable(
      environment,
      nested,
      current_triggers,
      current_body,
      depth + 1,
    )
    for retained_variable in nested_variables {
      retained.push(retained_variable)
    }
    current_triggers = nested_triggers
    current_body = nested_body
  }
  (retained, current_triggers, current_body)
}

///|
fn retain_quantifier_triggers(
  binders : ArrayView[@logic.VSymbol],
  body : @logic.Term,
  triggers : ArrayView[Array[@logic.Term]],
) -> Array[Array[@logic.Term]] {
  let free = body.free_variables()
  [
    for group in triggers if group.all(trigger => {
      trigger
      .free_variables()
      .all(variable => {
        binders.any(binder => binder == variable) ||
        free.any(candidate => candidate == variable)
      })
    }) => group.copy()
  ]
}

///|
fn eval_match_with(
  environment : VcEnvironment,
  keep_trace : Bool,
  stop : Bool,
  bindings : Map[@logic.VSymbol, @logic.Term],
  term : @logic.Term,
) -> @logic.Term raise {
  let stop = stop ||
    term.ty() is Some(_) ||
    term.attributes().any(attribute => attribute == annotation_attribute)
  let recurse = fn(child) -> @logic.Term raise {
    eval_match_with(environment, keep_trace, stop, bindings, child)
  }
  let replacement = match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => term
    Tapp(symbol, _, arguments) if is_builtin_equality(symbol) &&
      arguments.length() == 2 => {
      let left = recurse(arguments[0])
      let right = recurse(arguments[1])
      eval_constructor_equality(environment, keep_trace, bindings, left, right)
    }
    Tnot(inner) =>
      match inner.view() {
        Tapp(symbol, _, arguments) if is_builtin_equality(symbol) &&
          arguments.length() == 2 => {
          let equality = eval_constructor_equality(
            environment,
            keep_trace,
            bindings,
            recurse(arguments[0]),
            recurse(arguments[1]),
          )
          not_simplified(
            if term.source_span() is None {
              copy_term_decoration(inner, equality)
            } else {
              equality
            },
          )
        }
        _ => @logic.Term::not(recurse(inner), None)
      }
    Tapp(symbol, _, [argument]) if argument.view() is Tconst(constant) &&
      argument.ty() is Some(argument_type) &&
      argument_type.view() is TyApp(type_symbol, _) &&
      environment.pure_theory.range_projection(type_symbol) is Some(projection) &&
      projection == symbol => {
      guard term.ty() is Some(result_type) else {
        abort("range projection application lost its result type")
      }
      @logic.Term::constant(constant, result_type, term.source_span())
    }
    Tapp(symbol, _, [argument]) if is_projection_symbol(symbol) => {
      let argument = recurse(argument)
      match
        dive_to_eval_match_constructor(
          environment,
          keep_trace,
          bindings,
          argument,
          (_, _, constructor_symbol, arguments) => {
            select_constructor_projection(
              environment, constructor_symbol, symbol, arguments,
            )
          },
        ) {
        Some(selected) => selected
        None =>
          @logic.Term::elaborated_apply(symbol, [argument], term.ty(), None)
      }
    }
    Tapp(symbol, instantiations, arguments) =>
      match
        unfold_inlineable_logic_application(
          environment, symbol, instantiations, arguments,
        ) {
        Some(unfolded) =>
          eval_match_with(environment, keep_trace, stop, bindings, unfolded)
        None =>
          @logic.Term::elaborated_apply(
            symbol,
            arguments.map(recurse),
            term.ty(),
            None,
          )
      }
    Tif(condition, yes, no) =>
      @logic.Term::if_then_else(
        recurse(condition),
        recurse(yes),
        recurse(no),
        None,
      )
    Tlet(variable, value, body) => {
      let value = recurse(value)
      let body = match value.view() {
        Tif(predicate, yes, no) if yes == environment.boolean_true &&
          no == environment.boolean_false =>
          rewrite_boolean_tests(environment, body, variable, predicate)
        _ => body
      }
      let nested = bindings.copy()
      nested[variable] = value
      let_simplified_symbol(
        environment.context,
        variable,
        value,
        eval_match_with(environment, keep_trace, stop, nested, body),
        keep_trace && relevant_for_counterexample(variable),
      )
    }
    Tcase(scrutinee, branches) => {
      let scrutinee = recurse(scrutinee)
      match
        dive_to_eval_match_constructor(
          environment,
          keep_trace,
          bindings,
          scrutinee,
          (_, constructor_term, _, _) => {
            flatten_eval_match_case(environment, constructor_term, branches)
          },
        ) {
        Some(flattened) =>
          eval_match_with(environment, keep_trace, stop, bindings, flattened)
        None =>
          @logic.Term::case(
            scrutinee,
            branches.map(branch => {
              let view = branch.view()
              (view.pattern, recurse(view.body))
            }),
            None,
          )
      }
    }
    Teps(variable, body) => @logic.Term::epsilon(variable, recurse(body), None)
    Tquant(quantifier, binders, triggers, body) => {
      let retained : Array[@logic.VSymbol] = []
      let mut triggers = triggers.to_owned()
      let mut body = body
      for binder in binders {
        let (expanded, expanded_triggers, expanded_body) = if stop &&
          !binder.view().origin
          .attributes()
          .any(attribute => attribute == b"vc:break_me") {
          ([binder], triggers, body)
        } else {
          add_quantified_match_variable(environment, binder, triggers, body, 0)
        }
        for variable in expanded {
          retained.push(variable)
        }
        triggers = expanded_triggers
        body = expanded_body
      }
      body = eval_match_with(environment, keep_trace, stop, bindings, body)
      let free = body.free_variables()
      let used : Array[@logic.VSymbol] = []
      for binder in retained {
        if free.any(variable => variable == binder) {
          used.push(binder)
        }
      }
      @logic.Term::quantify(
        quantifier,
        used,
        retain_quantifier_triggers(used, body, triggers),
        body,
        None,
      )
    }
    Tbinop(operator, left, right) =>
      @logic.Term::binary(operator, recurse(left), recurse(right), None)
  }
  copy_term_decoration(term, replacement)
}

///|
fn eval_match(
  environment : VcEnvironment,
  keep_trace : Bool,
  term : @logic.Term,
) -> @logic.Term raise {
  eval_match_with(environment, keep_trace, false, Map([]), term)
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
