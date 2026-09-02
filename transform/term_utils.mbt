// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
let asym_split_attribute : Bytes = b"asym_split"

///|
let unused_attribute : Bytes = b"id:unused"

///|
fn bytes_have_prefix(value : BytesView, prefix : BytesView) -> Bool {
  value.length() >= prefix.length() && value[:prefix.length()] == prefix
}

///|
fn derived_generated_span(origin : @identity.Origin) -> @identity.SourceSpan? {
  guard origin.identifier_source_span() is Some(span) else { return None }
  if bytes_have_prefix(span.view().relative_path, b"why3-1.7.2/stdlib/") {
    None
  } else {
    Some(span)
  }
}

///|
fn derived_generated_attributes(origin : @identity.Origin) -> Array[Bytes] {
  let attributes = origin.attributes()
  let has_synthetic_builtin = attributes.any(attribute => {
    bytes_have_prefix(attribute, b"why3:builtin:")
  })
  if !has_synthetic_builtin {
    return attributes.to_owned()
  }
  [
    for attribute in attributes if attribute != b"builtin" &&
    !bytes_have_prefix(attribute, b"why3:builtin:") => attribute
  ]
}

///|
fn derived_generated_origin(
  stage : @identity.GeneratedStage,
  name : BytesView,
  parent : @identity.Origin,
  attributes : ArrayView[Bytes],
) -> @identity.Origin {
  @identity.Origin::generated_with_identifier_source_span(
    stage,
    name,
    derived_generated_span(parent),
    parent.identifier_source_span(),
    attributes,
  )
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
fn remove_term_attribute(
  term : @logic.Term,
  unwanted : BytesView,
) -> @logic.Term {
  if !term.attributes().any(attribute => attribute[:] == unwanted) {
    return term
  }
  let attributes = [
    for attribute in term.attributes() if attribute[:] != unwanted => attribute
  ]
  term.source_decorate(term.source_span(), attributes)
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
fn not_simplified(term : @logic.Term) -> @logic.Term raise TransformError {
  match term.view() {
    Ttrue => copy_term_decoration(term, @logic.Term::false_formula())
    Tfalse => copy_term_decoration(term, @logic.Term::true_formula())
    Tnot(inner) => copy_term_decoration(term, inner)
    _ =>
      @logic.Term::not(term, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.SimplifyFormula,
            "not simplification received a value term",
          )
      }
  }
}

///|
fn without_asym_split(term : @logic.Term) -> @logic.Term {
  remove_term_attribute(term, asym_split_attribute)
}

///|
fn binary_simplified(
  operator : @logic.BinaryLogicOp,
  left : @logic.Term,
  right : @logic.Term,
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  match operator {
    And =>
      if is_true(left) {
        right
      } else if is_true(right) || is_false(left) {
        without_asym_split(left)
      } else if is_false(right) {
        right
      } else if left == right {
        left
      } else {
        @logic.Term::binary(And, left, right, None) catch {
          _ => fail_transform(InvariantFailure, stage, "invalid conjunction")
        }
      }
    Or =>
      if is_true(left) {
        without_asym_split(left)
      } else if is_true(right) {
        right
      } else if is_false(left) {
        right
      } else if is_false(right) {
        without_asym_split(left)
      } else if left == right {
        left
      } else {
        @logic.Term::binary(Or, left, right, None) catch {
          _ => fail_transform(InvariantFailure, stage, "invalid disjunction")
        }
      }
    Implies =>
      if is_true(left) || is_true(right) {
        right
      } else if is_false(left) {
        copy_term_decoration(left, @logic.Term::true_formula())
      } else if is_false(right) {
        not_simplified(left)
      } else if left == right {
        copy_term_decoration(left, @logic.Term::true_formula())
      } else {
        @logic.Term::binary(Implies, left, right, None) catch {
          _ => fail_transform(InvariantFailure, stage, "invalid implication")
        }
      }
    Iff =>
      if is_true(left) {
        right
      } else if is_true(right) {
        left
      } else if is_false(left) {
        not_simplified(right)
      } else if is_false(right) {
        not_simplified(left)
      } else if left == right {
        copy_term_decoration(left, @logic.Term::true_formula())
      } else {
        @logic.Term::binary(Iff, left, right, None) catch {
          _ => fail_transform(InvariantFailure, stage, "invalid equivalence")
        }
      }
  }
}

///|
fn and_asym_simplified(
  left : @logic.Term,
  right : @logic.Term,
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  if is_true(left) {
    right
  } else if is_true(right) || is_false(left) {
    without_asym_split(left)
  } else if is_false(right) {
    right
  } else if left == right {
    left
  } else {
    let asymmetric = left.add_attributes([asym_split_attribute])
    @logic.Term::binary(And, asymmetric, right, None) catch {
      _ => fail_transform(InvariantFailure, stage, "invalid asymmetric and")
    }
  }
}

///|
fn if_simplified(
  condition : @logic.Term,
  then_branch : @logic.Term,
  else_branch : @logic.Term,
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  if is_true(condition) {
    then_branch
  } else if is_false(condition) {
    else_branch
  } else if is_true(then_branch) {
    binary_simplified(Implies, not_simplified(condition), else_branch, stage)
  } else if is_false(then_branch) {
    and_asym_simplified(not_simplified(condition), else_branch, stage)
  } else if is_true(else_branch) {
    binary_simplified(Implies, condition, then_branch, stage)
  } else if is_false(else_branch) {
    and_asym_simplified(condition, then_branch, stage)
  } else if then_branch == else_branch {
    then_branch
  } else {
    @logic.Term::if_then_else(condition, then_branch, else_branch, None) catch {
      _ => fail_transform(InvariantFailure, stage, "invalid if term")
    }
  }
}

///|
fn variable_occurrences(term : @logic.Term, target : @logic.VSymbol) -> Int {
  let mut count = 0
  let visit = fn(child) { count = count + variable_occurrences(child, target) }
  match term.view() {
    Tvar(variable) => if variable == target { count = 1 }
    Tconst(_) | Ttrue | Tfalse => ()
    Tapp(_, _, arguments) =>
      for argument in arguments {
        visit(argument)
      }
    Tif(condition, then_branch, else_branch) => {
      visit(condition)
      visit(then_branch)
      visit(else_branch)
    }
    Tlet(_, value, body) => {
      visit(value)
      visit(body)
    }
    Tcase(scrutinee, branches) => {
      visit(scrutinee)
      for branch in branches {
        visit(branch.view().body)
      }
    }
    Teps(_, body) => visit(body)
    Tquant(_, _, triggers, body) => {
      for group in triggers {
        for trigger in group {
          visit(trigger)
        }
      }
      visit(body)
    }
    Tbinop(_, left, right) => {
      visit(left)
      visit(right)
    }
    Tnot(inner) => visit(inner)
  }
  count
}

///|
fn small_term(term : @logic.Term) -> Bool {
  match term.view() {
    Tvar(_) | Tconst(_) => true
    _ => false
  }
}

///|
fn substitute_one(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  replacement : @logic.Term,
  body : @logic.Term,
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  @logic.TermSubstitution::new()
  .bind(variable, replacement, None)
  .apply(context, body, None) catch {
    _ => fail_transform(InvariantFailure, stage, "invalid term substitution")
  }
}

///|
fn unused_copy(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  stage : @identity.GeneratedStage,
) -> @logic.VSymbol raise TransformError {
  let view = variable.view()
  let name = view.name + b"'unused"
  let origin = derived_generated_origin(stage, name, view.origin, [
    unused_attribute,
  ])
  variable.clone_as(context, name, origin, view.ty, None) catch {
    _ => fail_transform(InvariantFailure, stage, "cannot copy unused binder")
  }
}

///|
fn let_simplified(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  value : @logic.Term,
  body : @logic.Term,
  keep_variable : Bool,
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  let occurrences = variable_occurrences(body, variable)
  if occurrences == 0 {
    if !keep_variable {
      return body
    }
    let unused = unused_copy(context, variable, stage)
    return @logic.Term::let_in(unused, value, body, None) catch {
      _ => fail_transform(InvariantFailure, stage, "invalid unused let")
    }
  }
  if occurrences == 1 || small_term(value) {
    let substituted = substitute_one(context, variable, value, body, stage)
    if !keep_variable {
      return substituted
    }
    let unused = unused_copy(context, variable, stage)
    return @logic.Term::let_in(unused, value, substituted, None) catch {
      _ => fail_transform(InvariantFailure, stage, "invalid retained let")
    }
  }
  @logic.Term::let_in(variable, value, body, None) catch {
    _ => fail_transform(InvariantFailure, stage, "invalid let term")
  }
}

///|
fn is_builtin_equality(symbol : @logic.LSymbol) -> Bool {
  symbol.view().origin
  .attributes()
  .any(attribute => attribute == b"why3:builtin:equality")
}

///|
fn equality_simplified(left : @logic.Term, right : @logic.Term) -> @logic.Term? {
  if left == right {
    Some(@logic.Term::true_formula())
  } else {
    None
  }
}

///|
fn free_variable_set(term : @logic.Term) -> Map[@logic.VSymbol, Unit] {
  let result : Map[@logic.VSymbol, Unit] = Map([])
  for variable in term.free_variables() {
    result[variable] = ()
  }
  result
}

///|
fn quantifier_simplified(
  quantifier : @logic.Quantifier,
  binders : ArrayView[@logic.VSymbol],
  triggers : ArrayView[Array[@logic.Term]],
  body : @logic.Term,
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  let free = free_variable_set(body)
  if binders.all(variable => free.contains(variable)) {
    return @logic.Term::quantify(quantifier, binders, triggers, body, None) catch {
      _ => fail_transform(InvariantFailure, stage, "invalid quantifier")
    }
  }
  let retained = [
    for variable in binders if free.contains(variable) => variable
  ]
  if retained.is_empty() {
    return body
  }
  let filtered : Array[Array[@logic.Term]] = []
  for group in triggers {
    if group.all(trigger => {
        trigger.free_variables().all(variable => free.contains(variable))
      }) {
      filtered.push(group.copy())
    }
  }
  @logic.Term::quantify(quantifier, retained, filtered, body, None) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "invalid simplified quantifier")
  }
}

///|
/// Replaces the presentation identifiers of opened binders while preserving
/// their semantic identities. Why3 opens quantified closures with `id_clone`;
/// when the mapped body changes, those cloned identifiers survive reclosing
/// and can later become observable through a persistent declaration cache.
fn substitute_opened_identifier_clones(
  term : @logic.Term,
  substitution : Map[@logic.VSymbol, @logic.VSymbol],
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  let recurse = fn(child) -> @logic.Term raise TransformError {
    substitute_opened_identifier_clones(child, substitution, stage)
  }
  match term.view() {
    Tvar(variable) =>
      match substitution.get(variable) {
        Some(replacement) =>
          copy_term_decoration(term, @logic.Term::variable(replacement))
        None => term
      }
    _ => map_plain(term, recurse, stage)
  }
}

///|
fn strict_term_groups_equal(
  left : ArrayView[Array[@logic.Term]],
  right : ArrayView[Array[@logic.Term]],
) -> Bool {
  if left.length() != right.length() {
    return false
  }
  for group_index, left_group in left {
    let right_group = right[group_index]
    if left_group.length() != right_group.length() {
      return false
    }
    for term_index, left_term in left_group {
      if !left_term.strict_alpha_equivalent(right_group[term_index]) {
        return false
      }
    }
  }
  true
}

///|
fn open_simplified_quantifier(
  context : @identity.CompilationContext,
  quantifier : @logic.Quantifier,
  binders : ArrayView[@logic.VSymbol],
  triggers : ArrayView[Array[@logic.Term]],
  body : @logic.Term,
  recurse : (@logic.Term) -> @logic.Term raise TransformError,
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  let opened_binders : Array[@logic.VSymbol] = []
  let substitution : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
  for binder in binders {
    let opened = binder.clone_identifier(context, None) catch {
      _ =>
        return fail_transform(
          InvariantFailure,
          stage,
          "cannot open simplified quantified binder",
        )
    }
    opened_binders.push(opened)
    substitution[binder] = opened
  }
  let opened_triggers = [
    for group in triggers => {
      [
        for trigger in group => {
          substitute_opened_identifier_clones(trigger, substitution, stage)
        }
      ]
    }
  ]
  let mapped_triggers = [
    for group in opened_triggers => [ for trigger in group => recurse(trigger) ]
  ]
  let opened_body = substitute_opened_identifier_clones(
    body, substitution, stage,
  )
  let mapped_body = recurse(opened_body)
  let free = free_variable_set(mapped_body)
  let removes_binder = binders.any(binder => !free.contains(binder))
  if !removes_binder &&
    mapped_body.strict_alpha_equivalent(opened_body) &&
    strict_term_groups_equal(mapped_triggers, opened_triggers) {
    return @logic.Term::quantify(quantifier, binders, triggers, body, None) catch {
      _ =>
        fail_transform(
          InvariantFailure,
          stage,
          "cannot preserve unchanged quantified term",
        )
    }
  }
  quantifier_simplified(
    quantifier, opened_binders, mapped_triggers, mapped_body, stage,
  )
}

///|
fn map_plain(
  term : @logic.Term,
  recurse : (@logic.Term) -> @logic.Term raise TransformError,
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  let replacement = match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => term
    Tapp(symbol, _, arguments) => {
      let mapped = [ for argument in arguments => recurse(argument) ]
      @logic.Term::elaborated_apply(symbol, mapped, term.ty(), None) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "invalid mapped application")
      }
    }
    Tif(condition, then_branch, else_branch) =>
      @logic.Term::if_then_else(
        recurse(condition),
        recurse(then_branch),
        recurse(else_branch),
        None,
      ) catch {
        _ => fail_transform(InvariantFailure, stage, "invalid mapped if")
      }
    Tlet(variable, value, body) =>
      @logic.Term::let_in(variable, recurse(value), recurse(body), None) catch {
        _ => fail_transform(InvariantFailure, stage, "invalid mapped let")
      }
    Tcase(scrutinee, branches) => {
      let mapped = [
        for branch in branches => {
          let view = branch.view()
          (view.pattern, recurse(view.body))
        }
      ]
      @logic.Term::case(recurse(scrutinee), mapped, None) catch {
        _ => fail_transform(InvariantFailure, stage, "invalid mapped case")
      }
    }
    Teps(variable, body) =>
      @logic.Term::epsilon(variable, recurse(body), None) catch {
        _ => fail_transform(InvariantFailure, stage, "invalid mapped epsilon")
      }
    Tquant(quantifier, binders, triggers, body) => {
      let mapped_triggers = [
        for group in triggers => [ for trigger in group => recurse(trigger) ]
      ]
      @logic.Term::quantify(
        quantifier,
        binders,
        mapped_triggers,
        recurse(body),
        None,
      ) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "invalid mapped quantifier")
      }
    }
    Tbinop(operator, left, right) =>
      @logic.Term::binary(operator, recurse(left), recurse(right), None) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "invalid mapped binary term")
      }
    Tnot(inner) =>
      @logic.Term::not(recurse(inner), None) catch {
        _ => fail_transform(InvariantFailure, stage, "invalid mapped negation")
      }
  }
  copy_term_decoration(term, replacement)
}

///|
fn map_simplified(
  context : @identity.CompilationContext,
  term : @logic.Term,
  recurse : (@logic.Term) -> @logic.Term raise TransformError,
  keep_let_variable : Bool,
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  let replacement = match term.view() {
    Tapp(symbol, _, arguments) if is_builtin_equality(symbol) &&
      arguments.length() == 2 => {
      let left = recurse(arguments[0])
      let right = recurse(arguments[1])
      match equality_simplified(left, right) {
        Some(simplified) => simplified
        None =>
          @logic.Term::elaborated_apply(symbol, [left, right], term.ty(), None) catch {
            _ => fail_transform(InvariantFailure, stage, "invalid equality")
          }
      }
    }
    Tif(condition, then_branch, else_branch) =>
      if_simplified(
        recurse(condition),
        recurse(then_branch),
        recurse(else_branch),
        stage,
      )
    Tlet(variable, value, body) =>
      let_simplified(
        context,
        variable,
        recurse(value),
        recurse(body),
        keep_let_variable,
        stage,
      )
    Tquant(quantifier, binders, triggers, body) =>
      open_simplified_quantifier(
        context, quantifier, binders, triggers, body, recurse, stage,
      )
    Tbinop(operator, left, right) =>
      binary_simplified(operator, recurse(left), recurse(right), stage)
    Tnot(inner) => not_simplified(recurse(inner))
    _ => return map_plain(term, recurse, stage)
  }
  copy_term_decoration(term, replacement)
}
