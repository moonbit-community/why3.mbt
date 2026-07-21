// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
let asym_split_attribute : Bytes = b"asym_split"

///|
let unused_attribute : Bytes = b"id:unused"

///|
fn derived_generated_span(origin : @identity.Origin) -> @identity.SourceSpan? {
  match origin.kind().view() {
    SnapshotKind => None
    UserKind | GeneratedKind(_) => origin.source_span()
  }
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
  let origin = @identity.Origin::generated(
    stage,
    name,
    derived_generated_span(view.origin),
    [unused_attribute],
  )
  @logic.VSymbol::new(context, name, origin, view.ty, None) catch {
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
  guard symbol.view().origin.snapshot_key() is Some(key) else { return false }
  let view = key.view()
  view.theory_key == b"why3.BuiltIn.BuiltIn" &&
  view.theory_item_ordinal == 3U &&
  view.declaration_inner_ordinal == 0U &&
  view.symbol_kind == Logic
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
      @logic.Term::trusted_case(recurse(scrutinee), mapped, None) catch {
        _ => fail_transform(InvariantFailure, stage, "invalid mapped case")
      }
    }
    Teps(variable, body) =>
      @logic.Term::trusted_epsilon(variable, recurse(body), None) catch {
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
    Tquant(quantifier, binders, triggers, body) => {
      let mapped_triggers = [
        for group in triggers => [ for trigger in group => recurse(trigger) ]
      ]
      quantifier_simplified(
        quantifier,
        binders,
        mapped_triggers,
        recurse(body),
        stage,
      )
    }
    Tbinop(operator, left, right) =>
      binary_simplified(operator, recurse(left), recurse(right), stage)
    Tnot(inner) => not_simplified(recurse(inner))
    _ => return map_plain(term, recurse, stage)
  }
  copy_term_decoration(term, replacement)
}
