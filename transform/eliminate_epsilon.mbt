// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn is_highord_application(symbol : @logic.LSymbol) -> Bool {
  guard symbol.view().origin.snapshot_key() is Some(key) else { return false }
  let view = key.view()
  view.theory_key == b"why3.HighOrd.HighOrd" &&
  view.theory_item_ordinal == 1U &&
  view.declaration_inner_ordinal == 0U &&
  view.symbol_kind == Logic
}

///|
fn is_boolean_true(term : @logic.Term) -> Bool {
  guard term.view() is Tapp(symbol, _, arguments) && arguments.is_empty() else {
    return false
  }
  guard symbol.view().origin.snapshot_key() is Some(key) else { return false }
  let view = key.view()
  view.theory_key == b"why3.Bool.Bool" &&
  view.theory_item_ordinal == 0U &&
  view.declaration_inner_ordinal == 1U &&
  view.symbol_kind == Logic
}

///|
fn disjoint_from_binders(
  term : @logic.Term,
  binders : ArrayView[@logic.VSymbol],
) -> Bool {
  let forbidden : Map[@logic.VSymbol, Unit] = Map([])
  for binder in binders {
    forbidden[binder] = ()
  }
  term.free_variables().all(variable => !forbidden.contains(variable))
}

///|
fn partial_arguments_are_canonical(
  arguments : ArrayView[@logic.Term],
  binders_reversed : ArrayView[@logic.VSymbol],
  all_binders : ArrayView[@logic.VSymbol],
) -> Bool {
  if arguments.length() < binders_reversed.length() {
    return false
  }
  for index, binder in binders_reversed {
    let argument = arguments[arguments.length() - index - 1]
    if !(argument.view() is Tvar(variable) && variable == binder) {
      return false
    }
  }
  let retained = arguments.length() - binders_reversed.length()
  for index = 0; index < retained; index = index + 1 {
    if !disjoint_from_binders(arguments[index], all_binders) {
      return false
    }
  }
  true
}

///|
fn epsilon_expression_matches(
  term : @logic.Term,
  index : Int,
  reversed : ArrayView[@logic.VSymbol],
) -> Bool {
  if index == reversed.length() {
    return disjoint_from_binders(term, reversed)
  }
  if index + 1 == reversed.length() &&
    term.view() is Tvar(found) &&
    found == reversed[index] {
    return true
  }
  match term.view() {
    Tapp(symbol, _, arguments) if is_highord_application(symbol) &&
      arguments.length() == 2 &&
      arguments[1].view() is Tvar(found) &&
      found == reversed[index] =>
      epsilon_expression_matches(arguments[0], index + 1, reversed)
    Tapp(_, _, arguments) =>
      partial_arguments_are_canonical(arguments, reversed[index:], reversed)
    _ => false
  }
}

///|
fn epsilon_head_matches(
  term : @logic.Term,
  index : Int,
  reversed : ArrayView[@logic.VSymbol],
  variable : @logic.VSymbol,
) -> Bool {
  if index == reversed.length() {
    return term.view() is Tvar(found) && found == variable
  }
  match term.view() {
    Tapp(symbol, _, arguments) if is_highord_application(symbol) &&
      arguments.length() == 2 &&
      arguments[1].view() is Tvar(found) &&
      found == reversed[index] =>
      epsilon_head_matches(arguments[0], index + 1, reversed, variable)
    _ => false
  }
}

///|
fn canonical_epsilon_body(
  variable : @logic.VSymbol,
  formula : @logic.Term,
) -> Bool {
  let (binders, formula) = match formula.view() {
    Tquant(ForallQuantifier, binders, _, body) => (binders, body)
    _ => ([][:], formula)
  }
  let (head, expression) = match formula.view() {
    Tapp(symbol, _, arguments) if is_builtin_equality(symbol) &&
      arguments.length() == 2 => (arguments[0], arguments[1])
    Tbinop(Iff, left, right) => {
      guard left.view() is Tapp(symbol, _, arguments) &&
        is_builtin_equality(symbol) &&
        arguments.length() == 2 &&
        is_boolean_true(arguments[1]) else {
        return false
      }
      let expression = match right.view() {
        Tapp(right_symbol, _, right_arguments) if is_builtin_equality(
            right_symbol,
          ) &&
          right_arguments.length() == 2 &&
          is_boolean_true(right_arguments[1]) => right_arguments[0]
        _ => right
      }
      (arguments[0], expression)
    }
    _ => return false
  }
  let reversed = [
    for index = 0; index < binders.length(); index = index + 1 => {
      binders[binders.length() - index - 1]
    }
  ]
  if !epsilon_expression_matches(expression, 0, reversed) {
    return false
  }
  epsilon_head_matches(head, 0, reversed, variable)
}

///|
fn eliminate_epsilon_term(
  context : @identity.CompilationContext,
  term : @logic.Term,
) -> @logic.Term raise TransformError {
  let stage = @identity.EliminateEpsilon
  match term.view() {
    Tapp(symbol, _, arguments) if is_builtin_equality(symbol) &&
      arguments.length() == 2 => {
      let rewrite = fn(
        other : @logic.Term,
        epsilon : @logic.Term,
      ) -> @logic.Term? raise TransformError {
        guard epsilon.view() is Teps(variable, formula) else { return None }
        if canonical_epsilon_body(variable, formula) {
          fail_transform(
            UnsupportedStructure,
            stage,
            "canonical lambda epsilon is outside the Stage-07 narrow path",
          )
        }
        let substituted = let_simplified(
          context, variable, other, formula, false, stage,
        )
        Some(
          copy_term_decoration(
            term,
            eliminate_epsilon_term(context, substituted),
          ),
        )
      }
      match rewrite(arguments[0], arguments[1]) {
        Some(result) => result
        None =>
          match rewrite(arguments[1], arguments[0]) {
            Some(result) => result
            None => {
              let recurse = fn(child) -> @logic.Term raise TransformError {
                eliminate_epsilon_term(context, child)
              }
              map_plain(term, recurse, stage)
            }
          }
      }
    }
    Teps(_, _) =>
      fail_transform(
        UnsupportedStructure,
        stage,
        "standalone epsilon is outside the Stage-07 narrow path",
      )
    _ => {
      let recurse = fn(child) -> @logic.Term raise TransformError {
        eliminate_epsilon_term(context, child)
      }
      map_plain(term, recurse, stage)
    }
  }
}

///|
fn eliminate_epsilon_definition(
  context : @identity.CompilationContext,
  definition : @logic.LogicDefinition,
) -> @logic.LogicDefinition raise TransformError {
  let stage = @identity.EliminateEpsilon
  let view = definition.view()
  let body = eliminate_epsilon_term(context, view.body)
  match view.symbol.view().origin.kind().view() {
    SnapshotKind =>
      @logic.LogicDefinition::trusted_recursive(
        context,
        view.symbol,
        view.parameters,
        body,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "invalid trusted epsilon definition",
          )
      }
    UserKind | GeneratedKind(_) =>
      @logic.LogicDefinition::new(
        context,
        view.symbol,
        view.parameters,
        body,
        None,
      ) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "invalid epsilon definition")
      }
  }
}

///|
fn eliminate_epsilon_declaration(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
) -> @logic.Decl raise TransformError {
  let stage = @identity.EliminateEpsilon
  match declaration.view() {
    Dtype(_) | Ddata(_) | Dparam(_) => declaration
    Dind(_) =>
      fail_transform(
        UnsupportedStructure,
        stage,
        "inductive declaration survived its slot",
      )
    Dlogic(definitions) => {
      let mapped = [
        for definition in definitions => {
          eliminate_epsilon_definition(context, definition)
        }
      ]
      match declaration.origin().kind().view() {
        SnapshotKind =>
          @logic.Decl::trusted_logic(
            context,
            declaration.origin(),
            mapped,
            None,
          ) catch {
            _ =>
              fail_transform(
                InvariantFailure,
                stage,
                "invalid trusted epsilon group",
              )
          }
        UserKind | GeneratedKind(_) =>
          @logic.Decl::logic(context, declaration.origin(), mapped, None) catch {
            _ =>
              fail_transform(InvariantFailure, stage, "invalid epsilon group")
          }
      }
    }
    Dprop(kind, proposition, formula) =>
      @logic.Decl::proposition(
        context,
        declaration.origin(),
        kind,
        proposition,
        eliminate_epsilon_term(context, formula),
        None,
      ) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "invalid epsilon proposition")
      }
  }
}

///|
pub fn eliminate_epsilon(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.EliminateEpsilon
  require_task_context(context, task, stage)
  let items : Array[@theory.TheoryItem] = []
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) =>
        items.push(
          TheoryDecl(eliminate_epsilon_declaration(context, declaration)),
        )
      TheoryUse(_) | TheoryClone(_) | TheoryMeta(_) => items.push(item)
    }
  }
  checked_task(task.context_anchor(), items, stage)
}
