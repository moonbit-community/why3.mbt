// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn origin_has_attribute(
  origin : @identity.Origin,
  attribute : BytesView,
) -> Bool {
  origin.attributes().any(value => value[:] == attribute)
}

///|
fn unused_equality_operand(term : @logic.Term) -> Bool {
  match term.view() {
    Tvar(variable) =>
      origin_has_attribute(variable.view().origin, unused_attribute)
    Tapp(symbol, _, arguments) =>
      arguments.is_empty() &&
      origin_has_attribute(symbol.view().origin, unused_attribute)
    _ => false
  }
}

///|
fn remove_unused_in_term(
  context : @identity.CompilationContext,
  polarity : Bool,
  term : @logic.Term,
) -> @logic.Term raise TransformError {
  let stage = @identity.CounterexamplesDependentIntros
  let recurse_same = fn(child) -> @logic.Term raise TransformError {
    remove_unused_in_term(context, polarity, child)
  }
  let replacement = match term.view() {
    Tbinop(Implies, left, right) =>
      binary_simplified(
        Implies,
        remove_unused_in_term(context, !polarity, left),
        remove_unused_in_term(context, polarity, right),
        stage,
      )
    Tbinop(Iff, left, right) => {
      let left_positive = remove_unused_in_term(context, polarity, left)
      let left_negative = remove_unused_in_term(context, !polarity, left)
      let right_positive = remove_unused_in_term(context, polarity, right)
      let right_negative = remove_unused_in_term(context, !polarity, right)
      if left_positive == left_negative && right_positive == right_negative {
        binary_simplified(Iff, left_positive, right_positive, stage)
      } else if polarity {
        binary_simplified(
          And,
          binary_simplified(Implies, left_negative, right_positive, stage),
          binary_simplified(Implies, right_negative, left_positive, stage),
          stage,
        )
      } else {
        binary_simplified(
          Implies,
          binary_simplified(Or, left_negative, right_negative, stage),
          binary_simplified(And, left_positive, right_positive, stage),
          stage,
        )
      }
    }
    Tnot(inner) =>
      not_simplified(remove_unused_in_term(context, !polarity, inner))
    Tlet(variable, value, body) => {
      let mapped_body = map_simplified(
        context, body, recurse_same, false, stage,
      )
      if origin_has_attribute(variable.view().origin, unused_attribute) {
        mapped_body
      } else {
        let_simplified(context, variable, value, mapped_body, true, stage)
      }
    }
    Tapp(symbol, _, arguments) if is_builtin_equality(symbol) &&
      arguments.length() == 2 &&
      unused_equality_operand(arguments[0]) =>
      if polarity {
        @logic.Term::false_formula()
      } else {
        @logic.Term::true_formula()
      }
    Tif(condition, then_branch, else_branch) if term.is_formula() => {
      let condition_positive = remove_unused_in_term(
        context, polarity, condition,
      )
      let condition_negative = remove_unused_in_term(
        context,
        !polarity,
        condition,
      )
      let then_branch = remove_unused_in_term(context, polarity, then_branch)
      let else_branch = remove_unused_in_term(context, polarity, else_branch)
      if condition_positive == condition_negative {
        if_simplified(condition_positive, then_branch, else_branch, stage)
      } else if polarity {
        binary_simplified(
          And,
          binary_simplified(Implies, condition_negative, then_branch, stage),
          binary_simplified(
            Implies,
            not_simplified(condition_positive),
            else_branch,
            stage,
          ),
          stage,
        )
      } else {
        binary_simplified(
          Or,
          binary_simplified(And, condition_positive, then_branch, stage),
          binary_simplified(
            And,
            not_simplified(condition_negative),
            else_branch,
            stage,
          ),
          stage,
        )
      }
    }
    Tif(_, _, _) | Teps(_, _) => term
    _ => map_simplified(context, term, recurse_same, false, stage)
  }
  copy_term_decoration(term, replacement)
}

///|
fn counterexample_decl(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
) -> @logic.Decl? raise TransformError {
  match declaration.view() {
    Dparam(symbol) if origin_has_attribute(
        symbol.view().origin,
        unused_attribute,
      ) => None
    Dlogic(definitions) if definitions.length() == 1 &&
      origin_has_attribute(
        definitions[0].view().symbol.view().origin,
        unused_attribute,
      ) => None
    Dprop(kind, proposition, formula) => {
      let polarity = match kind {
        Pgoal => true
        Paxiom => false
        Plemma =>
          return fail_transform(
            InvariantFailure,
            @identity.CounterexamplesDependentIntros,
            "Task contains an unclassified lemma",
          )
      }
      let mapped = remove_unused_in_term(context, polarity, formula)
      Some(
        @logic.Decl::proposition(
          context,
          declaration.origin(),
          kind,
          proposition,
          mapped,
          None,
        ),
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.CounterexamplesDependentIntros,
            "cannot rebuild proposition",
          )
      }
    }
    Dtype(_) | Ddata(_) | Dparam(_) | Dlogic(_) | Dind(_) => Some(declaration)
  }
}

///|
pub fn counterexamples_dependent_intros(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.CounterexamplesDependentIntros
  require_task_context(context, task, stage)
  let items : Array[@theory.TheoryItem] = []
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) =>
        if counterexample_decl(context, declaration) is Some(mapped) {
          items.push(TheoryDecl(mapped))
        }
      TheoryUse(_) | TheoryClone(_) | TheoryMeta(_) => items.push(item)
    }
  }
  checked_task(task.context_anchor(), items, stage)
}
