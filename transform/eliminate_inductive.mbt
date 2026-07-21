// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn raw_binary(
  operator : @logic.BinaryLogicOp,
  left : @logic.Term,
  right : @logic.Term,
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  @logic.Term::binary(operator, left, right, None) catch {
    _ => fail_transform(InvariantFailure, stage, "invalid inductive formula")
  }
}

///|
fn raw_equality(
  equality : @logic.LSymbol,
  left : @logic.Term,
  right : @logic.Term,
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  @logic.Term::elaborated_apply(equality, [left, right], None, None) catch {
    _ => fail_transform(InvariantFailure, stage, "invalid inductive equality")
  }
}

///|
fn replacement_uses_bound_variable(
  bound : Map[@logic.VSymbol, Unit],
  term : @logic.Term,
) -> Bool {
  term.free_variables().any(variable => bound.contains(variable))
}

///|
fn find_quantifier_substitution(
  equality : @logic.LSymbol,
  bound : Map[@logic.VSymbol, Unit],
  variable : @logic.VSymbol,
  positive : Bool,
  formula : @logic.Term,
) -> @logic.Term? {
  let candidate = fn(left : @logic.Term, right : @logic.Term) -> @logic.Term? {
    if positive &&
      left.view() is Tvar(found) &&
      found == variable &&
      left != right &&
      !replacement_uses_bound_variable(bound, right) {
      Some(right)
    } else {
      None
    }
  }
  match formula.view() {
    Tapp(symbol, _, arguments) if symbol == equality && arguments.length() == 2 =>
      match candidate(arguments[0], arguments[1]) {
        Some(term) => Some(term)
        None => candidate(arguments[1], arguments[0])
      }
    Tbinop(Or, left, right) if !positive =>
      match
        find_quantifier_substitution(equality, bound, variable, positive, left) {
        Some(term) => Some(term)
        None =>
          find_quantifier_substitution(
            equality, bound, variable, positive, right,
          )
      }
    Tbinop(And, left, right) if positive =>
      match
        find_quantifier_substitution(equality, bound, variable, positive, left) {
        Some(term) => Some(term)
        None =>
          find_quantifier_substitution(
            equality, bound, variable, positive, right,
          )
      }
    Tbinop(Implies, left, right) if !positive =>
      match
        find_quantifier_substitution(equality, bound, variable, true, left) {
        Some(term) => Some(term)
        None =>
          find_quantifier_substitution(equality, bound, variable, false, right)
      }
    Tnot(inner) =>
      find_quantifier_substitution(equality, bound, variable, !positive, inner)
    Tquant(_, binders, triggers, body) if triggers.is_empty() => {
      let nested = bound.copy()
      for binder in binders {
        nested[binder] = ()
      }
      find_quantifier_substitution(equality, nested, variable, positive, body)
    }
    Tlet(binder, _, body) => {
      let nested = bound.copy()
      nested[binder] = ()
      find_quantifier_substitution(equality, nested, variable, positive, body)
    }
    _ => None
  }
}

///|
fn simplify_selected_equalities(
  context : @identity.CompilationContext,
  equality : @logic.LSymbol,
  selected : (@logic.VSymbol, @logic.Term)?,
  formula : @logic.Term,
) -> @logic.Term raise TransformError {
  let stage = @identity.EliminateInductive
  let recurse = fn(child) -> @logic.Term raise TransformError {
    simplify_selected_equalities(context, equality, selected, child)
  }
  let replacement = match formula.view() {
    Tbinop(operator, left, right) => {
      let left = recurse(left)
      let right = recurse(right)
      match (operator, left.view(), right.view()) {
        (Or, Tfalse, _) | (And, Ttrue, _) | (Implies, Ttrue, _) => right
        (Or, _, Tfalse) | (And, _, Ttrue) => left
        _ => raw_binary(operator, left, right, stage)
      }
    }
    Tapp(symbol, _, arguments) if symbol == equality && arguments.length() == 2 => {
      let left = arguments[0]
      let right = arguments[1]
      let selected_equal = match selected {
        Some((variable, term)) =>
          (left.view() is Tvar(found) && found == variable && right == term) ||
          (right.view() is Tvar(found) && found == variable && left == term)
        None => false
      }
      if selected_equal {
        @logic.Term::true_formula()
      } else {
        let left = recurse(left)
        let right = recurse(right)
        match equality_simplified(left, right) {
          Some(result) => result
          None => raw_equality(equality, left, right, stage)
        }
      }
    }
    _ => {
      let mapped = fn(child) -> @logic.Term raise TransformError {
        recurse(child)
      }
      map_plain(formula, mapped, stage)
    }
  }
  copy_term_decoration(formula, replacement)
}

///|
fn simplify_quantifier_binders(
  context : @identity.CompilationContext,
  equality : @logic.LSymbol,
  binders : ArrayView[@logic.VSymbol],
  positive : Bool,
  formula : @logic.Term,
) -> (Array[@logic.VSymbol], @logic.Term) raise TransformError {
  let retained_reversed : Array[@logic.VSymbol] = []
  let mut result = formula
  for reverse_index = 0
      reverse_index < binders.length()
      reverse_index = reverse_index + 1 {
    let binder = binders[binders.length() - reverse_index - 1]
    if variable_occurrences(result, binder) == 0 {
      continue
    }
    let bound : Map[@logic.VSymbol, Unit] = Map([(binder, ())])
    match
      find_quantifier_substitution(equality, bound, binder, positive, result) {
      None => retained_reversed.push(binder)
      Some(replacement) => {
        result = substitute_one(
          context,
          binder,
          replacement,
          result,
          @identity.EliminateInductive,
        )
        result = simplify_selected_equalities(context, equality, None, result)
      }
    }
  }
  let retained = [
    for reverse_index = 0
        reverse_index < retained_reversed.length()
        reverse_index = reverse_index + 1 => {
      retained_reversed[retained_reversed.length() - reverse_index - 1]
    }
  ]
  (retained, result)
}

///|
fn remove_trivial_quantification(
  context : @identity.CompilationContext,
  equality : @logic.LSymbol,
  formula : @logic.Term,
) -> @logic.Term raise TransformError {
  let stage = @identity.EliminateInductive
  match formula.view() {
    Tquant(quantifier, binders, triggers, body) => {
      if !triggers.is_empty() {
        return formula
      }
      let positive = quantifier == ExistsQuantifier
      let (binders, body) = simplify_quantifier_binders(
        context, equality, binders, positive, body,
      )
      let body = remove_trivial_quantification(context, equality, body)
      let replacement = @logic.Term::quantify(
        quantifier,
        binders,
        [],
        body,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "invalid simplified quantifier",
          )
      }
      copy_term_decoration(formula, replacement)
    }
    _ => {
      let recurse = fn(child) -> @logic.Term raise TransformError {
        remove_trivial_quantification(context, equality, child)
      }
      map_plain(formula, recurse, stage)
    }
  }
}

///|
fn inversion_case(
  equality : @logic.LSymbol,
  formal_arguments : ArrayView[@logic.Term],
  formula : @logic.Term,
) -> @logic.Term raise TransformError {
  let stage = @identity.EliminateInductive
  match formula.view() {
    Tquant(ForallQuantifier, binders, triggers, body) =>
      @logic.Term::quantify(
        ExistsQuantifier,
        binders,
        triggers,
        inversion_case(equality, formal_arguments, body),
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "invalid inversion existential",
          )
      }
    Tbinop(Implies, premise, conclusion) =>
      raw_binary(
        And,
        premise,
        inversion_case(equality, formal_arguments, conclusion),
        stage,
      )
    Tapp(_, _, actual_arguments) => {
      if formal_arguments.length() != actual_arguments.length() {
        return fail_transform(
          InvariantFailure,
          stage,
          "inductive head has the wrong arity",
        )
      }
      let mut result = @logic.Term::true_formula()
      for index, formal in formal_arguments {
        result = binary_simplified(
          And,
          result,
          raw_equality(equality, formal, actual_arguments[index], stage),
          stage,
        )
      }
      result
    }
    Tlet(variable, value, body) =>
      @logic.Term::let_in(
        variable,
        value,
        inversion_case(equality, formal_arguments, body),
        None,
      ) catch {
        _ => fail_transform(InvariantFailure, stage, "invalid inversion let")
      }
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "invalid trusted inductive case shape",
      )
  }
}

///|
fn inversion_axiom(
  context : @identity.CompilationContext,
  equality : @logic.LSymbol,
  declaration : @logic.InductiveDeclaration,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.EliminateInductive
  let view = declaration.view()
  let predicate_view = view.predicate.view()
  let binders : Array[@logic.VSymbol] = []
  for ty in predicate_view.argument_types {
    let origin = @identity.Origin::generated(stage, b"z", None, [])
    binders.push(
      @logic.VSymbol::new(context, b"z", origin, ty, None) catch {
        _ => fail_transform(InvariantFailure, stage, "invalid inversion binder")
      },
    )
  }
  let arguments = [ for binder in binders => @logic.Term::variable(binder) ]
  let head = @logic.Term::apply_predicate(view.predicate, arguments, None) catch {
    _ => fail_transform(InvariantFailure, stage, "invalid inversion head")
  }
  guard !view.cases.is_empty() else {
    return fail_transform(
      InvariantFailure,
      stage,
      "empty inductive declaration",
    )
  }
  let mut cases = inversion_case(
    equality,
    arguments,
    view.cases[0].view().formula,
  )
  for index = 1; index < view.cases.length(); index = index + 1 {
    cases = raw_binary(
      Or,
      cases,
      inversion_case(equality, arguments, view.cases[index].view().formula),
      stage,
    )
  }
  let implication = raw_binary(Implies, head, cases, stage)
  let simplified = remove_trivial_quantification(context, equality, implication)
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    binders,
    [],
    simplified,
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "invalid inversion formula")
  }
  let name = predicate_view.name + b"_inversion"
  let origin = @identity.Origin::generated(
    stage,
    name,
    derived_generated_span(predicate_view.origin),
    predicate_view.origin.attributes(),
  )
  let proposition = @logic.PrSymbol::new(context, name, origin)
  let axiom = @logic.Decl::proposition(
    context,
    origin,
    Paxiom,
    proposition,
    formula,
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "invalid inversion axiom")
  }
  TheoryDecl(axiom)
}

///|
fn eliminate_inductive_group(
  context : @identity.CompilationContext,
  equality : @logic.LSymbol,
  declarations : ArrayView[@logic.InductiveDeclaration],
) -> Array[@theory.TheoryItem] raise TransformError {
  let stage = @identity.EliminateInductive
  let result : Array[@theory.TheoryItem] = []
  for declaration in declarations {
    let predicate = declaration.view().predicate
    result.push(
      TheoryDecl(
        @logic.Decl::parameter(
          context,
          predicate.view().origin,
          predicate,
          None,
        ),
      ) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "invalid inductive parameter")
      },
    )
  }
  for declaration in declarations {
    for case_ in declaration.view().cases {
      let view = case_.view()
      result.push(
        TheoryDecl(
          @logic.Decl::proposition(
            context,
            view.proposition.view().origin,
            Paxiom,
            view.proposition,
            view.formula,
            None,
          ),
        ) catch {
          _ =>
            fail_transform(InvariantFailure, stage, "invalid inductive axiom")
        },
      )
    }
  }
  for declaration in declarations {
    result.push(inversion_axiom(context, equality, declaration))
  }
  result
}

///|
pub fn eliminate_inductive(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.EliminateInductive
  require_task_context(context, task, stage)
  let equality = task_equality_symbol(task)
  let result : Array[@theory.TheoryItem] = []
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) =>
        match declaration.view() {
          Dind(declarations) => {
            guard equality is Some(equality) else {
              return fail_transform(
                InvariantFailure,
                stage,
                "task has no builtin equality symbol",
              )
            }
            for
              mapped in eliminate_inductive_group(
                context, equality, declarations,
              ) {
              result.push(mapped)
            }
          }
          _ => result.push(item)
        }
      TheoryUse(_) | TheoryClone(_) | TheoryMeta(_) => result.push(item)
    }
  }
  checked_task(task.context_anchor(), result, stage)
}
