// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn counterexample_constant(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
) -> (@logic.LSymbol, @logic.Term, @logic.Decl) raise TransformError {
  let stage = @identity.PrepareForCounterexmp
  let view = variable.view()
  let symbol = @logic.LSymbol::new_function(
    context,
    view.name,
    view.origin,
    [],
    view.ty,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot introduce a counterexample constant",
      )
  }
  let term = @logic.Term::apply_function(symbol, [], None) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot apply an introduced counterexample constant",
      )
  }
  let declaration = @logic.Decl::parameter(context, view.origin, symbol, None) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot declare an introduced counterexample constant",
      )
  }
  (symbol, term, declaration)
}

///|
fn counterexample_axiom(
  context : @identity.CompilationContext,
  formula : @logic.Term,
) -> @logic.Decl raise TransformError {
  let stage = @identity.PrepareForCounterexmp
  let origin = @identity.Origin::generated(
    stage,
    b"H",
    formula.source_span(),
    formula.attributes(),
  )
  let proposition = @logic.PrSymbol::new(context, b"H", origin)
  @logic.Decl::proposition(context, origin, Paxiom, proposition, formula, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot introduce a counterexample premise",
      )
  }
}

///|
fn counterexample_let(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  value : @logic.Term,
) -> (@logic.Term, @logic.Decl) raise TransformError {
  let stage = @identity.PrepareForCounterexmp
  let view = variable.view()
  let symbol = @logic.LSymbol::new_function(
    context,
    view.name,
    view.origin,
    [],
    view.ty,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot introduce a counterexample let symbol",
      )
  }
  let application = @logic.Term::apply_function(symbol, [], None) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot apply a counterexample let symbol",
      )
  }
  let definition = @logic.LogicDefinition::new(context, symbol, [], value, None) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot define a counterexample let symbol",
      )
  }
  let declaration = @logic.Decl::logic(context, view.origin, [definition], None) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot declare a counterexample let symbol",
      )
  }
  (application, declaration)
}

///|
fn substitute_counterexample_variable(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  replacement : @logic.Term,
  body : @logic.Term,
) -> @logic.Term raise TransformError {
  @logic.TermSubstitution::new()
  .bind(variable, replacement, None)
  .apply(context, body, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.PrepareForCounterexmp,
        "cannot substitute an introduced counterexample variable",
      )
  }
}

///|
fn introduce_positive_foralls(
  context : @identity.CompilationContext,
  formula : @logic.Term,
  declarations : Array[@logic.Decl],
) -> @logic.Term raise TransformError {
  let stage = @identity.PrepareForCounterexmp
  let rebuilt = match formula.view() {
    Tbinop(Implies, premise, conclusion) =>
      @logic.Term::binary(
        Implies,
        premise,
        introduce_positive_foralls(context, conclusion, declarations),
        None,
      ) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot rebuild a counterexample implication",
          )
      }
    Tbinop(And, left, right) =>
      @logic.Term::binary(
        And,
        introduce_positive_foralls(context, left, declarations),
        introduce_positive_foralls(context, right, declarations),
        None,
      ) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot rebuild a counterexample conjunction",
          )
      }
    Tquant(ForallQuantifier, binders, _, body) => {
      let mut substitution = @logic.TermSubstitution::new()
      for binder in binders {
        let (_, replacement, declaration) = counterexample_constant(
          context, binder,
        )
        declarations.push(declaration)
        substitution = substitution.bind(binder, replacement, None) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              stage,
              "cannot bind a positive counterexample quantifier",
            )
        }
      }
      let body = substitution.apply(context, body, None) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot open a positive counterexample quantifier",
          )
      }
      introduce_positive_foralls(context, body, declarations)
    }
    _ => formula
  }
  copy_term_decoration(formula, rebuilt)
}

///|
fn introduce_counterexample_goal(
  context : @identity.CompilationContext,
  formula : @logic.Term,
  declarations : Array[@logic.Decl],
) -> @logic.Term raise TransformError {
  match formula.view() {
    Tbinop(Implies, premise, conclusion) => {
      declarations.push(counterexample_axiom(context, premise))
      introduce_counterexample_goal(
        context,
        copy_term_decoration(formula, conclusion),
        declarations,
      )
    }
    Tquant(ForallQuantifier, binders, _, body) => {
      let mut substitution = @logic.TermSubstitution::new()
      for binder in binders {
        let (_, replacement, declaration) = counterexample_constant(
          context, binder,
        )
        declarations.push(declaration)
        substitution = substitution.bind(binder, replacement, None) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              @identity.PrepareForCounterexmp,
              "cannot bind a counterexample quantifier",
            )
        }
      }
      let body = substitution.apply(context, body, None) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            @identity.PrepareForCounterexmp,
            "cannot open a counterexample quantifier",
          )
      }
      introduce_counterexample_goal(
        context,
        copy_term_decoration(formula, body),
        declarations,
      )
    }
    Tlet(variable, value, body) => {
      let (replacement, declaration) = counterexample_let(
        context, variable, value,
      )
      declarations.push(declaration)
      introduce_counterexample_goal(
        context,
        substitute_counterexample_variable(context, variable, replacement, body),
        declarations,
      )
    }
    _ => introduce_positive_foralls(context, formula, declarations)
  }
}

///|
pub fn prepare_for_counterexmp(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.PrepareForCounterexmp
  require_task_context(context, task, stage)
  if !task_has_meta(task, b"get_counterexmp") {
    return task
  }
  let items = task.view().items.to_owned()
  guard items.pop() is Some(TheoryDecl(goal)) &&
    goal.view() is Dprop(Pgoal, proposition, formula) else {
    return fail_transform(
      InvalidTask,
      stage,
      "counterexample preparation requires a final goal",
    )
  }
  let declarations : Array[@logic.Decl] = []
  let formula = introduce_counterexample_goal(context, formula, declarations)
  for declaration in declarations {
    items.push(TheoryDecl(declaration))
  }
  let rebuilt = @logic.Decl::proposition(
    context,
    goal.origin(),
    Pgoal,
    proposition,
    formula,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot rebuild the prepared counterexample goal",
      )
  }
  items.push(TheoryDecl(rebuilt))
  checked_task(task, items, stage)
}
