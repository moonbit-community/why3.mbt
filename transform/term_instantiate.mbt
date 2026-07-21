// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn instantiate_type(
  substitution : @logic.TySubstitution,
  ty : @logic.Ty,
  stage : @identity.GeneratedStage,
) -> @logic.Ty raise TransformError {
  substitution.apply(ty, None) catch {
    _ => fail_transform(InvariantFailure, stage, "cannot instantiate a type")
  }
}

///|
fn instantiate_optional_type(
  substitution : @logic.TySubstitution,
  ty : @logic.Ty?,
  stage : @identity.GeneratedStage,
) -> @logic.Ty? raise TransformError {
  match ty {
    None => None
    Some(ty) => Some(instantiate_type(substitution, ty, stage))
  }
}

///|
fn instantiate_variable(
  context : @identity.CompilationContext,
  substitution : @logic.TySubstitution,
  variable : @logic.VSymbol,
  stage : @identity.GeneratedStage,
) -> @logic.VSymbol raise TransformError {
  let view = variable.view()
  let ty = instantiate_type(substitution, view.ty, stage)
  if ty == view.ty {
    return variable
  }
  @logic.VSymbol::new(
    context,
    view.name,
    view.origin,
    ty,
    view.origin.source_span(),
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "cannot instantiate a binder")
  }
}

///|
fn variable_from_replacement(
  replacement : @logic.Term,
  stage : @identity.GeneratedStage,
) -> @logic.VSymbol raise TransformError {
  match replacement.view() {
    Tvar(variable) => variable
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "binder mapping is not a variable",
      )
  }
}

///|
fn instantiate_pattern(
  substitution : @logic.TySubstitution,
  variables : Map[@logic.VSymbol, @logic.Term],
  pattern : @logic.Pattern,
  stage : @identity.GeneratedStage,
) -> @logic.Pattern raise TransformError {
  let ty = instantiate_type(substitution, pattern.ty(), stage)
  match pattern.view() {
    Pwild(_) => @logic.Pattern::trusted_wild(ty)
    Pvar(variable) => {
      let replacement = match variables.get(variable) {
        Some(replacement) => replacement
        None =>
          fail_transform(InvariantFailure, stage, "missing pattern binder")
      }
      @logic.Pattern::trusted_variable(
        variable_from_replacement(replacement, stage),
      )
    }
    Papp(symbol, arguments, _) =>
      @logic.Pattern::trusted_app(
        symbol,
        [
          for argument in arguments => {
            instantiate_pattern(substitution, variables, argument, stage)
          }
        ],
        ty,
        None,
      ) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "cannot instantiate pattern")
      }
    Por(left, right, _) =>
      @logic.Pattern::trusted_or(
        instantiate_pattern(substitution, variables, left, stage),
        instantiate_pattern(substitution, variables, right, stage),
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot instantiate or-pattern",
          )
      }
    Pas(inner, variable, _) => {
      let replacement = match variables.get(variable) {
        Some(replacement) => replacement
        None =>
          fail_transform(InvariantFailure, stage, "missing as-pattern binder")
      }
      @logic.Pattern::trusted_as(
        instantiate_pattern(substitution, variables, inner, stage),
        variable_from_replacement(replacement, stage),
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot instantiate as-pattern",
          )
      }
    }
  }
}

///|
fn instantiate_term(
  context : @identity.CompilationContext,
  substitution : @logic.TySubstitution,
  values : Map[@logic.VSymbol, @logic.Term],
  term : @logic.Term,
  stage : @identity.GeneratedStage,
) -> @logic.Term raise TransformError {
  let recurse = fn(child) -> @logic.Term raise TransformError {
    instantiate_term(context, substitution, values, child, stage)
  }
  let replacement = match term.view() {
    Tvar(variable) =>
      match values.get(variable) {
        Some(replacement) => replacement
        None => {
          let instantiated = instantiate_variable(
            context, substitution, variable, stage,
          )
          @logic.Term::variable(instantiated)
        }
      }
    Tconst(constant) => {
      guard term.ty() is Some(ty) else {
        return fail_transform(
          InvariantFailure,
          stage,
          "constant is missing its type",
        )
      }
      @logic.Term::constant(
        constant,
        instantiate_type(substitution, ty, stage),
        None,
      ) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "cannot instantiate constant")
      }
    }
    Tapp(symbol, _, arguments) =>
      @logic.Term::elaborated_apply(
        symbol,
        [
          for argument in arguments => recurse(argument)
        ],
        instantiate_optional_type(substitution, term.ty(), stage),
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot instantiate application",
          )
      }
    Tif(condition, then_branch, else_branch) =>
      @logic.Term::if_then_else(
        recurse(condition),
        recurse(then_branch),
        recurse(else_branch),
        None,
      ) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "cannot instantiate if term")
      }
    Tlet(variable, value, body) => {
      let replacement_variable = instantiate_variable(
        context, substitution, variable, stage,
      )
      let nested = values.copy()
      nested[variable] = @logic.Term::variable(replacement_variable)
      @logic.Term::let_in(
        replacement_variable,
        recurse(value),
        instantiate_term(context, substitution, nested, body, stage),
        None,
      ) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "cannot instantiate let term")
      }
    }
    Tcase(scrutinee, branches) => {
      let mapped : Array[(@logic.Pattern, @logic.Term)] = []
      for branch in branches {
        let view = branch.view()
        let nested = values.copy()
        for variable in view.pattern.bound_variables() {
          let replacement = instantiate_variable(
            context, substitution, variable, stage,
          )
          nested[variable] = @logic.Term::variable(replacement)
        }
        mapped.push(
          (
            instantiate_pattern(substitution, nested, view.pattern, stage),
            instantiate_term(context, substitution, nested, view.body, stage),
          ),
        )
      }
      @logic.Term::trusted_case(recurse(scrutinee), mapped, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot instantiate case term",
          )
      }
    }
    Teps(variable, body) => {
      let replacement_variable = instantiate_variable(
        context, substitution, variable, stage,
      )
      let nested = values.copy()
      nested[variable] = @logic.Term::variable(replacement_variable)
      @logic.Term::trusted_epsilon(
        replacement_variable,
        instantiate_term(context, substitution, nested, body, stage),
        None,
      ) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "cannot instantiate epsilon")
      }
    }
    Tquant(quantifier, binders, triggers, body) => {
      let nested = values.copy()
      let mapped_binders : Array[@logic.VSymbol] = []
      for binder in binders {
        let replacement = instantiate_variable(
          context, substitution, binder, stage,
        )
        mapped_binders.push(replacement)
        nested[binder] = @logic.Term::variable(replacement)
      }
      let mapped_triggers = [
        for group in triggers => {
          [
            for trigger in group => {
              instantiate_term(context, substitution, nested, trigger, stage)
            }
          ]
        }
      ]
      @logic.Term::quantify(
        quantifier,
        mapped_binders,
        mapped_triggers,
        instantiate_term(context, substitution, nested, body, stage),
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot instantiate quantifier",
          )
      }
    }
    Tbinop(operator, left, right) =>
      @logic.Term::binary(operator, recurse(left), recurse(right), None) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "cannot instantiate formula")
      }
    Tnot(inner) =>
      @logic.Term::not(recurse(inner), None) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "cannot instantiate negation")
      }
    Ttrue => @logic.Term::true_formula()
    Tfalse => @logic.Term::false_formula()
  }
  copy_term_decoration(term, replacement)
}
