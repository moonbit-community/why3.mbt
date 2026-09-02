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
  variable.clone_with_type(context, ty, view.origin.source_span()) catch {
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
    Pwild(_) => @logic.Pattern::wild(ty)
    Pvar(variable) => {
      let replacement = match variables.get(variable) {
        Some(replacement) => replacement
        None =>
          fail_transform(InvariantFailure, stage, "missing pattern binder")
      }
      @logic.Pattern::variable(variable_from_replacement(replacement, stage))
    }
    Papp(symbol, arguments, _) =>
      @logic.Pattern::app(
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
      @logic.Pattern::or(
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
      @logic.Pattern::as_pattern(
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
  span : @identity.SourceSpan?,
) -> @logic.Term raise TransformError {
  let substituted_value = match term.view() {
    Tvar(variable) => values.contains(variable)
    _ => false
  }
  let recurse = fn(child) -> @logic.Term raise TransformError {
    instantiate_term(context, substitution, values, child, stage, span)
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
        span,
      ) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "cannot instantiate constant")
      }
    }
    Tapp(symbol, _, arguments) => {
      let mapped_arguments = [ for argument in arguments => recurse(argument) ]
      let mapped_type = instantiate_optional_type(
        substitution,
        term.ty(),
        stage,
      )
      @logic.Term::elaborated_apply(symbol, mapped_arguments, mapped_type, span) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot instantiate application",
          )
      }
    }
    Tif(condition, then_branch, else_branch) => {
      let mapped_condition = recurse(condition)
      let mapped_then = recurse(then_branch)
      let mapped_else = recurse(else_branch)
      @logic.Term::if_then_else(
        mapped_condition, mapped_then, mapped_else, span,
      ) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "cannot instantiate if term")
      }
    }
    Tlet(variable, value, body) => {
      let replacement_variable = instantiate_variable(
        context, substitution, variable, stage,
      )
      let nested = values.copy()
      nested[variable] = @logic.Term::variable(replacement_variable)
      let mapped_value = recurse(value)
      let mapped_body = instantiate_term(
        context, substitution, nested, body, stage, span,
      )
      @logic.Term::let_in(replacement_variable, mapped_value, mapped_body, span) catch {
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
            instantiate_term(
              context,
              substitution,
              nested,
              view.body,
              stage,
              span,
            ),
          ),
        )
      }
      let mapped_scrutinee = recurse(scrutinee)
      @logic.Term::case(mapped_scrutinee, mapped, span) catch {
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
      let mapped_body = instantiate_term(
        context, substitution, nested, body, stage, span,
      )
      @logic.Term::epsilon(replacement_variable, mapped_body, span) catch {
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
              instantiate_term(
                context, substitution, nested, trigger, stage, span,
              )
            }
          ]
        }
      ]
      let mapped_body = instantiate_term(
        context, substitution, nested, body, stage, span,
      )
      @logic.Term::quantify(
        quantifier, mapped_binders, mapped_triggers, mapped_body, span,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot instantiate quantifier",
          )
      }
    }
    Tbinop(operator, left, right) => {
      let mapped_left = recurse(left)
      let mapped_right = recurse(right)
      @logic.Term::binary(operator, mapped_left, mapped_right, span) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "cannot instantiate formula")
      }
    }
    Tnot(inner) => {
      let mapped_inner = recurse(inner)
      @logic.Term::not(mapped_inner, span) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "cannot instantiate negation")
      }
    }
    Ttrue => @logic.Term::true_formula()
    Tfalse => @logic.Term::false_formula()
  }
  let replacement = match (span, replacement.source_span()) {
    (Some(span), None) =>
      replacement.source_decorate(Some(span), replacement.attributes())
    (Some(span), Some(_)) if !substituted_value =>
      replacement.source_decorate(Some(span), replacement.attributes())
    _ => replacement
  }
  copy_term_decoration(term, replacement)
}
