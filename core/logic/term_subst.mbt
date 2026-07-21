// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
struct TermSubstitution {
  entries : Map[VSymbol, Term]
  order : Array[VSymbol]
}

///|
pub fn TermSubstitution::new() -> TermSubstitution {
  { entries: Map([]), order: [] }
}

///|
pub fn TermSubstitution::bind(
  self : TermSubstitution,
  variable : VSymbol,
  replacement : Term,
  span : @identity.SourceSpan?,
) -> TermSubstitution raise TypeError {
  let replacement_type = require_value_type(replacement, span)
  if variable.ty != replacement_type {
    fail_type(TypeMismatch, span, "term substitution has the wrong value type")
  }
  if !variable.semantic_id().same_context(replacement_type.context_anchor()) {
    fail_type(
      ContextMismatch,
      span,
      "term substitution combines different compilation contexts",
    )
  }
  let entries = self.entries.copy()
  let order = self.order.copy()
  if !entries.contains(variable) {
    order.push(variable)
  }
  entries[variable] = replacement
  { entries, order }
}

///|
pub fn TermSubstitution::bindings(
  self : TermSubstitution,
) -> Array[(VSymbol, Term)] {
  [
    for variable in self.order => (variable, self.entries[variable])
  ]
}

///|
fn extend_bound_renaming(
  bound : Map[VSymbol, VSymbol],
  original : VSymbol,
  replacement : VSymbol,
) -> Map[VSymbol, VSymbol] {
  let result = bound.copy()
  result[original] = replacement
  result
}

///|
fn rename_pattern(
  pattern : Pattern,
  renamed : Map[VSymbol, VSymbol],
  span : @identity.SourceSpan?,
) -> Pattern raise TypeError {
  match pattern.node {
    WildPattern => Pattern::trusted_wild(pattern.ty)
    VariablePattern(variable) => Pattern::trusted_variable(renamed[variable])
    ApplicationPattern(symbol, arguments) =>
      Pattern::trusted_app(
        symbol,
        [
          for argument in arguments => rename_pattern(argument, renamed, span)
        ],
        pattern.ty,
        span,
      )
    OrPattern(left, right) =>
      Pattern::trusted_or(
        rename_pattern(left, renamed, span),
        rename_pattern(right, renamed, span),
        span,
      )
    AsPattern(inner, variable) =>
      Pattern::trusted_as(
        rename_pattern(inner, renamed, span),
        renamed[variable],
        span,
      )
  }
}

///|
fn substitute_term(
  context : @identity.CompilationContext,
  substitution : TermSubstitution,
  bound : Map[VSymbol, VSymbol],
  term : Term,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  let recurse = fn(child) -> Term raise TypeError {
    substitute_term(context, substitution, bound, child, span)
  }
  let rebuilt = match term.node {
    VariableTerm(variable) =>
      match bound.get(variable) {
        Some(renamed) => Term::variable(renamed)
        None =>
          match substitution.entries.get(variable) {
            Some(replacement) => replacement
            None => Term::variable(variable)
          }
      }
    ConstantTerm(constant) => {
      guard term.result_type is Some(result_type) else {
        abort("constant term is missing its type")
      }
      Term::constant(constant, result_type, span)
    }
    ApplicationTerm(symbol, _, arguments) =>
      apply_logic_symbol(
        symbol,
        [
          for argument in arguments => recurse(argument)
        ],
        span,
      )
    IfTerm(condition, then_branch, else_branch) =>
      Term::if_then_else(
        recurse(condition),
        recurse(then_branch),
        recurse(else_branch),
        span,
      )
    LetTerm(variable, value, body) => {
      let value = recurse(value)
      let replacement = variable.fresh_like(context, span)
      let body = substitute_term(
        context,
        substitution,
        extend_bound_renaming(bound, variable, replacement),
        body,
        span,
      )
      Term::let_in(replacement, value, body, span)
    }
    CaseTerm(scrutinee, branches) => {
      let rebuilt_branches : Array[(Pattern, Term)] = []
      for branch in branches {
        let mut branch_bound = bound
        let renamed : Map[VSymbol, VSymbol] = Map([])
        for variable in branch.pattern.bound_variables {
          let replacement = variable.fresh_like(context, span)
          renamed[variable] = replacement
          branch_bound = extend_bound_renaming(
            branch_bound, variable, replacement,
          )
        }
        rebuilt_branches.push(
          (
            rename_pattern(branch.pattern, renamed, span),
            substitute_term(
              context,
              substitution,
              branch_bound,
              branch.body,
              span,
            ),
          ),
        )
      }
      Term::trusted_case(recurse(scrutinee), rebuilt_branches, span)
    }
    EpsilonTerm(variable, body) => {
      let replacement = variable.fresh_like(context, span)
      Term::trusted_epsilon(
        replacement,
        substitute_term(
          context,
          substitution,
          extend_bound_renaming(bound, variable, replacement),
          body,
          span,
        ),
        span,
      )
    }
    QuantifiedTerm(quantifier, binders, triggers, body) => {
      let replacements : Array[VSymbol] = []
      let mut quantified_bound = bound
      for binder in binders {
        let replacement = binder.fresh_like(context, span)
        replacements.push(replacement)
        quantified_bound = extend_bound_renaming(
          quantified_bound, binder, replacement,
        )
      }
      let rebuilt_triggers : Array[Array[Term]] = []
      for group in triggers {
        rebuilt_triggers.push(
          [
            for trigger in group => {
              substitute_term(
                context, substitution, quantified_bound, trigger, span,
              )
            }
          ],
        )
      }
      Term::quantify(
        quantifier,
        replacements,
        rebuilt_triggers,
        substitute_term(context, substitution, quantified_bound, body, span),
        span,
      )
    }
    BinaryTerm(operator, left, right) =>
      Term::binary(operator, recurse(left), recurse(right), span)
    NotTerm(inner) => Term::not(recurse(inner), span)
    TrueTerm => Term::true_formula()
    FalseTerm => Term::false_formula()
  }
  term.copy_decoration(rebuilt)
}

///|
/// Applies a type-safe substitution. Every crossed binder is alpha-renamed
/// through `context`, which makes capture impossible even when a replacement
/// contains the old binder identity as a free variable.
pub fn TermSubstitution::apply(
  self : TermSubstitution,
  context : @identity.CompilationContext,
  term : Term,
  span : @identity.SourceSpan?,
) -> Term raise TypeError {
  if self.order.is_empty() {
    return term
  }
  for variable in self.order {
    require_context_id(
      context,
      variable.semantic_id(),
      span,
      "term substitution belongs to another compilation context",
    )
    validate_term_context(context, self.entries[variable], span)
  }
  substitute_term(context, self, Map([]), term, span)
}
