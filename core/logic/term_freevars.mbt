// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn with_bound_variable(
  bound : Map[VSymbol, Unit],
  variable : VSymbol,
) -> Map[VSymbol, Unit] {
  let result = bound.copy()
  result[variable] = ()
  result
}

///|
fn with_bound_variables(
  bound : Map[VSymbol, Unit],
  variables : ArrayView[VSymbol],
) -> Map[VSymbol, Unit] {
  let result = bound.copy()
  for variable in variables {
    result[variable] = ()
  }
  result
}

///|
fn collect_free_term_variables(
  term : Term,
  bound : Map[VSymbol, Unit],
  seen : Map[VSymbol, Unit],
  result : Array[VSymbol],
) -> Unit {
  let visit = fn(child) {
    collect_free_term_variables(child, bound, seen, result)
  }
  match term.node {
    VariableTerm(variable) =>
      if !bound.contains(variable) && !seen.contains(variable) {
        seen[variable] = ()
        result.push(variable)
      }
    ConstantTerm(_) | TrueTerm | FalseTerm => ()
    ApplicationTerm(_, _, arguments) =>
      for argument in arguments {
        visit(argument)
      }
    IfTerm(condition, then_branch, else_branch) => {
      visit(condition)
      visit(then_branch)
      visit(else_branch)
    }
    LetTerm(variable, value, body) => {
      visit(value)
      collect_free_term_variables(
        body,
        with_bound_variable(bound, variable),
        seen,
        result,
      )
    }
    CaseTerm(scrutinee, branches) => {
      visit(scrutinee)
      for branch in branches {
        collect_free_term_variables(
          branch.body,
          with_bound_variables(bound, branch.pattern.bound_variables),
          seen,
          result,
        )
      }
    }
    EpsilonTerm(variable, body) =>
      collect_free_term_variables(
        body,
        with_bound_variable(bound, variable),
        seen,
        result,
      )
    QuantifiedTerm(_, binders, triggers, body) => {
      let quantified = with_bound_variables(bound, binders)
      for group in triggers {
        for trigger in group {
          collect_free_term_variables(trigger, quantified, seen, result)
        }
      }
      collect_free_term_variables(body, quantified, seen, result)
    }
    BinaryTerm(_, left, right) => {
      visit(left)
      visit(right)
    }
    NotTerm(inner) => visit(inner)
  }
}

///|
pub fn Term::free_variables(self : Term) -> Array[VSymbol] {
  let result : Array[VSymbol] = []
  collect_free_term_variables(self, Map([]), Map([]), result)
  result
}

///|
fn collect_type_variables_from_type(
  ty : Ty,
  seen : Map[TyVarSymbol, Unit],
  result : Array[TyVarSymbol],
) -> Unit {
  for variable in ty.free_variables() {
    if !seen.contains(variable) {
      seen[variable] = ()
      result.push(variable)
    }
  }
}

///|
fn collect_pattern_type_variables(
  pattern : Pattern,
  seen : Map[TyVarSymbol, Unit],
  result : Array[TyVarSymbol],
) -> Unit {
  collect_type_variables_from_type(pattern.ty, seen, result)
  match pattern.node {
    WildPattern | VariablePattern(_) => ()
    ApplicationPattern(_, arguments) =>
      for argument in arguments {
        collect_pattern_type_variables(argument, seen, result)
      }
    OrPattern(left, right) => {
      collect_pattern_type_variables(left, seen, result)
      collect_pattern_type_variables(right, seen, result)
    }
    AsPattern(inner, _) => collect_pattern_type_variables(inner, seen, result)
  }
}

///|
fn collect_term_type_variables(
  term : Term,
  seen : Map[TyVarSymbol, Unit],
  result : Array[TyVarSymbol],
) -> Unit {
  if term.result_type is Some(ty) {
    collect_type_variables_from_type(ty, seen, result)
  }
  let visit = fn(child) { collect_term_type_variables(child, seen, result) }
  match term.node {
    VariableTerm(variable) =>
      collect_type_variables_from_type(variable.ty, seen, result)
    ConstantTerm(_) | TrueTerm | FalseTerm => ()
    ApplicationTerm(_, instantiation, arguments) => {
      for entry in instantiation {
        collect_type_variables_from_type(entry.1, seen, result)
      }
      for argument in arguments {
        visit(argument)
      }
    }
    IfTerm(condition, then_branch, else_branch) => {
      visit(condition)
      visit(then_branch)
      visit(else_branch)
    }
    LetTerm(variable, value, body) => {
      collect_type_variables_from_type(variable.ty, seen, result)
      visit(value)
      visit(body)
    }
    CaseTerm(scrutinee, branches) => {
      visit(scrutinee)
      for branch in branches {
        collect_pattern_type_variables(branch.pattern, seen, result)
        visit(branch.body)
      }
    }
    EpsilonTerm(variable, body) => {
      collect_type_variables_from_type(variable.ty, seen, result)
      visit(body)
    }
    QuantifiedTerm(_, binders, triggers, body) => {
      for binder in binders {
        collect_type_variables_from_type(binder.ty, seen, result)
      }
      for group in triggers {
        for trigger in group {
          visit(trigger)
        }
      }
      visit(body)
    }
    BinaryTerm(_, left, right) => {
      visit(left)
      visit(right)
    }
    NotTerm(inner) => visit(inner)
  }
}

///|
pub fn Term::free_type_variables(self : Term) -> Array[TyVarSymbol] {
  let result : Array[TyVarSymbol] = []
  collect_term_type_variables(self, Map([]), result)
  result
}

///|
fn term_contains_logic_symbol(term : Term, target : LSymbol) -> Bool {
  let mut found = false
  let visit = fn(child) {
    if !found && term_contains_logic_symbol(child, target) {
      found = true
    }
  }
  match term.node {
    ApplicationTerm(symbol, _, arguments) => {
      if symbol == target {
        return true
      }
      for argument in arguments {
        visit(argument)
      }
    }
    IfTerm(condition, then_branch, else_branch) => {
      visit(condition)
      visit(then_branch)
      visit(else_branch)
    }
    LetTerm(_, value, body) => {
      visit(value)
      visit(body)
    }
    CaseTerm(scrutinee, branches) => {
      visit(scrutinee)
      for branch in branches {
        visit(branch.body)
      }
    }
    EpsilonTerm(_, body) => visit(body)
    QuantifiedTerm(_, _, triggers, body) => {
      for group in triggers {
        for trigger in group {
          visit(trigger)
        }
      }
      visit(body)
    }
    BinaryTerm(_, left, right) => {
      visit(left)
      visit(right)
    }
    NotTerm(inner) => visit(inner)
    VariableTerm(_) | ConstantTerm(_) | TrueTerm | FalseTerm => ()
  }
  found
}

///|
pub fn Term::contains_logic_symbol(self : Term, symbol : LSymbol) -> Bool {
  term_contains_logic_symbol(self, symbol)
}
