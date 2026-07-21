// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn mapping_contains_value(
  mapping : Map[VSymbol, VSymbol],
  value : VSymbol,
) -> Bool {
  mapping.values().any(item => item == value)
}

///|
fn bind_alpha_pair(
  mapping : Map[VSymbol, VSymbol],
  left : VSymbol,
  right : VSymbol,
) -> Map[VSymbol, VSymbol]? {
  if left.ty != right.ty {
    return None
  }
  match mapping.get(left) {
    Some(previous) => if previous == right { Some(mapping) } else { None }
    None => {
      if mapping_contains_value(mapping, right) {
        return None
      }
      let result = mapping.copy()
      result[left] = right
      Some(result)
    }
  }
}

///|
fn alpha_pattern(
  left : Pattern,
  right : Pattern,
  mapping : Map[VSymbol, VSymbol],
) -> Map[VSymbol, VSymbol]? {
  if left.ty != right.ty {
    return None
  }
  match (left.node, right.node) {
    (WildPattern, WildPattern) => Some(mapping)
    (VariablePattern(left_variable), VariablePattern(right_variable)) =>
      bind_alpha_pair(mapping, left_variable, right_variable)
    (
      ApplicationPattern(left_symbol, left_arguments),
      ApplicationPattern(right_symbol, right_arguments),
    ) => {
      if left_symbol != right_symbol ||
        left_arguments.length() != right_arguments.length() {
        return None
      }
      let mut result = Some(mapping)
      for index, left_argument in left_arguments {
        guard result is Some(current) else { return None }
        result = alpha_pattern(left_argument, right_arguments[index], current)
      }
      result
    }
    (OrPattern(left_a, left_b), OrPattern(right_a, right_b)) => {
      guard alpha_pattern(left_a, right_a, mapping) is Some(first) else {
        return None
      }
      alpha_pattern(left_b, right_b, first)
    }
    (
      AsPattern(left_pattern, left_variable),
      AsPattern(right_pattern, right_variable),
    ) => {
      guard alpha_pattern(left_pattern, right_pattern, mapping) is Some(inner) else {
        return None
      }
      bind_alpha_pair(inner, left_variable, right_variable)
    }
    _ => None
  }
}

///|
fn alpha_term_array(
  left : ArrayView[Term],
  right : ArrayView[Term],
  mapping : Map[VSymbol, VSymbol],
) -> Bool {
  if left.length() != right.length() {
    return false
  }
  for index, item in left {
    if !alpha_term(item, right[index], mapping) {
      return false
    }
  }
  true
}

///|
fn alpha_term(
  left : Term,
  right : Term,
  mapping : Map[VSymbol, VSymbol],
) -> Bool {
  if left.result_type != right.result_type {
    return false
  }
  match (left.node, right.node) {
    (VariableTerm(left_variable), VariableTerm(right_variable)) =>
      match mapping.get(left_variable) {
        Some(mapped) => mapped == right_variable
        None =>
          left_variable == right_variable &&
          !mapping_contains_value(mapping, right_variable)
      }
    (ConstantTerm(left_constant), ConstantTerm(right_constant)) =>
      left_constant == right_constant
    (
      ApplicationTerm(left_symbol, left_instantiation, left_arguments),
      ApplicationTerm(right_symbol, right_instantiation, right_arguments),
    ) =>
      left_symbol == right_symbol &&
      left_instantiation == right_instantiation &&
      alpha_term_array(left_arguments, right_arguments, mapping)
    (
      IfTerm(left_condition, left_then, left_else),
      IfTerm(right_condition, right_then, right_else),
    ) =>
      alpha_term(left_condition, right_condition, mapping) &&
      alpha_term(left_then, right_then, mapping) &&
      alpha_term(left_else, right_else, mapping)
    (
      LetTerm(left_variable, left_value, left_body),
      LetTerm(right_variable, right_value, right_body),
    ) => {
      if !alpha_term(left_value, right_value, mapping) {
        return false
      }
      guard bind_alpha_pair(mapping, left_variable, right_variable)
        is Some(inner) else {
        return false
      }
      alpha_term(left_body, right_body, inner)
    }
    (CaseTerm(left_value, left_branches), CaseTerm(right_value, right_branches)) => {
      if !alpha_term(left_value, right_value, mapping) ||
        left_branches.length() != right_branches.length() {
        return false
      }
      for index, left_branch in left_branches {
        let right_branch = right_branches[index]
        guard alpha_pattern(left_branch.pattern, right_branch.pattern, mapping)
          is Some(branch_mapping) else {
          return false
        }
        if !alpha_term(left_branch.body, right_branch.body, branch_mapping) {
          return false
        }
      }
      true
    }
    (
      EpsilonTerm(left_variable, left_body),
      EpsilonTerm(right_variable, right_body),
    ) => {
      guard bind_alpha_pair(mapping, left_variable, right_variable)
        is Some(inner) else {
        return false
      }
      alpha_term(left_body, right_body, inner)
    }
    (
      QuantifiedTerm(left_quantifier, left_binders, left_triggers, left_body),
      QuantifiedTerm(
        right_quantifier,
        right_binders,
        right_triggers,
        right_body
      ),
    ) => {
      if left_quantifier != right_quantifier ||
        left_binders.length() != right_binders.length() ||
        left_triggers.length() != right_triggers.length() {
        return false
      }
      let mut quantified = mapping
      for index, left_binder in left_binders {
        guard bind_alpha_pair(quantified, left_binder, right_binders[index])
          is Some(next) else {
          return false
        }
        quantified = next
      }
      for index, left_group in left_triggers {
        if !alpha_term_array(left_group, right_triggers[index], quantified) {
          return false
        }
      }
      alpha_term(left_body, right_body, quantified)
    }
    (
      BinaryTerm(left_operator, left_left, left_right),
      BinaryTerm(right_operator, right_left, right_right),
    ) =>
      left_operator == right_operator &&
      alpha_term(left_left, right_left, mapping) &&
      alpha_term(left_right, right_right, mapping)
    (NotTerm(left_inner), NotTerm(right_inner)) =>
      alpha_term(left_inner, right_inner, mapping)
    (TrueTerm, TrueTerm) | (FalseTerm, FalseTerm) => true
    _ => false
  }
}

///|
/// Alpha-equivalence ignores binder spelling/identity and term decoration but
/// preserves all semantic symbols, types, constants, triggers, and node order.
pub fn Term::alpha_equivalent(self : Term, other : Term) -> Bool {
  alpha_term(self, other, Map([]))
}

///|
pub impl Eq for Term with fn equal(self, other) {
  self.alpha_equivalent(other)
}
