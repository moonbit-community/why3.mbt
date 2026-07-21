// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv struct PureSpResult {
  safety : @logic.Term
  normal : @logic.Term?
  reads : Array[@logic.VSymbol]
}

///|
fn symbol_contains(
  symbols : ArrayView[@logic.VSymbol],
  wanted : @logic.VSymbol,
) -> Bool {
  symbols.any(symbol => symbol == wanted)
}

///|
fn symbol_union(
  left : ArrayView[@logic.VSymbol],
  right : ArrayView[@logic.VSymbol],
) -> Array[@logic.VSymbol] {
  let result = left.to_owned()
  for symbol in right {
    if !symbol_contains(result, symbol) {
      result.push(symbol)
    }
  }
  result
}

///|
fn symbol_remove(
  symbols : ArrayView[@logic.VSymbol],
  unwanted : @logic.VSymbol,
) -> Array[@logic.VSymbol] {
  [
    for symbol in symbols if symbol != unwanted => symbol
  ]
}

///|
fn symbol_remove_all(
  symbols : ArrayView[@logic.VSymbol],
  unwanted : ArrayView[@logic.VSymbol],
) -> Array[@logic.VSymbol] {
  [
    for symbol in symbols if !symbol_contains(unwanted, symbol) => symbol
  ]
}

///|
fn symbol_difference(
  left : ArrayView[@logic.VSymbol],
  right : ArrayView[@logic.VSymbol],
) -> Array[@logic.VSymbol] {
  [
    for symbol in left if !symbol_contains(right, symbol) => symbol
  ]
}

///|
fn reads_with_term(
  reads : ArrayView[@logic.VSymbol],
  term : @logic.Term,
) -> Array[@logic.VSymbol] {
  symbol_union(reads, term.free_variables())
}

///|
fn pure_sp_and(left : @logic.Term, right : @logic.Term) -> @logic.Term raise {
  if is_true(left) || is_false(right) {
    right
  } else if is_true(right) || is_false(left) {
    left
  } else {
    plain_and(left, right)
  }
}

///|
fn pure_sp_or(left : @logic.Term, right : @logic.Term) -> @logic.Term raise {
  if is_true(left) || is_false(right) {
    left
  } else if is_true(right) || is_false(left) {
    right
  } else {
    @logic.Term::binary(Or, left, right, None).add_attributes([
      case_split_attribute,
    ])
  }
}

///|
fn pure_sp_if(
  condition : @logic.Term,
  yes : @logic.Term,
  no : @logic.Term,
) -> @logic.Term raise {
  if is_true(condition) || (is_true(yes) && is_true(no)) {
    yes
  } else if is_false(condition) || (is_false(yes) && is_false(no)) {
    no
  } else if is_false(no) {
    pure_sp_and(condition, yes)
  } else if is_false(yes) {
    pure_sp_and(not_simplified(condition), no)
  } else {
    @logic.Term::if_then_else(condition, yes, no, None).add_attributes([
      case_split_attribute,
    ])
  }
}

///|
fn exists_simplified(
  binders : ArrayView[@logic.VSymbol],
  body : @logic.Term,
) -> @logic.Term raise {
  let free = body.free_variables()
  @logic.Term::quantify(
    ExistsQuantifier,
    [
      for binder in binders if symbol_contains(free, binder) => binder
    ],
    [],
    body,
    None,
  )
}

///|
fn pure_sp_let(
  environment : VcEnvironment,
  variable : @mlw.PVariable,
  value : @logic.Term,
  formula : @logic.Term,
  post_reads : ArrayView[@logic.VSymbol],
) -> @logic.Term raise {
  let symbol = variable.view().pure_symbol
  guard environment.unit_value.ty() is Some(unit_type) else {
    abort("validated unit value is untyped")
  }
  if variable.view().ity.to_ty(None) == unit_type {
    substitute_variable(
      environment.context,
      symbol,
      environment.unit_value,
      formula,
    )
  } else if symbol_contains(post_reads, symbol) {
    pure_sp_and(
      @logic.Term::elaborated_apply(
        environment.equality,
        [@logic.Term::variable(symbol), value],
        None,
        None,
      ),
      formula,
    )
  } else {
    let_simplified_symbol(
      environment.context,
      symbol,
      value,
      formula,
      relevant_for_counterexample(symbol),
    )
  }
}

///|
fn normal_sp_conjunction(
  left : @logic.Term?,
  right : @logic.Term?,
) -> @logic.Term? raise {
  match (left, right) {
    (Some(left), Some(right)) => Some(pure_sp_or(left, right))
    (Some(formula), None) | (None, Some(formula)) => Some(formula)
    (None, None) => None
  }
}

///|
fn pure_sp_sequence(
  environment : VcEnvironment,
  first : Kode,
  second : Kode,
  post_reads : ArrayView[@logic.VSymbol],
) -> PureSpResult raise {
  match first.view() {
    Klet(variable, value, constraint) => {
      let tail = pure_sp(environment, second, post_reads)
      let safety = wp_let(
        environment,
        variable,
        value,
        sp_implies(constraint, tail.safety),
      )
      let normal = match tail.normal {
        Some(formula) =>
          Some(
            pure_sp_let(
              environment,
              variable,
              value,
              pure_sp_and(constraint, formula),
              post_reads,
            ),
          )
        None => None
      }
      let reads = symbol_remove(
        reads_with_term(reads_with_term(tail.reads, value), constraint),
        variable.view().pure_symbol,
      )
      { safety, normal, reads }
    }
    _ => {
      let tail = pure_sp(environment, second, post_reads)
      let head = pure_sp(environment, first, tail.reads)
      match head.normal {
        None => { safety: head.safety, normal: None, reads: head.reads }
        Some(head_sp) => {
          let bound = symbol_difference(tail.reads, head.reads)
          let tail_safety = forall_simplified(
            bound,
            sp_implies(head_sp, tail.safety),
          )
          let safety = wp_and(head.safety, tail_safety)
          let normal = match tail.normal {
            None => None
            Some(tail_sp) =>
              Some(
                exists_simplified(
                  symbol_difference(bound, post_reads),
                  pure_sp_and(head_sp, tail_sp),
                ),
              )
          }
          { safety, normal, reads: head.reads }
        }
      }
    }
  }
}

///|
fn pure_sp(
  environment : VcEnvironment,
  kode : Kode,
  post_reads : ArrayView[@logic.VSymbol],
) -> PureSpResult raise {
  match kode.view() {
    Kseq(first, index, second) => {
      if index != 0 {
        fail_vc(
          UnsupportedComputation,
          None,
          "exceptional SP continuations are outside the classical MVP",
        )
      }
      pure_sp_sequence(environment, first, second, post_reads)
    }
    Kpar(left, right) => {
      let left = pure_sp(environment, left, post_reads)
      let right = pure_sp(environment, right, post_reads)
      {
        safety: wp_and(left.safety, right.safety),
        normal: normal_sp_conjunction(left.normal, right.normal),
        reads: symbol_union(left.reads, right.reads),
      }
    }
    Kif(condition, yes, no) => {
      let yes = pure_sp(environment, yes, post_reads)
      let no = pure_sp(environment, no, post_reads)
      let condition_formula = environment.boolean_test(condition)
      let normal = match (yes.normal, no.normal) {
        (Some(yes_sp), Some(no_sp)) =>
          Some(pure_sp_if(condition_formula, yes_sp, no_sp))
        (Some(yes_sp), None) => Some(pure_sp_and(condition_formula, yes_sp))
        (None, Some(no_sp)) =>
          Some(pure_sp_and(not_simplified(condition_formula), no_sp))
        (None, None) => None
      }
      {
        safety: wp_if(condition_formula, yes.safety, no.safety),
        normal,
        reads: symbol_union(
          [condition.view().pure_symbol],
          symbol_union(yes.reads, no.reads),
        ),
      }
    }
    Klet(variable, value, constraint) => {
      let normal = pure_sp_let(
        environment, variable, value, constraint, post_reads,
      )
      {
        safety: @logic.Term::true_formula(),
        normal: Some(normal),
        reads: symbol_remove(
          reads_with_term(post_reads, normal),
          variable.view().pure_symbol,
        ),
      }
    }
    Kval(variables, constraint) => {
      let binders = [ for variable in variables => variable.view().pure_symbol ]
      let lost = [
        for binder in binders if !symbol_contains(post_reads, binder) => binder
      ]
      let normal = exists_simplified(lost, constraint)
      {
        safety: @logic.Term::true_formula(),
        normal: Some(normal),
        reads: symbol_remove_all(reads_with_term(post_reads, normal), binders),
      }
    }
    Kcut(formula) =>
      {
        safety: formula,
        normal: Some(formula),
        reads: reads_with_term(post_reads, formula),
      }
    Kstop(formula) =>
      { safety: formula, normal: None, reads: formula.free_variables() }
    Kcont(index) => {
      if index != 0 {
        fail_vc(
          UnsupportedComputation,
          None,
          "exceptional SP continuations are outside the classical MVP",
        )
      }
      {
        safety: @logic.Term::true_formula(),
        normal: Some(@logic.Term::true_formula()),
        reads: post_reads.to_owned(),
      }
    }
  }
}

///|
fn pure_if_wp(
  environment : VcEnvironment,
  condition : @mlw.PVariable,
  yes : Kode,
  no : Kode,
  continuation : @logic.Term,
) -> @logic.Term raise {
  pure_sp(environment, kseq(kif(condition, yes, no), 0, kstop(continuation)), []).safety
}
