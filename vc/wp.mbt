// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn continuation_formula(
  continuations : ArrayView[(Int, @logic.Term)],
  index : Int,
) -> @logic.Term raise VcError {
  for entry in continuations {
    if entry.0 == index {
      return entry.1
    }
  }
  fail_vc(InvariantFailure, None, "Kode requests an undefined continuation")
}

///|
fn bind_continuation(
  continuations : ArrayView[(Int, @logic.Term)],
  index : Int,
  formula : @logic.Term,
) -> Array[(Int, @logic.Term)] {
  let result = []
  let mut replaced = false
  for entry in continuations {
    if entry.0 == index {
      result.push((index, formula))
      replaced = true
    } else {
      result.push(entry)
    }
  }
  if !replaced {
    result.push((index, formula))
  }
  result
}

///|
fn filter_continuations(
  continuations : ArrayView[(Int, @logic.Term)],
  outcomes : ArrayView[Int],
) -> Array[(Int, @logic.Term)] {
  let result : Array[(Int, @logic.Term)] = []
  for continuation in continuations {
    if outcomes.contains(continuation.0) {
      result.push(continuation)
    }
  }
  result
}

///|
fn efficient_wp_kode(
  environment : VcEnvironment,
  kode : Kode,
  continuations : ArrayView[(Int, @logic.Term)],
) -> @logic.Term raise {
  let mut closed = kode
  for continuation in continuations {
    closed = kseq(closed, continuation.0, kstop(continuation.1))
  }
  let result = pure_sp(environment, closed, [])
  if !result.outcomes.is_empty() {
    fail_vc(InvariantFailure, None, "Kode requests an undefined continuation")
  }
  result.safety
}

///|
fn wp_kode(
  environment : VcEnvironment,
  kode : Kode,
  continuations : ArrayView[(Int, @logic.Term)],
) -> @logic.Term raise {
  match kode.view() {
    Kseq(first, index, second) => {
      let next = wp_kode(environment, second, continuations)
      wp_kode(environment, first, bind_continuation(continuations, index, next))
    }
    Kpar(left, right) =>
      wp_and(
        wp_kode(environment, left, continuations),
        wp_kode(environment, right, continuations),
      )
    Kif(condition, yes, no) =>
      wp_if(
        environment.boolean_test(condition),
        wp_kode(environment, yes, continuations),
        wp_kode(environment, no, continuations),
      )
    Kcase(scrutinee, branches) => {
      let formulas = branches.map(entry => {
        (entry.0, wp_kode(environment, entry.1, continuations))
      })
      if formulas.all(entry => can_simplify_true(entry.1)) {
        @logic.Term::true_formula()
      } else {
        @logic.Term::case(pvariable_term(scrutinee), formulas, None)
      }
    }
    Khavoc(affected, writes, span) =>
      wp_havoc(
        environment,
        affected,
        writes,
        continuation_formula(continuations, 0),
        span,
      )
    Klet(binder, value, constraint) =>
      wp_let(
        environment,
        binder,
        value,
        sp_implies(constraint, continuation_formula(continuations, 0)),
      )
    Kval(binders, constraint) =>
      forall_simplified(
        [
          for binder in binders => binder.view().pure_symbol
        ],
        sp_implies(constraint, continuation_formula(continuations, 0)),
      )
    Kcut(formula) =>
      wp_and_asymmetric(formula, continuation_formula(continuations, 0))
    Kstop(formula) => formula
    Kcont(index) => continuation_formula(continuations, index)
    Koff(explanation, inner) =>
      solder_explanation(
        wp_kode(environment, inner, continuations),
        explanation,
      )
    Kmode(ClassicalWp, inner) => wp_kode(environment, inner, continuations)
    Kmode(EfficientSp, inner) =>
      efficient_wp_kode(environment, inner, continuations)
    Kout(outcomes, inner) =>
      wp_kode(environment, inner, filter_continuations(continuations, outcomes))
    Kpush(_, _) =>
      fail_vc(InvariantFailure, None, "unconsumed Kode continuation marker")
  }
}

///|
pub fn lower_routine(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
  cty : @mlw.Cty,
  body : @mlw.Expr,
) -> Kode raise {
  let environment = VcEnvironment::new(context, pmodule)
  routine_kode(environment, cty, body)
}

///|
pub fn classical_wp(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
  kode : Kode,
) -> @logic.Term raise {
  let environment = VcEnvironment::new(context, pmodule)
  wp_kode(environment, kode, [])
}

///|
pub fn efficient_wp(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
  kode : Kode,
) -> @logic.Term raise {
  let environment = VcEnvironment::new(context, pmodule)
  efficient_wp_kode(environment, kode, [])
}

///|
fn routine_vc_formula(
  environment : VcEnvironment,
  cty : @mlw.Cty,
  body : @mlw.Expr,
  mode : VcMode,
) -> @logic.Term raise {
  let kode = reflow_kode(mode, routine_kode(environment, cty, body))
  wp_kode(environment, kode, [])
}
