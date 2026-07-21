// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn normal_continuation(
  continuation : @logic.Term?,
) -> @logic.Term raise VcError {
  match continuation {
    Some(formula) => formula
    None =>
      fail_vc(
        InvariantFailure,
        None,
        "Kode requests a normal continuation where none is defined",
      )
  }
}

///|
fn wp_kode(
  environment : VcEnvironment,
  kode : Kode,
  continuation : @logic.Term?,
) -> @logic.Term raise {
  match kode.view() {
    Kseq(first, index, second) => {
      if index != 0 {
        fail_vc(
          UnsupportedComputation,
          None,
          "exceptional Kode continuations are outside the classical MVP",
        )
      }
      let next = wp_kode(environment, second, continuation)
      wp_kode(environment, first, Some(next))
    }
    Kpar(left, right) =>
      wp_and(
        wp_kode(environment, left, continuation),
        wp_kode(environment, right, continuation),
      )
    Kif(condition, yes, no) =>
      match continuation {
        Some(formula) => pure_if_wp(environment, condition, yes, no, formula)
        None =>
          wp_if(
            environment.boolean_test(condition),
            wp_kode(environment, yes, continuation),
            wp_kode(environment, no, continuation),
          )
      }
    Klet(binder, value, constraint) =>
      wp_let(
        environment,
        binder,
        value,
        sp_implies(constraint, normal_continuation(continuation)),
      )
    Kval(binders, constraint) =>
      forall_simplified(
        [
          for binder in binders => binder.view().pure_symbol
        ],
        sp_implies(constraint, normal_continuation(continuation)),
      )
    Kcut(formula) =>
      wp_and_asymmetric(formula, normal_continuation(continuation))
    Kstop(formula) => formula
    Kcont(index) => {
      if index != 0 {
        fail_vc(
          UnsupportedComputation,
          None,
          "exceptional Kode continuations are outside the classical MVP",
        )
      }
      normal_continuation(continuation)
    }
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
  wp_kode(environment, kode, None)
}

///|
fn routine_vc_formula(
  environment : VcEnvironment,
  cty : @mlw.Cty,
  body : @mlw.Expr,
) -> @logic.Term raise {
  wp_kode(environment, routine_kode(environment, cty, body), None)
}
