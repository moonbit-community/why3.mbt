// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn count_term_attribute(term : @logic.Term, wanted : BytesView) -> Int {
  let mut count = if term.attributes().any(attribute => attribute[:] == wanted) {
    1
  } else {
    0
  }
  let visit = fn(child) { count = count + count_term_attribute(child, wanted) }
  match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => ()
    Tapp(_, _, arguments) =>
      for argument in arguments {
        visit(argument)
      }
    Tif(condition, yes, no) => {
      visit(condition)
      visit(yes)
      visit(no)
    }
    Tlet(_, value, body) => {
      visit(value)
      visit(body)
    }
    Tcase(scrutinee, branches) => {
      visit(scrutinee)
      for branch in branches {
        visit(branch.view().body)
      }
    }
    Teps(_, body) => visit(body)
    Tquant(_, _, triggers, body) => {
      for group in triggers {
        for trigger in group {
          visit(trigger)
        }
      }
      visit(body)
    }
    Tbinop(_, left, right) => {
      visit(left)
      visit(right)
    }
    Tnot(inner) => visit(inner)
  }
  count
}

///|
fn count_task_attribute(task : @theory.Task, wanted : BytesView) -> Int {
  let mut count = 0
  for item in task.view().items {
    if item is TheoryDecl(declaration) {
      match declaration.view() {
        Dlogic(definitions) =>
          for definition in definitions {
            count = count + count_term_attribute(definition.view().body, wanted)
          }
        Dprop(_, _, formula) =>
          count = count + count_term_attribute(formula, wanted)
        Dtype(_) | Ddata(_) | Dparam(_) | Dind(_) => ()
      }
    }
  }
  count
}

///|
test "simplify_formula removes asymmetric split from program VCs" {
  let source : Bytes = b"module Abs\n  use int.Int\n  let abs (x : int) : int\n    ensures { result >= 0 }\n    ensures { result = x \\/ result = -x }\n  = if x >= 0 then x else -x\nend\n"
  let checked = tasks(check(source, filename=b"abs.mlw"))
  let context = checked.context
  let profile = bind_z3_profile(checked.environment, context)
  guard checked.raw_goals() is [raw] else { fail("expected one Abs VC") }
  let task = update_z3_task(profile, raw)
  let task = counterexamples_dependent_intros(context, task)
  let task = inline_trivial(context, task)
  let task = eliminate_builtin(context, task)
  let task = remove_unused_keep_constants(context, task)
  let task = detect_polymorphism(context, task)
  let task = eliminate_definition_conditionally(context, task)
  let task = eliminate_inductive(context, task)
  let task = eliminate_epsilon(context, task)
  let task = eliminate_literal(context, task)
  assert_true(count_task_attribute(task, b"asym_split") > 0)
  let simplified = simplify_formula(context, task)
  assert_eq(count_task_attribute(simplified, b"asym_split"), 0)
}
