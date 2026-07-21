// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
let closure_a_source : Bytes = b"theory T\n  use int.Int\n  constant x : int\n  axiom A : x = 1\n  goal G : x + 1 = 2\nend\n"

///|
test "checked file separates checking, raw tasks, and prepared calls" {
  let checked = check(closure_a_source, filename=b"closure-a.mlw")
  assert_eq(checked.typed_units().length(), 1)
  assert_eq(checked.raw_goals().length(), 0)
  guard checked.typed_units()[0] is Theory(theory)
  assert_eq(theory.view().name.view().name, b"T")
  let tasked = tasks(checked)
  assert_eq(tasked.raw_goals().length(), 1)
  let calls = prepare_proof(tasked)
  assert_eq(calls.length(), 1)
  let call = calls[0]
  let goal = call.goal_info().view()
  assert_eq(goal.unit_kind, @z3.TheoryUnit)
  assert_eq(goal.unit_name, b"T")
  assert_eq(goal.goal.view().name, b"G")
  assert_eq(goal.display_name, b"G")
  assert_eq(goal.ordinal, 0)
  assert_eq(goal.expl_attributes.length(), 0)
  assert_true(
    call.raw_task().context_anchor() == tasked.raw_goals()[0].context_anchor(),
  )
  assert_true(!call.query().bytes().is_empty())
  let command = call.command().view()
  assert_eq(command.executable_request, b"z3")
  assert_eq(command.arguments, [
    b"-smt2", b"-in", b"-T:10", b"sat.random_seed=42", b"nlsat.randomize=false",
    b"smt.random_seed=42", b"-st",
  ])
}

///|
let closure_b_source : Bytes = b"module ClosureB\n  use int.Int\n  val guarded (x : int) : int\n    requires { x >= 0 }\n    ensures { result = x }\n  let branch (x : int) : int\n    ensures { result >= 0 }\n  = if x >= 0 then guarded x else -x\n  let checked (x : int) : int\n    requires { x >= 0 }\n    ensures { result = x }\n  = assume { x >= 0 };\n    assert { x >= 0 };\n    x\nend\n"

///|
test "program modules generate ordered raw VCs before Z3 preparation" {
  let checked = check(closure_b_source, filename=b"closure-b.mlw")
  assert_eq(checked.typed_units().length(), 1)
  assert_eq(checked.raw_goals().length(), 0)
  guard checked.typed_units()[0] is Module(pmodule) else {
    fail("closure B did not elaborate as a program module")
  }
  assert_eq(pmodule.pure_theory().view().name.view().name, b"ClosureB")
  let tasked = tasks(checked)
  assert_eq(tasked.raw_goals().length(), 2)
  let infos = tasked.goal_infos()
  assert_eq(infos.length(), 2)
  assert_eq(infos[0].view().unit_kind, @z3.ModuleUnit)
  assert_eq(infos[0].view().unit_name, b"ClosureB")
  assert_eq(infos[0].view().goal.view().name, b"branch'vc")
  assert_eq(infos[0].view().ordinal, 0)
  assert_eq(infos[1].view().goal.view().name, b"checked'vc")
  assert_eq(infos[1].view().ordinal, 1)
  let calls = prepare_proof(tasked)
  assert_eq(calls.length(), 2)
  for call in calls {
    assert_true(!call.query().bytes().is_empty())
  }
}
