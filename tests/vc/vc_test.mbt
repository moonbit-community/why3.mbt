// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn elaborate_test_module(
  source : String,
  filename : BytesView,
) -> (@identity.CompilationContext, @mlw.Pmodule) raise {
  guard @parser.parse_mlw_file(@utf8.encode(source)[:], filename~)
    is Modules([unit]) else {
    abort("VC test input did not parse as one module")
  }
  let context = @identity.CompilationContext::new()
  let frozen = @stdlib.minimal_env(context)
  (
    context,
    @elab.elaborate_program_unit(context, frozen.semantic_environment(), unit),
  )
}

///|
fn concrete_routines(
  pmodule : @mlw.Pmodule,
) -> Array[(@mlw.RoutineSymbol, @mlw.Cty, @mlw.Expr)] {
  let result = []
  for item in pmodule.view().items {
    if item is Udecl(PDlet(symbol, Cfun(cty, Some(body)), _)) {
      result.push((symbol, cty, body))
    }
  }
  result
}

///|
fn count_kode(kode : @why3vc.Kode, counts : Array[Int]) -> Unit {
  match kode.view() {
    Kseq(first, _, second) => {
      counts[0] = counts[0] + 1
      count_kode(first, counts)
      count_kode(second, counts)
    }
    Kpar(left, right) => {
      counts[1] = counts[1] + 1
      count_kode(left, counts)
      count_kode(right, counts)
    }
    Kif(_, yes, no) => {
      counts[2] = counts[2] + 1
      count_kode(yes, counts)
      count_kode(no, counts)
    }
    Klet(_, _, _) => counts[3] = counts[3] + 1
    Kval(_, _) => counts[4] = counts[4] + 1
    Kcut(_) => counts[5] = counts[5] + 1
    Kstop(_) => counts[6] = counts[6] + 1
    Kcont(_) => counts[7] = counts[7] + 1
  }
}

///|
test "Kode lowering keeps every classical MVP layer explicit" {
  let source =
    #|module Rules
    #|  use int.Int
    #|  val guarded (x : int) : int
    #|    requires { x >= 0 }
    #|    ensures { result = x }
    #|
    #|  let branch (x : int) : int
    #|    ensures { result >= 0 }
    #|  = if x >= 0 then guarded x else -x
    #|
    #|  let checked (x : int) : int
    #|    requires { x >= 0 }
    #|    ensures { result = x }
    #|  = assume { x >= 0 };
    #|    assert { x >= 0 };
    #|    x
    #|end
  let (context, pmodule) = elaborate_test_module(source, b"vc-rules.mlw")
  let routines = concrete_routines(pmodule)
  assert_eq(routines.length(), 2)
  let counts = Array::make(8, 0)
  for routine in routines {
    count_kode(
      @why3vc.lower_routine(context, pmodule, routine.1, routine.2),
      counts,
    )
  }
  for index = 0; index < 7; index = index + 1 {
    assert_true(counts[index] > 0)
  }
  assert_eq(counts[7], 0)
  assert_true(@why3vc.Kode::continue_normally().view() is Kcont(0))
}

///|
fn final_goal_name(task : @theory.Task) -> Bytes {
  let items = task.view().items
  guard !items.is_empty() &&
    items[items.length() - 1] is TheoryDecl(declaration) &&
    declaration.view() is Dprop(Pgoal, proposition, _) else {
    abort("VC task has no final goal")
  }
  proposition.view().name
}

///|
test "VC declarations precede concrete routines and suppress trivial goals" {
  let source =
    #|module Suppression
    #|  use int.Int
    #|  let passthrough (x : int) : int = x
    #|  let checked (x : int) : int
    #|    ensures { result = x }
    #|  = assert { x = x };
    #|    x
    #|end
  let (context, pmodule) = elaborate_test_module(source, b"vc-suppress.mlw")
  let generated = @why3vc.generate_module(context, pmodule)
  let items = generated.view().items
  let declaration_kinds : Array[Bytes] = []
  for item in items {
    match item {
      Udecl(PDpure([declaration])) => {
        guard declaration.view() is Dprop(Pgoal, proposition, _) else {
          fail("generated pure declaration is not a VC goal")
        }
        declaration_kinds.push(proposition.view().name)
      }
      Udecl(PDlet(symbol, _, _)) => declaration_kinds.push(symbol.view().name)
      _ => ()
    }
  }
  assert_eq(declaration_kinds, [b"passthrough", b"checked'vc", b"checked"])
  let tasks = @theory.split_theory(context, generated.pure_theory(), None)
  assert_eq(tasks.length(), 1)
  assert_eq(final_goal_name(tasks[0]), b"checked'vc")
}

///|
test "VC control attributes fail before expression lowering" {
  let source =
    #|module Control
    #|  let identity (x : int) : int
    #|    ensures { result = x }
    #|  = x
    #|end
  let (context, pmodule) = elaborate_test_module(source, b"vc-control.mlw")
  guard concrete_routines(pmodule) is [(routine, cty, _)] else {
    fail("expected one concrete routine")
  }
  let argument = cty.view().arguments[0]
  let controlled = @mlw.Expr::variable(argument, routine.view().origin, [
    b"vc:sp",
  ])
  try @why3vc.lower_routine(context, pmodule, cty, controlled) catch {
    @why3vc.VcError(diagnostic) =>
      assert_eq(diagnostic.kind, @why3vc.UnsupportedControlAttribute)
    _ => fail("control attribute raised the wrong error family")
  } noraise {
    _ => fail("control attribute unexpectedly reached WP generation")
  }
}
