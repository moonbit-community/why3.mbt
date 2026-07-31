// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn elaborate_test_module(
  source : String,
  filename : BytesView,
) -> (@identity.CompilationContext, @mlw.Pmodule) raise {
  let (context, _, pmodule) = elaborate_test_module_with_environment(
    source, filename,
  )
  (context, pmodule)
}

///|
fn elaborate_test_module_with_environment(
  source : String,
  filename : BytesView,
) -> (@identity.CompilationContext, @environment.Environment, @mlw.Pmodule) raise {
  guard @parser.parse_mlw_file(@utf8.encode(source)[:], filename~)
    is Modules([unit]) else {
    abort("VC test input did not parse as one module")
  }
  let context = @identity.CompilationContext::new()
  let environment = @stdlib.embedded_environment_in_context(context)
  (
    context,
    environment,
    @elab.elaborate_program_unit(context, environment, unit),
  )
}

///|
fn concrete_routines(
  pmodule : @mlw.Pmodule,
) -> Array[(@mlw.RoutineSymbol, @mlw.Cty, @mlw.Expr)] {
  let result = []
  for item in pmodule.view().items {
    if item is Udecl(PDlet(symbol, Cfun(cty, Some(body)), _, _)) {
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
    Kcase(_, branches) => {
      counts[3] = counts[3] + 1
      for branch in branches {
        count_kode(branch.1, counts)
      }
    }
    Klet(_, _, _) => counts[4] = counts[4] + 1
    Kval(_, _) => counts[5] = counts[5] + 1
    Kcut(_) => counts[6] = counts[6] + 1
    Kstop(_) => counts[7] = counts[7] + 1
    Kcont(_) => counts[8] = counts[8] + 1
    Khavoc(_, _, _) => ()
    Koff(_, inner) | Kmode(_, inner) | Kout(_, inner) | Kpush(_, inner) =>
      count_kode(inner, counts)
  }
}

///|
fn find_stop_with_explanation(
  kode : @why3vc.Kode,
  explanation : BytesView,
) -> @logic.Term? {
  match kode.view() {
    Kseq(first, _, second) | Kpar(first, second) =>
      match find_stop_with_explanation(first, explanation) {
        Some(term) => Some(term)
        None => find_stop_with_explanation(second, explanation)
      }
    Kif(_, yes, no) =>
      match find_stop_with_explanation(yes, explanation) {
        Some(term) => Some(term)
        None => find_stop_with_explanation(no, explanation)
      }
    Kcase(_, branches) => {
      for branch in branches {
        if find_stop_with_explanation(branch.1, explanation) is Some(term) {
          return Some(term)
        }
      }
      None
    }
    Koff(_, inner) | Kmode(_, inner) | Kout(_, inner) | Kpush(_, inner) =>
      find_stop_with_explanation(inner, explanation)
    Kstop(term) =>
      if term.attributes().any(attribute => attribute[:] == explanation) {
        Some(term)
      } else {
        None
      }
    Khavoc(_, _, _) | Klet(_, _, _) | Kval(_, _) | Kcut(_) | Kcont(_) => None
  }
}

///|
test "absurd VC stop keeps the expression source span" {
  let source =
    #|module AbsurdSpan
    #|  let impossible () : int = absurd
    #|end
  let (context, pmodule) = elaborate_test_module(source, b"absurd-span.mlw")
  guard concrete_routines(pmodule) is [(_, cty, body)] &&
    body.origin().source_span() is Some(absurd_span) else {
    fail("absurd fixture did not elaborate into a located routine body")
  }
  let kode = @why3vc.lower_routine(context, pmodule, cty, body)
  guard find_stop_with_explanation(kode, b"expl:unreachable point")
    is Some(stop) else {
    fail("absurd lowering did not produce an unreachable stop")
  }
  assert_eq(stop.source_span(), Some(absurd_span))
}

///|
fn kode_contains_explanation_offset(
  kode : @why3vc.Kode,
  wanted : BytesView,
) -> Bool {
  match kode.view() {
    Kseq(first, _, second) | Kpar(first, second) =>
      kode_contains_explanation_offset(first, wanted) ||
      kode_contains_explanation_offset(second, wanted)
    Kif(_, yes, no) =>
      kode_contains_explanation_offset(yes, wanted) ||
      kode_contains_explanation_offset(no, wanted)
    Kcase(_, branches) =>
      branches.any(branch => kode_contains_explanation_offset(branch.1, wanted))
    Koff(explanation, inner) =>
      explanation == wanted || kode_contains_explanation_offset(inner, wanted)
    Kmode(_, inner) | Kout(_, inner) | Kpush(_, inner) =>
      kode_contains_explanation_offset(inner, wanted)
    Khavoc(_, _, _)
    | Klet(_, _, _)
    | Kval(_, _)
    | Kcut(_)
    | Kstop(_)
    | Kcont(_) => false
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
  let counts = Array::make(9, 0)
  for routine in routines {
    count_kode(
      @why3vc.lower_routine(context, pmodule, routine.1, routine.2),
      counts,
    )
  }
  for index = 0; index < 3; index = index + 1 {
    assert_true(counts[index] > 0)
  }
  for index = 4; index < 8; index = index + 1 {
    assert_true(counts[index] > 0)
  }
  assert_eq(counts[3], 0)
  assert_eq(counts[8], 0)
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
      Udecl(PDpure([declaration], _)) => {
        guard declaration.view() is Dprop(Pgoal, proposition, _) else {
          fail("generated pure declaration is not a VC goal")
        }
        declaration_kinds.push(proposition.view().name)
      }
      Udecl(PDlet(symbol, _, _, _)) =>
        declaration_kinds.push(symbol.view().name)
      _ => ()
    }
  }
  assert_eq(declaration_kinds, [b"passthrough", b"checked'vc", b"checked"])
  let tasks = @theory.split_theory(context, generated.pure_theory(), None)
  assert_eq(tasks.length(), 1)
  assert_eq(final_goal_name(tasks[0]), b"checked'vc")
}

///|
test "VC closure orders free variables by Why3 symbol creation order" {
  let source =
    #|module VcFreeVariableOrder
    #|  use int.Int
    #|  use ref.Ref
    #|  val first : ref int
    #|  val second : ref int
    #|  let compare () : unit
    #|    ensures { !second < !first }
    #|  = ()
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-free-variable-order.mlw",
  )
  let first = pmodule.export_namespace().find_variable([b"first"], None)
  let second = pmodule.export_namespace().find_variable([b"second"], None)
  let generated = @why3vc.generate_module(context, pmodule)
  let mut goal : @logic.Term? = None
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) &&
      proposition.view().name == b"compare'vc" {
      goal = Some(formula)
    }
  }
  guard goal is Some(goal) &&
    goal.view() is Tquant(ForallQuantifier, binders, _, _) else {
    fail("VC goal did not close its global variables")
  }
  assert_eq(binders.length(), 2)
  assert_true(
    binders[0].semantic_id().local_id() < binders[1].semantic_id().local_id(),
  )
  assert_true(
    [binders[0].view().name, binders[1].view().name].contains(
      first.view().pure_symbol.view().name,
    ),
  )
  assert_true(
    [binders[0].view().name, binders[1].view().name].contains(
      second.view().pure_symbol.view().name,
    ),
  )
}

///|
fn contains_vc_mode(kode : @why3vc.Kode, wanted : @why3vc.VcMode) -> Bool {
  match kode.view() {
    Kmode(mode, inner) => mode == wanted || contains_vc_mode(inner, wanted)
    Kseq(first, _, second) =>
      contains_vc_mode(first, wanted) || contains_vc_mode(second, wanted)
    Kpar(left, right) =>
      contains_vc_mode(left, wanted) || contains_vc_mode(right, wanted)
    Kif(_, yes, no) =>
      contains_vc_mode(yes, wanted) || contains_vc_mode(no, wanted)
    Kcase(_, branches) =>
      branches.any(branch => contains_vc_mode(branch.1, wanted))
    Koff(_, inner) | Kout(_, inner) | Kpush(_, inner) =>
      contains_vc_mode(inner, wanted)
    Khavoc(_, _, _)
    | Klet(_, _, _)
    | Kval(_, _)
    | Kcut(_)
    | Kstop(_)
    | Kcont(_) => false
  }
}

///|
test "VC control attributes become local WP and SP mode boundaries" {
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
  let kode = @why3vc.lower_routine(context, pmodule, cty, controlled)
  assert_true(contains_vc_mode(kode, @why3vc.EfficientSp))
  ignore(@why3vc.classical_wp(context, pmodule, kode))
}

///|
fn contains_match_artifact(term : @logic.Term) -> Bool {
  match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => false
    Tapp(symbol, _, arguments) =>
      symbol.view().role is Projection || arguments.any(contains_match_artifact)
    Tif(condition, yes, no) =>
      contains_match_artifact(condition) ||
      contains_match_artifact(yes) ||
      contains_match_artifact(no)
    Tlet(_, value, body) =>
      contains_match_artifact(value) || contains_match_artifact(body)
    Tcase(_, _) => true
    Teps(_, body) => contains_match_artifact(body)
    Tquant(_, _, triggers, body) =>
      triggers.any(group => group.any(contains_match_artifact)) ||
      contains_match_artifact(body)
    Tbinop(_, left, right) =>
      contains_match_artifact(left) || contains_match_artifact(right)
    Tnot(inner) => contains_match_artifact(inner)
  }
}

///|
fn first_case_scrutinee_variable(
  term : @logic.Term,
) -> @logic.VSymbol? {
  match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => None
    Tapp(_, _, arguments) => {
      for argument in arguments {
        if first_case_scrutinee_variable(argument) is Some(variable) {
          return Some(variable)
        }
      }
      None
    }
    Tif(condition, yes, no) =>
      match first_case_scrutinee_variable(condition) {
        Some(variable) => Some(variable)
        None =>
          match first_case_scrutinee_variable(yes) {
            Some(variable) => Some(variable)
            None => first_case_scrutinee_variable(no)
          }
      }
    Tlet(_, value, body) =>
      match first_case_scrutinee_variable(value) {
        Some(variable) => Some(variable)
        None => first_case_scrutinee_variable(body)
      }
    Tcase(scrutinee, _) =>
      match scrutinee.view() {
        Tvar(variable) => Some(variable)
        _ => first_case_scrutinee_variable(scrutinee)
      }
    Teps(_, body) => first_case_scrutinee_variable(body)
    Tquant(_, _, triggers, body) => {
      for group in triggers {
        for trigger in group {
          if first_case_scrutinee_variable(trigger) is Some(variable) {
            return Some(variable)
          }
        }
      }
      first_case_scrutinee_variable(body)
    }
    Tbinop(_, left, right) =>
      match first_case_scrutinee_variable(left) {
        Some(variable) => Some(variable)
        None => first_case_scrutinee_variable(right)
      }
    Tnot(inner) => first_case_scrutinee_variable(inner)
  }
}

///|
test "eval_match expands constructor arguments in Why3 reverse order" {
  let source =
    #|module TupleMatchOrder
    #|  use option.Option
    #|  predicate marked (value : option int)
    #|  let inspect (x y z : option int) : unit =
    #|    match x, y, z with
    #|    | None, _, _ -> assert { marked x }
    #|    | _, None, _ -> assert { marked y }
    #|    | _, _, None -> assert { marked z }
    #|    | _ -> assert { marked x }
    #|    end
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-tuple-match-order.mlw",
  )
  let generated = @why3vc.generate_module(context, pmodule)
  let mut formula : @logic.Term? = None
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, goal) &&
      proposition.view().name == b"inspect'vc" {
      formula = Some(goal)
    }
  }
  guard formula is Some(formula) &&
    first_case_scrutinee_variable(formula) is Some(scrutinee) else {
    fail("tuple-match VC has no case scrutinee")
  }
  assert_eq(scrutinee.view().name, b"z")
}

///|
test "eval_match reduces record projections and constructor cases in VCs" {
  let source =
    #|module MatchReduction
    #|  type pair = { first : int; second : int }
    #|  function selected_field (value : pair) : int =
    #|    match value with
    #|    | { first = selected } -> selected
    #|    end
    #|
    #|  let projected (x : int) : int
    #|    ensures { result = first { first = x; second = 0 } }
    #|  = x
    #|
    #|  let selected (x : int) : int
    #|    ensures {
    #|      result = selected_field { first = x; second = 0 }
    #|    }
    #|  = x
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-match-reduction.mlw",
  )
  let generated = @why3vc.generate_module_with_options(
    context,
    pmodule,
    @why3vc.VcOptions::classical().with_keep_trace(false),
  )
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, _, formula) {
      formulas.push(formula)
    }
  }
  assert_eq(formulas.length(), 2)
  for formula in formulas {
    assert_false(contains_match_artifact(formula))
    assert_true(formula.view() is Ttrue)
  }
}

///|
fn has_exception_continuation(kode : @why3vc.Kode) -> Bool {
  match kode.view() {
    Kseq(first, index, second) =>
      index > 0 ||
      has_exception_continuation(first) ||
      has_exception_continuation(second)
    Kpar(left, right) =>
      has_exception_continuation(left) || has_exception_continuation(right)
    Kif(_, yes, no) =>
      has_exception_continuation(yes) || has_exception_continuation(no)
    Kcase(_, branches) =>
      branches.any(branch => has_exception_continuation(branch.1))
    Kcont(index) => index > 0
    Koff(_, inner) | Kmode(_, inner) | Kout(_, inner) | Kpush(_, inner) =>
      has_exception_continuation(inner)
    Khavoc(_, _, _) | Klet(_, _, _) | Kval(_, _) | Kcut(_) | Kstop(_) => false
  }
}

///|
test "exceptional continuations prove raises clauses and try handlers" {
  let source =
    #|module Exceptional
    #|  exception Stop int
    #|
    #|  let may_fail (x : int) : int
    #|    raises { Stop result -> result = x }
    #|  = raise Stop x
    #|
    #|  let caught (x : int) : int
    #|    ensures { result = x }
    #|  = try raise Stop x with Stop value -> value end
    #|end
  let (context, pmodule) = elaborate_test_module(source, b"vc-exceptional.mlw")
  let routines = concrete_routines(pmodule)
  assert_eq(routines.length(), 2)
  for routine in routines {
    assert_true(
      has_exception_continuation(
        @why3vc.lower_routine(context, pmodule, routine.1, routine.2),
      ),
    )
  }
  let generated = @why3vc.generate_module_with_options(
    context,
    pmodule,
    @why3vc.VcOptions::classical().with_keep_trace(false),
  )
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, _, formula) {
      formulas.push(formula)
    }
  }
  assert_eq(formulas.length(), 2)
  for formula in formulas {
    assert_true(formula.view() is Ttrue)
  }
}

///|
test "efficient WP carries normal and exceptional SP outcomes" {
  let source =
    #|module EfficientExceptional
    #|  use int.Int
    #|  exception Stop int
    #|
    #|  let absolute (x : int) : int
    #|    ensures { result >= 0 }
    #|  = if x >= 0 then x else -x
    #|
    #|  let caught (x : int) : int
    #|    ensures { result = x }
    #|  = [@vc:sp]
    #|    try raise Stop x with Stop value -> value end
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-efficient-exceptional.mlw",
  ) catch {
    @elab.ElabError(diagnostic) =>
      fail("efficient SP fixture failed to elaborate: \{diagnostic.message}")
    error => raise error
  }
  let routines = concrete_routines(pmodule)
  assert_eq(routines.length(), 2)
  let absolute_kode = @why3vc.lower_routine(
    context,
    pmodule,
    routines[0].1,
    routines[0].2,
  )
  let efficient_formula = @why3vc.efficient_wp(context, pmodule, absolute_kode)
  assert_true(term_contains_attribute(efficient_formula, b"case_split"))
  let generated = @why3vc.generate_module_with_options(
    context,
    pmodule,
    @why3vc.VcOptions::efficient(),
  )
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, _, formula) {
      formulas.push(formula)
    }
  }
  assert_eq(formulas.length(), 2)
  for formula in formulas {
    assert_false(formula.view() is Tfalse)
  }
}

///|
test "assignment havoc and while invariants reach classical WP" {
  let source =
    #|module Stateful
    #|  use int.Int
    #|  type cell = { mutable contents : int }
    #|
    #|  let set (value : cell) : unit
    #|    ensures { value.contents = 1 }
    #|    writes { value.contents }
    #|  = value.contents <- 1
    #|
    #|  let idle () : unit =
    #|    while false do
    #|      invariant { true }
    #|      variant { 0 }
    #|      ()
    #|    done;
    #|    for i = 0 to 2 do
    #|      invariant { 0 <= i }
    #|      check { i <= 2 }
    #|    done
    #|end
  let (context, pmodule) = elaborate_test_module(source, b"vc-stateful.mlw")
  let routines = concrete_routines(pmodule)
  assert_eq(routines.length(), 2)
  for routine in routines {
    ignore(@why3vc.lower_routine(context, pmodule, routine.1, routine.2)) catch {
      @theory.TheoryError(diagnostic) =>
        fail(
          "lowering \{@mlw.RoutineSymbol::view(routine.0).name} failed: \{diagnostic.message}",
        )
      error => raise error
    }
  }
  let generated = @why3vc.generate_module(context, pmodule)
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, _, formula) {
      formulas.push(formula)
    }
  }
  assert_eq(formulas.length(), 2)
  for formula in formulas {
    assert_false(formula.view() is Tfalse)
  }
}

///|
test "field-sensitive havoc preserves unwritten record fields" {
  let source =
    #|module FieldSensitiveHavoc
    #|  use int.Int
    #|
    #|  type pair = {
    #|    mutable left : int;
    #|    mutable right : int;
    #|  }
    #|
    #|  val abstract_set_left (value : pair) : unit
    #|    writes { value.left }
    #|    ensures { value.left = 1 }
    #|
    #|  let concrete_set_left (value : pair) : unit
    #|    writes { value.left }
    #|    ensures { value.left = 1 }
    #|    ensures { value.right = old value.right }
    #|  = value.left <- 1
    #|
    #|  let call_set_left (value : pair) : unit
    #|    writes { value.left }
    #|    ensures { value.right = old value.right }
    #|  = abstract_set_left value
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-field-sensitive-havoc.mlw",
  )
  let generated = @why3vc.generate_module_with_options(
    context,
    pmodule,
    @why3vc.VcOptions::classical().with_keep_trace(false),
  )
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) {
      if proposition.view().name == b"concrete_set_left'vc" ||
        proposition.view().name == b"call_set_left'vc" {
        formulas.push(formula)
      }
    }
  }
  assert_eq(formulas.length(), 2)
  for formula in formulas {
    assert_false(formula.view() is Tfalse)
    let count = term_logic_name_count(formula, b"right")
    if count < 4 {
      fail("field-sensitive havoc retained only \{count} right projections")
    }
  }
}

///|
fn term_contains_attribute(term : @logic.Term, wanted : BytesView) -> Bool {
  if term.attributes().any(attribute => attribute[:] == wanted) {
    return true
  }
  match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => false
    Tapp(_, _, arguments) =>
      arguments.any(argument => term_contains_attribute(argument, wanted))
    Tif(condition, yes, no) =>
      term_contains_attribute(condition, wanted) ||
      term_contains_attribute(yes, wanted) ||
      term_contains_attribute(no, wanted)
    Tlet(_, value, body) =>
      term_contains_attribute(value, wanted) ||
      term_contains_attribute(body, wanted)
    Tcase(scrutinee, branches) =>
      term_contains_attribute(scrutinee, wanted) ||
      branches.any(branch => term_contains_attribute(branch.view().body, wanted))
    Teps(_, body) => term_contains_attribute(body, wanted)
    Tquant(_, _, triggers, body) =>
      triggers.any(group => {
        group.any(trigger => term_contains_attribute(trigger, wanted))
      }) ||
      term_contains_attribute(body, wanted)
    Tbinop(_, left, right) =>
      term_contains_attribute(left, wanted) ||
      term_contains_attribute(right, wanted)
    Tnot(inner) => term_contains_attribute(inner, wanted)
  }
}

///|
fn attributed_term_contains_unknown_integer(
  term : @logic.Term,
  wanted : BytesView,
  attributed? : Bool = false,
) -> Bool {
  let attributed = attributed ||
    term.attributes().any(attribute => attribute[:] == wanted)
  if attributed && term.view() is Tconst(ConstInt({ kind: ILitUnk, .. })) {
    return true
  }
  match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => false
    Tapp(_, _, arguments) =>
      arguments.any(argument => {
        attributed_term_contains_unknown_integer(argument, wanted, attributed~)
      })
    Tif(condition, yes, no) =>
      attributed_term_contains_unknown_integer(condition, wanted, attributed~) ||
      attributed_term_contains_unknown_integer(yes, wanted, attributed~) ||
      attributed_term_contains_unknown_integer(no, wanted, attributed~)
    Tlet(_, value, body) =>
      attributed_term_contains_unknown_integer(value, wanted, attributed~) ||
      attributed_term_contains_unknown_integer(body, wanted, attributed~)
    Tcase(scrutinee, branches) =>
      attributed_term_contains_unknown_integer(scrutinee, wanted, attributed~) ||
      branches.any(branch => {
        attributed_term_contains_unknown_integer(
          branch.view().body,
          wanted,
          attributed~,
        )
      })
    Teps(_, body) =>
      attributed_term_contains_unknown_integer(body, wanted, attributed~)
    Tquant(_, _, triggers, body) =>
      triggers.any(group => {
        group.any(trigger => {
          attributed_term_contains_unknown_integer(trigger, wanted, attributed~)
        })
      }) ||
      attributed_term_contains_unknown_integer(body, wanted, attributed~)
    Tbinop(_, left, right) =>
      attributed_term_contains_unknown_integer(left, wanted, attributed~) ||
      attributed_term_contains_unknown_integer(right, wanted, attributed~)
    Tnot(inner) =>
      attributed_term_contains_unknown_integer(inner, wanted, attributed~)
  }
}

///|
fn attributed_term_span(
  term : @logic.Term,
  wanted : BytesView,
) -> @identity.SourceSpan? {
  if term.attributes().any(attribute => attribute[:] == wanted) {
    return term.source_span()
  }
  match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => None
    Tapp(_, _, arguments) => {
      for argument in arguments {
        if attributed_term_span(argument, wanted) is Some(span) {
          return Some(span)
        }
      }
      None
    }
    Tif(condition, yes, no) =>
      match attributed_term_span(condition, wanted) {
        Some(span) => Some(span)
        None =>
          match attributed_term_span(yes, wanted) {
            Some(span) => Some(span)
            None => attributed_term_span(no, wanted)
          }
      }
    Tlet(_, value, body) =>
      match attributed_term_span(value, wanted) {
        Some(span) => Some(span)
        None => attributed_term_span(body, wanted)
      }
    Tcase(scrutinee, branches) => {
      match attributed_term_span(scrutinee, wanted) {
        Some(span) => return Some(span)
        None => ()
      }
      for branch in branches {
        if attributed_term_span(branch.view().body, wanted) is Some(span) {
          return Some(span)
        }
      }
      None
    }
    Teps(_, body) => attributed_term_span(body, wanted)
    Tquant(_, _, triggers, body) => {
      for group in triggers {
        for trigger in group {
          if attributed_term_span(trigger, wanted) is Some(span) {
            return Some(span)
          }
        }
      }
      attributed_term_span(body, wanted)
    }
    Tbinop(_, left, right) =>
      match attributed_term_span(left, wanted) {
        Some(span) => Some(span)
        None => attributed_term_span(right, wanted)
      }
    Tnot(inner) => attributed_term_span(inner, wanted)
  }
}

///|
test "for-loop bounds preserve Why3 locations, literals, and offset explanations" {
  let source =
    #|module ForLoopMetadata
    #|  use int.Int
    #|
    #|  let scan (last : int) : unit
    #|    requires { 0 <= last }
    #|    ensures { last >= 0 }
    #|  =
    #|    for index = 0 to last do
    #|      invariant { 0 <= index }
    #|      ()
    #|    done;
    #|    ()
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-for-loop-metadata.mlw",
  )
  let generated = @why3vc.generate_module(context, pmodule)
  let mut goal : @logic.Term? = None
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) &&
      proposition.view().name == b"scan'vc" {
      goal = Some(formula)
    }
  }
  guard goal is Some(goal) else { fail("for-loop fixture produced no VC goal") }
  guard attributed_term_span(goal, b"expl:loop bounds") is Some(span) else {
    fail("for-loop bounds lost their source span")
  }
  let view = span.view()
  assert_eq(view.start_line, 8L)
  assert_eq(view.start_column, 4L)
  assert_eq(view.end_line, 11L)
  assert_eq(view.end_column, 8L)
  assert_true(
    attributed_term_contains_unknown_integer(goal, b"expl:loop bounds"),
  )
  let routines = concrete_routines(pmodule)
  assert_eq(routines.length(), 1)
  assert_true(
    kode_contains_explanation_offset(
      @why3vc.lower_routine(context, pmodule, routines[0].1, routines[0].2),
      b"expl:out of loop bounds",
    ),
  )
}

///|
fn term_contains_logic_name(term : @logic.Term, wanted : BytesView) -> Bool {
  match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => false
    Tapp(symbol, _, arguments) =>
      symbol.view().name[:] == wanted ||
      arguments.any(argument => term_contains_logic_name(argument, wanted))
    Tif(condition, yes, no) =>
      term_contains_logic_name(condition, wanted) ||
      term_contains_logic_name(yes, wanted) ||
      term_contains_logic_name(no, wanted)
    Tlet(_, value, body) =>
      term_contains_logic_name(value, wanted) ||
      term_contains_logic_name(body, wanted)
    Tcase(scrutinee, branches) =>
      term_contains_logic_name(scrutinee, wanted) ||
      branches.any(branch => {
        term_contains_logic_name(branch.view().body, wanted)
      })
    Teps(_, body) => term_contains_logic_name(body, wanted)
    Tquant(_, _, triggers, body) =>
      triggers.any(group => {
        group.any(trigger => term_contains_logic_name(trigger, wanted))
      }) ||
      term_contains_logic_name(body, wanted)
    Tbinop(_, left, right) =>
      term_contains_logic_name(left, wanted) ||
      term_contains_logic_name(right, wanted)
    Tnot(inner) => term_contains_logic_name(inner, wanted)
  }
}

///|
fn term_logic_name_count(term : @logic.Term, wanted : BytesView) -> Int {
  match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => 0
    Tapp(symbol, _, arguments) => {
      let mut count = if symbol.view().name[:] == wanted { 1 } else { 0 }
      for argument in arguments {
        count = count + term_logic_name_count(argument, wanted)
      }
      count
    }
    Tif(condition, yes, no) =>
      term_logic_name_count(condition, wanted) +
      term_logic_name_count(yes, wanted) +
      term_logic_name_count(no, wanted)
    Tlet(_, value, body) =>
      term_logic_name_count(value, wanted) + term_logic_name_count(body, wanted)
    Tcase(scrutinee, branches) => {
      let mut count = term_logic_name_count(scrutinee, wanted)
      for branch in branches {
        count = count + term_logic_name_count(branch.view().body, wanted)
      }
      count
    }
    Teps(_, body) => term_logic_name_count(body, wanted)
    Tquant(_, _, triggers, body) => {
      let mut count = term_logic_name_count(body, wanted)
      for group in triggers {
        for trigger in group {
          count = count + term_logic_name_count(trigger, wanted)
        }
      }
      count
    }
    Tbinop(_, left, right) =>
      term_logic_name_count(left, wanted) + term_logic_name_count(right, wanted)
    Tnot(inner) => term_logic_name_count(inner, wanted)
  }
}

///|
fn bytes_start_with(value : BytesView, prefix : BytesView) -> Bool {
  value.length() >= prefix.length() && value[:prefix.length()] == prefix
}

///|
fn variable_has_attribute_prefix(
  variable : @logic.VSymbol,
  prefix : BytesView,
) -> Bool {
  variable.view().origin
  .attributes()
  .any(attribute => bytes_start_with(attribute, prefix))
}

///|
fn term_contains_variable_attribute_prefix(
  term : @logic.Term,
  prefix : BytesView,
) -> Bool {
  match term.view() {
    Tvar(variable) => variable_has_attribute_prefix(variable, prefix)
    Tconst(_) | Ttrue | Tfalse => false
    Tapp(_, _, arguments) =>
      arguments.any(argument => {
        term_contains_variable_attribute_prefix(argument, prefix)
      })
    Tif(condition, yes, no) =>
      term_contains_variable_attribute_prefix(condition, prefix) ||
      term_contains_variable_attribute_prefix(yes, prefix) ||
      term_contains_variable_attribute_prefix(no, prefix)
    Tlet(variable, value, body) =>
      variable_has_attribute_prefix(variable, prefix) ||
      term_contains_variable_attribute_prefix(value, prefix) ||
      term_contains_variable_attribute_prefix(body, prefix)
    Tcase(scrutinee, branches) =>
      term_contains_variable_attribute_prefix(scrutinee, prefix) ||
      branches.any(branch => {
        term_contains_variable_attribute_prefix(branch.view().body, prefix)
      })
    Teps(variable, body) =>
      variable_has_attribute_prefix(variable, prefix) ||
      term_contains_variable_attribute_prefix(body, prefix)
    Tquant(_, binders, triggers, body) =>
      binders.any(variable => variable_has_attribute_prefix(variable, prefix)) ||
      triggers.any(group => {
        group.any(trigger => {
          term_contains_variable_attribute_prefix(trigger, prefix)
        })
      }) ||
      term_contains_variable_attribute_prefix(body, prefix)
    Tbinop(_, left, right) =>
      term_contains_variable_attribute_prefix(left, prefix) ||
      term_contains_variable_attribute_prefix(right, prefix)
    Tnot(inner) => term_contains_variable_attribute_prefix(inner, prefix)
  }
}

///|
test "recursive groups and local recursion emit variant-decrease goals" {
  let source =
    #|module RecursiveVc
    #|  use int.Int
    #|  let rec even (value : int) : bool
    #|    variant { value }
    #|  = if value = 0 then true else odd (value - 1)
    #|  with odd (value : int) : bool
    #|    variant { value }
    #|  = if value = 0 then false else even (value - 1)
    #|
    #|  let outer (base : int) : int =
    #|    let rec descend (value : int) : int
    #|      variant { value }
    #|    = if value = 0 then base else descend (value - 1)
    #|    in descend 2
    #|end
  let (context, pmodule) = elaborate_test_module(source, b"vc-recursion.mlw")
  let generated = @why3vc.generate_module(context, pmodule)
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, _, formula) {
      formulas.push(formula)
    }
  }
  assert_eq(formulas.length(), 3)
  for formula in formulas {
    assert_true(term_contains_attribute(formula, b"expl:variant decrease"))
    assert_false(formula.view() is Tfalse)
  }
}

///|
test "local aliases of recursive routines retain variant-decrease handling" {
  let source =
    #|module RecursiveAliasVc
    #|  type tree = Leaf | Node tree
    #|  let rec lemma walk (tree : tree) : unit
    #|    variant { tree }
    #|  = let ghost again = walk in
    #|    match tree with
    #|    | Leaf -> ()
    #|    | Node child -> again child
    #|    end
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-recursive-alias.mlw",
  )
  let generated = @why3vc.generate_module(context, pmodule)
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, _, formula) {
      formulas.push(formula)
    }
  }
  assert_eq(formulas.length(), 1)
  assert_true(term_contains_attribute(formulas[0], b"expl:variant decrease"))
}

///|
test "default algebraic orders and custom relation accessibility reach VCs" {
  let source =
    #|module VariantOrders
    #|  use int.Int
    #|
    #|  type chain = Stop | Step chain
    #|
    #|  let rec depth (value : chain) : int
    #|    variant { value }
    #|  = match value with
    #|    | Stop -> 0
    #|    | Step tail -> depth tail
    #|    end
    #|
    #|  predicate rel (x y : int) = x < y /\ x >= 0
    #|
    #|  let rec custom (value : int) : int
    #|    variant { value with rel }
    #|  = if value = 0 then 0 else custom (value - 1)
    #|end
  let (context, environment, pmodule) = elaborate_test_module_with_environment(
    source, b"vc-variant-orders.mlw",
  ) catch {
    @elab.ElabError(diagnostic) =>
      fail("variant-order elaboration failed: \{diagnostic.message}")
    error => raise error
  }
  let mut integer_theory : @theory.Theory? = None
  for theory in pmodule.pure_theory().used_theories() {
    let key = theory.key().view()
    if key.path == [b"int"] && key.name == b"Int" {
      integer_theory = Some(theory)
      break
    }
  }
  guard integer_theory is Some(integer_theory) else {
    fail("variant-order module lost int.Int")
  }
  let generated = @why3vc.generate_module_with_support(
    context,
    pmodule,
    integer_theory,
    environment.well_founded_module().pure_theory(),
  )
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) {
      formulas.push((proposition.view().name, formula))
    }
  }
  assert_eq(formulas.length(), 2)
  assert_eq(formulas[0].0, b"depth'vc")
  assert_true(contains_match_artifact(formulas[0].1))
  assert_eq(formulas[1].0, b"custom'vc")
  assert_true(term_contains_logic_name(formulas[1].1, b"acc"))
}

///|
test "type invariants generate inhabitance and concrete witness VCs" {
  let source =
    #|module TypeInvariantVc
    #|  use int.Int
    #|
    #|  type inhabited = { value : int }
    #|    invariant { value >= 0 }
    #|
    #|  type witnessed = { content : int }
    #|    invariant { content = 0 }
    #|    by { content = 0 }
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-type-invariants.mlw",
  )
  let generated = @why3vc.generate_module(context, pmodule)
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) {
      formulas.push((proposition.view().name, formula))
    }
  }
  assert_eq(formulas.length(), 2)
  assert_eq(formulas[0].0, b"inhabited'vc")
  assert_true(term_contains_attribute(formulas[0].1, b"expl:type invariant"))
  assert_eq(formulas[1].0, b"witnessed'vc")
  assert_true(term_contains_attribute(formulas[1].1, b"expl:type invariant"))
  assert_false(formulas[1].1.view() is Tfalse)
}

///|
test "multi-field type witnesses resolve hidden tuple constructors" {
  let source =
    #|module TupleWitnessVc
    #|  use int.Int
    #|
    #|  type witnessed = { first : int; second : int; third : int }
    #|    invariant { first + second + third = 0 }
    #|    by { first = 0; second = 0; third = 0 }
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-hidden-tuple-witness.mlw",
  )
  let generated = @why3vc.generate_module(context, pmodule)
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) {
      formulas.push((proposition.view().name, formula))
    }
  }
  assert_eq(formulas.length(), 1)
  assert_eq(formulas[0].0, b"witnessed'vc")
  assert_true(term_contains_attribute(formulas[0].1, b"expl:type invariant"))
  assert_false(formulas[0].1.view() is Tfalse)
}

///|
test "record writes prove substituted type invariants before state havoc" {
  let source =
    #|module TypeInvariantWrite
    #|  use int.Int
    #|
    #|  type limited = { mutable amount : int }
    #|    invariant { amount >= 0 }
    #|    by { amount = 0 }
    #|
    #|  let invalidate (value : limited) : unit
    #|    writes { value.amount }
    #|  = value.amount <- -1
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-type-invariant-write.mlw",
  )
  let generated = @why3vc.generate_module(context, pmodule)
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) {
      formulas.push((proposition.view().name, formula))
    }
  }
  assert_eq(formulas.length(), 2)
  assert_eq(formulas[1].0, b"invalidate'vc")
  assert_true(term_contains_attribute(formulas[1].1, b"expl:type invariant"))
  assert_false(formulas[1].1.view() is Ttrue)
}

///|
test "typeinv pins permit temporarily broken records until commit" {
  let source =
    #|module TypeInvariantCommit
    #|  use int.Int
    #|
    #|  type bounded = {
    #|    mutable lower : int;
    #|    mutable upper : int;
    #|  }
    #|    invariant { lower <= upper }
    #|    by { lower = 0; upper = 0 }
    #|
    #|  let normalize (value : bounded) : unit
    #|    writes { value.lower, value.upper }
    #|    ensures { value.lower = 1 /\ value.upper = 1 }
    #|  = value.lower <- 1;
    #|    value.upper <- 1
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-type-invariant-commit.mlw",
  )
  let generated = @why3vc.generate_module(context, pmodule)
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) {
      formulas.push((proposition.view().name, formula))
    }
  }
  assert_eq(formulas.length(), 2)
  assert_eq(formulas[1].0, b"normalize'vc")
  assert_false(formulas[1].1.view() is Tfalse)
  assert_true(term_contains_attribute(formulas[1].1, b"expl:type invariant"))
  assert_false(term_contains_logic_name(formulas[1].1, b"valid"))
}

///|
test "typeinv follows fragile records through records and sum branches" {
  let source =
    #|module NestedTypeInvariantCommit
    #|  use int.Int
    #|
    #|  type bounded = {
    #|    mutable lower : int;
    #|    mutable upper : int;
    #|  }
    #|    invariant { lower <= upper }
    #|    by { lower = 0; upper = 0 }
    #|
    #|  type envelope = { payload : bounded }
    #|  type choice = Empty | Full bounded
    #|
    #|  let normalize_nested (value : envelope) : unit
    #|    writes { value.payload.lower, value.payload.upper }
    #|  = value.payload.lower <- 1;
    #|    value.payload.upper <- 1
    #|
    #|  let normalize_choice (value : choice) : unit
    #|  = match value with
    #|    | Empty -> ()
    #|    | Full payload ->
    #|        payload.lower <- 1;
    #|        payload.upper <- 1
    #|    end
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-type-invariant-nested.mlw",
  )
  let generated = @why3vc.generate_module(context, pmodule)
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) {
      formulas.push((proposition.view().name, formula))
    }
  }
  assert_true(formulas.length() >= 3)
  assert_true(formulas.any(entry => entry.0 == b"normalize_nested'vc"))
  assert_true(formulas.any(entry => entry.0 == b"normalize_choice'vc"))
  for entry in formulas {
    assert_false(entry.1.view() is Tfalse)
    assert_false(term_contains_logic_name(entry.1, b"valid"))
  }
}

///|
test "typeinv commits aliases and values crossing abstract call boundaries" {
  let source =
    #|module TypeInvariantBoundaries
    #|  use int.Int
    #|
    #|  type bounded = {
    #|    mutable lower : int;
    #|    mutable upper : int;
    #|  }
    #|    invariant { lower <= upper }
    #|    by { lower = 0; upper = 0 }
    #|
    #|  val observe (value : bounded) : unit
    #|
    #|  let alias_commit (value other : bounded) : unit
    #|    writes { value.lower, value.upper }
    #|  = value.lower <- 1;
    #|    assume { value = other };
    #|    assert { value.lower = other.lower };
    #|    value.upper <- 1
    #|
    #|  let call_while_broken (value : bounded) : unit
    #|    writes { value.lower, value.upper }
    #|  = value.lower <- 1;
    #|    observe value;
    #|    value.upper <- 1
    #|
    #|  let call_after_restore (value : bounded) : unit
    #|    writes { value.lower, value.upper }
    #|  = value.lower <- 1;
    #|    value.upper <- 1;
    #|    observe value
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-type-invariant-boundaries.mlw",
  )
  let generated = @why3vc.generate_module(context, pmodule)
  let formulas = []
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) {
      formulas.push((proposition.view().name, formula))
    }
  }
  for
    expected in [
      b"alias_commit'vc", b"call_while_broken'vc", b"call_after_restore'vc",
    ] {
    let mut selected : @logic.Term? = None
    for entry in formulas {
      if entry.0 == expected {
        selected = Some(entry.1)
        break
      }
    }
    guard selected is Some(formula) else {
      fail("type-invariant boundary fixture lost \\{expected}")
    }
    assert_false(formula.view() is Tfalse)
    assert_true(term_contains_attribute(formula, b"expl:type invariant"))
    assert_false(term_contains_logic_name(formula, b"valid"))
  }
}

///|
test "divergent controls expose or suppress termination obligations" {
  let source =
    #|module DivergenceControls
    #|  let checked () : unit
    #|  = while true do
    #|      invariant { true }
    #|      ()
    #|    done
    #|
    #|  let accepted () : unit
    #|  = [@vc:divergent]
    #|    while true do
    #|      invariant { true }
    #|      ()
    #|    done
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-divergence-controls.mlw",
  )
  let routines = concrete_routines(pmodule)
  guard routines.length() == 2 else {
    fail("divergence-control fixture lost its concrete routines")
  }
  let mut accepted_body : @mlw.Expr? = None
  for routine in routines {
    if routine.0.view().name == b"accepted" {
      accepted_body = Some(routine.2)
    }
  }
  guard accepted_body is Some(accepted_body) else {
    fail("divergence-control fixture lost accepted")
  }
  assert_true(accepted_body.view() is Ewhile(_, _, _, _))
  assert_true(
    accepted_body.attributes().any(attribute => attribute == b"vc:divergent"),
  )
  let generated = @why3vc.generate_module(context, pmodule)
  let mut checked : @logic.Term? = None
  let mut accepted : @logic.Term? = None
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) {
      if proposition.view().name == b"checked'vc" {
        checked = Some(formula)
      } else if proposition.view().name == b"accepted'vc" {
        accepted = Some(formula)
      }
    }
  }
  guard checked is Some(formula) else {
    fail("divergent loop lost its termination VC")
  }
  assert_true(term_contains_attribute(formula, b"expl:termination"))
  match accepted {
    Some(formula) =>
      assert_false(term_contains_attribute(formula, b"expl:termination"))
    None => ()
  }
}

///|
test "white-box trailing contracts are proved against their bodies" {
  let source =
    #|module WhiteBoxContracts
    #|  use int.Int
    #|
    #|  let valid (x : int) : int
    #|  = x ensures { result = x }
    #|
    #|  let invalid (x : int) : int
    #|  = x ensures { result = x + 1 }
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-white-box-contracts.mlw",
  )
  let generated = @why3vc.generate_module_with_options(
    context,
    pmodule,
    @why3vc.VcOptions::classical().with_keep_trace(false),
  )
  let mut valid : @logic.Term? = None
  let mut invalid : @logic.Term? = None
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) {
      if proposition.view().name == b"valid'vc" {
        valid = Some(formula)
      } else if proposition.view().name == b"invalid'vc" {
        invalid = Some(formula)
      }
    }
  }
  match valid {
    Some(formula) => assert_true(formula.view() is Ttrue)
    None => ()
  }
  guard invalid is Some(formula) else {
    fail("invalid white-box postcondition was assumed instead of proved")
  }
  assert_true(term_contains_attribute(formula, b"expl:postcondition"))
  assert_false(formula.view() is Ttrue)
}

///|
test "trace and match-evaluation VC options follow upstream controls" {
  let source =
    #|module VcEvaluationControls
    #|  use int.Int
    #|
    #|  type pair = { first : int; second : int }
    #|
    #|  val opaque (x : int) : int
    #|    ensures { result = x }
    #|
    #|  let traced (x : int) : int
    #|    ensures { result = first { first = x; second = 0 } }
    #|  = opaque x
    #|
    #|  let untraced (x : int) : int
    #|    ensures { result = x }
    #|  = [@vc:do_not_keep_trace] opaque x
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-evaluation-controls.mlw",
  )
  let generated = @why3vc.generate_module(context, pmodule)
  let mut traced : @logic.Term? = None
  let mut untraced : @logic.Term? = None
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) {
      if proposition.view().name == b"traced'vc" {
        traced = Some(formula)
      } else if proposition.view().name == b"untraced'vc" {
        untraced = Some(formula)
      }
    }
  }
  guard traced is Some(traced_formula) && untraced is Some(untraced_formula) else {
    fail("trace-control routines lost their VCs")
  }
  assert_true(
    term_contains_variable_attribute_prefix(traced_formula, b"model_trace:"),
  )
  assert_false(
    term_contains_variable_attribute_prefix(untraced_formula, b"model_trace:"),
  )
  let unevaluated = @why3vc.generate_module_with_options(
    context,
    pmodule,
    @why3vc.VcOptions::classical()
    .with_keep_trace(false)
    .with_match_evaluation(false),
  )
  let mut retained_match_artifact = false
  for item in unevaluated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) &&
      proposition.view().name == b"traced'vc" {
      retained_match_artifact = contains_match_artifact(formula)
    }
  }
  assert_true(retained_match_artifact)
}

///|
fn term_epsilon_count(term : @logic.Term) -> Int {
  match term.view() {
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => 0
    Tapp(_, _, arguments) =>
      arguments.fold(init=0, fn(total, argument) {
        total + term_epsilon_count(argument)
      })
    Tif(condition, yes, no) =>
      term_epsilon_count(condition) +
      term_epsilon_count(yes) +
      term_epsilon_count(no)
    Tlet(_, value, body) =>
      term_epsilon_count(value) + term_epsilon_count(body)
    Tcase(scrutinee, branches) =>
      term_epsilon_count(scrutinee) +
      branches.fold(init=0, fn(total, branch) {
        total + term_epsilon_count(branch.view().body)
      })
    Teps(_, body) => 1 + term_epsilon_count(body)
    Tquant(_, _, triggers, body) =>
      triggers.fold(init=term_epsilon_count(body), fn(total, group) {
        total +
        group.fold(init=0, fn(group_total, trigger) {
          group_total + term_epsilon_count(trigger)
        })
      })
    Tbinop(_, left, right) =>
      term_epsilon_count(left) + term_epsilon_count(right)
    Tnot(inner) => term_epsilon_count(inner)
  }
}

///|
test "functional postconditions become epsilon-defined values" {
  let source =
    #|module FunctionalPost
    #|  use int.Int
    #|
    #|  let ghost function add_from (base : int) : int -> int =
    #|    fun value -> base + value
    #|end
  let (context, pmodule) = elaborate_test_module(
    source, b"vc-functional-post.mlw",
  )
  let generated = @why3vc.generate_module(context, pmodule)
  let mut goal : @logic.Term? = None
  for item in generated.view().items {
    if item is Udecl(PDpure([declaration], _)) &&
      declaration.view() is Dprop(Pgoal, proposition, formula) &&
      proposition.view().name == b"add_from'vc" {
      goal = Some(formula)
    }
  }
  guard goal is Some(goal) else {
    fail("functional definition lost its VC")
  }
  assert_true(term_epsilon_count(goal) >= 1)
}
