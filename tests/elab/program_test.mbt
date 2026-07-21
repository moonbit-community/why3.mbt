// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn parsed_program_unit(
  source : String,
  filename : BytesView,
) -> @parser.MlwModule raise {
  guard @parser.parse_mlw_file(@utf8.encode(source)[:], filename~)
    is Modules([unit]) else {
    abort("program test input did not parse as one named unit")
  }
  unit
}

///|
fn program_declarations(
  pmodule : @mlw.Pmodule,
) -> Array[@mlw.ProgramDeclaration] {
  let result : Array[@mlw.ProgramDeclaration] = []
  for item in pmodule.view().items {
    if item is Udecl(declaration) {
      result.push(declaration)
    }
  }
  result
}

///|
test "program Real operator keeps the frozen routine identity and ANF proxy" {
  let source =
    #|module ProgramReal
    #|  use real.Real
    #|  let plus_zero (x : real) : real
    #|    ensures { result = x }
    #|  = x + 0.0
    #|end
  let context = @identity.CompilationContext::new()
  let frozen = @stdlib.minimal_env(context)
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    frozen.semantic_environment(),
    parsed_program_unit(source, b"program-real.mlw"),
  )
  let declarations = program_declarations(pmodule)
  guard declarations is [PDlet(_, Cfun(cty, Some(body)), _)] else {
    fail("expected one concrete program routine")
  }
  assert_eq(cty.view().arguments.length(), 1)
  assert_eq(cty.view().postconditions.length(), 1)
  guard body.view() is Elet(_, value, call, _) else {
    fail("real literal argument did not receive an ANF proxy")
  }
  assert_true(value.view() is Econst(_, _))
  guard call.view() is EroutineCall(symbol, arguments, _) else {
    fail("real addition was not a routine call")
  }
  assert_eq(arguments.length(), 2)
  assert_true(symbol == frozen.handles().view().real_add)
  assert_true(symbol.view().logic is RLls(_))
}

///|
test "postcondition result shadows an equally named program parameter" {
  let source =
    #|module Shadow
    #|  use int.Int
    #|  let shadow (result : int) : int
    #|    ensures { result = 0 }
    #|  = result
    #|end
  let context = @identity.CompilationContext::new()
  let frozen = @stdlib.minimal_env(context)
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    frozen.semantic_environment(),
    parsed_program_unit(source, b"program-shadow.mlw"),
  )
  guard program_declarations(pmodule) is [PDlet(_, Cfun(cty, Some(body)), _)] else {
    fail("expected one concrete shadowing routine")
  }
  let argument = cty.view().arguments[0]
  let post = cty.view().postconditions[0].view()
  let free = post.formula.free_variables()
  assert_true(free.any(variable => variable == post.result))
  assert_true(!free.any(variable => variable == argument.view().pure_symbol))
  assert_true(body.view() is Evar(variable, _) && variable == argument)
}

///|
fn expect_program_elaboration_kind(
  source : String,
  filename : BytesView,
  expected : @why3_elab.ElabErrorKind,
) -> Unit raise {
  let context = @identity.CompilationContext::new()
  let frozen = @stdlib.minimal_env(context)
  try
    @why3_elab.elaborate_program_unit(
      context,
      frozen.semantic_environment(),
      parsed_program_unit(source, filename),
    )
  catch {
    @why3_elab.ElabError(diagnostic) => assert_eq(diagnostic.kind, expected)
    _ => fail("program test raised an unexpected error family")
  } noraise {
    _ => fail("expected program elaboration to fail")
  }
}

///|
test "program routines reject residual polymorphism and result mismatches" {
  let polymorphic =
    #|module Polymorphic
    #|  let identity (value : 'a) : 'a = value
    #|end
  expect_program_elaboration_kind(
    polymorphic,
    b"program-polymorphic.mlw",
    @why3_elab.TypeFailure(PolymorphicProgramRoutine),
  )
  let mismatch =
    #|module Mismatch
    #|  let mismatch () : int = true
    #|end
  expect_program_elaboration_kind(
    mismatch,
    b"program-mismatch.mlw",
    @why3_elab.TypeFailure(TypeMismatch),
  )
}

///|
test "program contracts are checked as formulas against the result type" {
  let invalid_requires =
    #|module InvalidRequires
    #|  let invalid (x : int) : int
    #|    requires { x }
    #|  = x
    #|end
  expect_program_elaboration_kind(
    invalid_requires,
    b"program-invalid-requires.mlw",
    @why3_elab.TypeFailure(TypeMismatch),
  )
  let invalid_ensures =
    #|module InvalidEnsures
    #|  let invalid () : int
    #|    ensures { result = true }
    #|  = 0
    #|end
  expect_program_elaboration_kind(
    invalid_ensures,
    b"program-invalid-ensures.mlw",
    @why3_elab.TypeFailure(TypeMismatch),
  )
}

///|
test "program conditionals and routine calls enforce monomorphic types" {
  let branch_mismatch =
    #|module BranchMismatch
    #|  let choose () : int = if true then 0 else false
    #|end
  expect_program_elaboration_kind(
    branch_mismatch,
    b"program-branch-mismatch.mlw",
    @why3_elab.TypeFailure(TypeMismatch),
  )
  let arity_mismatch =
    #|module CallArity
    #|  val combine (left right : int) : int
    #|  let invalid (value : int) : int = combine value
    #|end
  expect_program_elaboration_kind(
    arity_mismatch,
    b"program-call-arity.mlw",
    @why3_elab.TypeFailure(ArityMismatch),
  )
  let argument_mismatch =
    #|module CallType
    #|  val identity (value : int) : int
    #|  let invalid () : int = identity true
    #|end
  expect_program_elaboration_kind(
    argument_mismatch,
    b"program-call-type.mlw",
    @why3_elab.TypeFailure(TypeMismatch),
  )
}

///|
test "trusted polymorphic equality has two monomorphic call instances" {
  let source =
    #|module TrustedPolymorphism
    #|  let int_reflexive (value : int) : bool = value = value
    #|  let bool_reflexive (value : bool) : bool = value = value
    #|end
  let context = @identity.CompilationContext::new()
  let frozen = @stdlib.minimal_env(context)
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    frozen.semantic_environment(),
    parsed_program_unit(source, b"program-trusted-polymorphism.mlw"),
  )
  guard program_declarations(pmodule)
    is [
      PDlet(_, Cfun(_, Some(int_body)), _),
      PDlet(_, Cfun(_, Some(bool_body)), _),
    ] else {
    fail("expected two concrete equality routines")
  }
  guard int_body.view() is EpureApp(int_equality, int_arguments, int_ity) &&
    bool_body.view() is EpureApp(bool_equality, bool_arguments, bool_ity) else {
    fail("trusted equality did not elaborate as pure applications")
  }
  assert_true(int_equality == bool_equality)
  assert_eq(int_arguments.length(), 2)
  assert_eq(bool_arguments.length(), 2)
  assert_true(int_arguments[0].view().ity != bool_arguments[0].view().ity)
  assert_true(int_ity == bool_ity)
}

///|
test "loop syntax is classified before unsupported imports are resolved" {
  let loop_source =
    #|module Loop
    #|  use ref.Ref
    #|  let run () : unit = while true do () done
    #|end
  expect_program_elaboration_kind(
    loop_source,
    b"program-loop.mlw",
    @why3_elab.Unsupported(Loop),
  )
}

///|
test "recursion mutation and exceptions have precise unsupported kinds" {
  let recursion =
    #|module Recursion
    #|  use int.Int
    #|  let rec countdown (value : int) : int
    #|    requires { value >= 0 }
    #|    ensures { result = 0 }
    #|    variant { value }
    #|  = if value = 0 then 0 else countdown (value - 1)
    #|end
  expect_program_elaboration_kind(
    recursion,
    b"program-recursion.mlw",
    @why3_elab.Unsupported(Recursion),
  )
  let mutation =
    #|module Mutation
    #|  use ref.Ref
    #|  let mutate () : int = let ref value = 0 in value := 1; value
    #|end
  expect_program_elaboration_kind(
    mutation,
    b"program-mutation.mlw",
    @why3_elab.Unsupported(Reference),
  )
  let exception_ =
    #|module Exception
    #|  exception Stop
    #|end
  expect_program_elaboration_kind(
    exception_,
    b"program-exception.mlw",
    @why3_elab.Unsupported(Exception),
  )
}
