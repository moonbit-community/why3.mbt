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
let shared_program_fixture_cache : Ref[
  (@identity.CompilationContext, @environment.Environment)?,
] = Ref(None)

///|
fn shared_program_fixture() -> (
  @identity.CompilationContext,
  @environment.Environment,
) raise {
  match shared_program_fixture_cache.val {
    Some(fixture) => fixture
    None => {
      let context = @identity.CompilationContext::new()
      let environment = @stdlib.embedded_environment_in_context(context)
      let fixture = (context, environment)
      shared_program_fixture_cache.val = Some(fixture)
      fixture
    }
  }
}

///|
fn shared_program_context() -> @identity.CompilationContext raise {
  shared_program_fixture().0
}

///|
fn fresh_program_environment(
  _context : @identity.CompilationContext,
) -> @environment.Environment raise {
  shared_program_fixture().1
}

///|
fn isolated_program_environment(
  context : @identity.CompilationContext,
) -> @environment.Environment raise {
  @stdlib.embedded_environment_in_context(context)
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
fn terminal_program_expression(expression : @mlw.Expr) -> @mlw.Expr {
  match expression.view() {
    Elet(_, body) => terminal_program_expression(body)
    _ => expression
  }
}

///|
fn outer_program_let_values(expression : @mlw.Expr) -> Array[@mlw.Expr] {
  match expression.view() {
    Elet(definition, body) => {
      let values = match definition.view() {
        LDvar(_, value) => [value]
        LDsym(_, _) | LDrec(_) => []
      }
      values.push_iter(outer_program_let_values(body).iter())
      values
    }
    _ => []
  }
}

///|
test "program Real operator keeps the source routine identity and ANF proxy" {
  let source =
    #|module ProgramReal
    #|  use real.Real
    #|  let plus_zero (x : real) : real
    #|    ensures { result = x }
    #|  = x + 0.0
    #|end
  let context = shared_program_context()
  let environment = fresh_program_environment(context)
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    environment,
    parsed_program_unit(source, b"program-real.mlw"),
  )
  let declarations = program_declarations(pmodule)
  guard declarations is [PDlet(_, Cfun(cty, Some(body)), _, _)] else {
    fail("expected one concrete program routine")
  }
  assert_eq(cty.view().arguments.length(), 1)
  assert_eq(cty.view().postconditions.length(), 1)
  guard body.view() is Elet(definition, call) &&
    definition.view() is LDvar(_, value) else {
    fail("real literal argument did not receive an ANF proxy")
  }
  assert_true(value.view() is Econst(_))
  guard call.view() is Eexec(computation, _) &&
    computation.view() is Capp(symbol, arguments) else {
    fail("real addition was not a routine call")
  }
  assert_eq(arguments.length(), 2)
  let real_add = environment
    .resolve_module(@theory.TheoryKey::new([b"real"], b"Real"), None)
    .export_namespace()
    .find_routine([b"infix +"], None)
  assert_true(symbol == real_add)
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
  let context = shared_program_context()
  let environment = fresh_program_environment(context)
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    environment,
    parsed_program_unit(source, b"program-shadow.mlw"),
  )
  guard program_declarations(pmodule) is [PDlet(_, Cfun(cty, Some(body)), _, _)] else {
    fail("expected one concrete shadowing routine")
  }
  let argument = cty.view().arguments[0]
  let post = cty.view().postconditions[0].view()
  let free = post.formula.free_variables()
  assert_true(free.any(variable => variable == post.result))
  assert_true(!free.any(variable => variable == argument.view().pure_symbol))
  assert_true(body.view() is Evar(variable) && variable == argument)
}

///|
fn expect_program_elaboration_kind(
  source : String,
  filename : BytesView,
  expected : @why3_elab.ElabErrorKind,
) -> Unit raise {
  let context = shared_program_context()
  let environment = fresh_program_environment(context)
  try
    @why3_elab.elaborate_program_unit(
      context,
      environment,
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
test "program routines generalize declared variables but reject result mismatches" {
  let polymorphic =
    #|module Polymorphic
    #|  let identity (value : 'a) : 'a = value
    #|  let integer () : int = identity 1
    #|  let boolean () : bool = identity true
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(polymorphic, b"program-polymorphic.mlw"),
  )
  guard program_declarations(pmodule)
    is [
      PDlet(identity, Cfun(identity_cty, Some(_)), _, _),
      PDlet(_, Cfun(_, Some(integer)), _, _),
      PDlet(_, Cfun(_, Some(boolean)), _, _),
    ] else {
    fail("polymorphic routine and its call sites did not elaborate")
  }
  assert_true(
    identity_cty.view().arguments[0].view().ity.view() is ItyVar(variable) &&
    identity_cty.view().result.view() is ItyVar(result_variable) &&
    variable == result_variable,
  )
  guard terminal_program_expression(integer).view()
    is Eexec(integer_call, integer_cty) &&
    integer_call.view() is Capp(integer_identity, [_]) &&
    terminal_program_expression(boolean).view()
    is Eexec(boolean_call, boolean_cty) &&
    boolean_call.view() is Capp(boolean_identity, [_]) else {
    fail("polymorphic calls did not retain routine applications")
  }
  assert_true(integer_identity == identity)
  assert_true(boolean_identity == identity)
  assert_true(
    integer_cty.view().result.view() is ItyApp(symbol, [], _) &&
    symbol.view().logic_type.name() == b"int",
  )
  assert_true(
    boolean_cty.view().result.view() is ItyApp(symbol, [], _) &&
    symbol.view().logic_type.name() == b"bool",
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
test "nested polymorphic pure applications share argument inference" {
  let source =
    #|module NestedInference
    #|  type symbol 'a = Symbol 'a
    #|  constant identity : 'a -> 'a
    #|  function eval (function_ : 'a -> 'b) (argument : 'a) : 'b
    #|  let consume (x : 'c) (term : symbol 'b) (rename : 'b -> 'c) : unit =
    #|    ()
    #|  let regression (x : 'c) (substitute : 'a -> symbol 'c)
    #|      (argument : 'a) : unit =
    #|    consume x (eval substitute argument) identity
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-nested-inference.mlw"),
  )
  let regression = pmodule
    .export_namespace()
    .find_routine([b"regression"], None)
  assert_eq(regression.view().cty.view().arguments.length(), 3)
}

///|
test "abstract polymorphic routines defensively spoil escaping variables" {
  let source =
    #|module DefensiveAbstract
    #|  val choose (value : 'a) : 'a
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"defensive-abstract.mlw"),
  )
  let choose = pmodule.export_namespace().find_routine([b"choose"], None)
  let result_variables = choose.view().cty.view().result.free_type_variables()
  let spoils = choose.view().cty.view().effect.view().spoils
  assert_true(
    result_variables is [result_variable] &&
    spoils is [spoiled] &&
    spoiled == result_variable,
  )
}

///|
test "checked writes preserve computed polymorphic spoils" {
  let source =
    #|module CheckedWriteSpoils
    #|  use ref.Ref
    #|  val overwrite (target : ref 'a) (value : 'a) : unit
    #|    writes { target }
    #|  let forward (target : ref 'a) (value : 'a) : unit
    #|    writes { target }
    #|  = overwrite target value
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"checked-write-spoils.mlw"),
  )
  let forward = pmodule.export_namespace().find_routine([b"forward"], None)
  assert_eq(forward.view().cty.view().effect.view().spoils.length(), 1)
}

///|
test "a call result alias preserves nested writes through an ANF proxy" {
  let source =
    #|module NestedAlias
    #|  use array.Array
    #|  type ptr 'a = abstract {
    #|    mutable data : array 'a;
    #|    offset : int;
    #|  }
    #|  type holder = { pointer : ptr int }
    #|  val shift (pointer : ptr 'a) : ptr 'a
    #|    alias { pointer.data with result.data }
    #|  val set (pointer : ptr 'a) (value : 'a) : unit
    #|    writes { pointer.data.elts }
    #|  val set_at (pointer : ptr 'a) (index : int) (value : 'a) : unit
    #|    writes { pointer.data.elts }
    #|  val combine (target left right : ptr 'a) : unit
    #|    alias { target.data with left.data }
    #|    alias { target.data with right.data }
    #|    alias { left.data with right.data }
    #|    writes { target.data.elts }
    #|  val allocate () : ptr 'a
    #|  val allocate_pair () : (left : ptr 'a, right : ptr 'a)
    #|    alias { left.data with right.data }
    #|  let set_shifted (pointer : ptr 'a) (value : 'a) : unit =
    #|    set (shift pointer) value
    #|  let combine_same (pointer : ptr 'a) : unit =
    #|    combine pointer pointer pointer
    #|  let initialize () : unit =
    #|    let pointer = allocate () in
    #|    set pointer 0
    #|  let initialize_loop (limit : int) : unit =
    #|    let pointer = allocate () in
    #|    for index = 0 to limit do
    #|      set_at pointer index 0
    #|    done
    #|  let create_holder (limit : int) : holder =
    #|    let pointer = allocate () in
    #|    for index = 0 to limit do
    #|      set_at pointer index 0
    #|    done;
    #|    { pointer = pointer }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-nested-alias.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("nested alias elaboration failed: \{diagnostic.message}")
    _ => fail("nested alias elaboration raised another error")
  }
  let routine = pmodule.export_namespace().find_routine([b"set_shifted"], None)
  let mut body_writes = -1
  let mut write_is_reachable = false
  for declaration in program_declarations(pmodule) {
    if declaration is PDlet(symbol, Cfun(_, Some(body)), _, _) &&
      symbol == routine {
      body_writes = body.effect().view().writes.length()
      if body.effect().view().writes is [write] {
        write_is_reachable = body.effect().view().reads.any(read => {
          read.view().ity
          .reachable_regions()
          .any(region => region == write.view().region)
        })
      }
    }
  }
  assert_eq(body_writes, 1)
  assert_true(write_is_reachable)
  assert_eq(routine.view().cty.view().effect.view().writes.length(), 1)
  ignore(pmodule.export_namespace().find_routine([b"initialize"], None))
  ignore(pmodule.export_namespace().find_routine([b"initialize_loop"], None))
  ignore(pmodule.export_namespace().find_routine([b"create_holder"], None))
  ignore(pmodule.export_namespace().find_routine([b"allocate_pair"], None))
}

///|
test "constructors accept values that contain mutable regions" {
  let source =
    #|module ConstructorEffects
    #|  use ref.Ref
    #|  type cell = { mutable value : int }
    #|  let nested (cell : cell) : unit =
    #|    let ref cursor = cell in
    #|    let pair = (ref cell, ref cell) in
    #|    cursor <- cell;
    #|    ()
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-constructor-effects.mlw"),
  )
  ignore(pmodule.export_namespace().find_routine([b"nested"], None))
}

///|
test "reference initializers use implicit reads to infer their content type" {
  let source =
    #|module ReferenceInference
    #|  use ref.Ref
    #|  use int.Int
    #|  use mach.int.Int32
    #|  use mach.int.UInt32
    #|  use mach.c.C
    #|  use mach.int.UInt64
    #|  type limb = uint64
    #|  type pointer = ptr limb
    #|  type counter = { count : uint32 }
    #|  type bounded_counter = { exp : uint32 }
    #|    invariant { 0 <= exp }
    #|    by { exp = 0 }
    #|  val combine (left right : uint64) : uint64
    #|  let loop (limit : int32) : unit =
    #|    let ref index = 0 in
    #|    while Int32.(<) index limit do
    #|      index <- index
    #|    done
    #|  let preserve_initializer (limit : int32) : unit =
    #|    let ref index = limit in
    #|    while index >= 1 do
    #|      index <- index
    #|    done
    #|  let pointer_loop (pointer : ptr int) (limit : int32) : unit =
    #|    let ref current = C.incr pointer 0 in
    #|    while Int32.(<) 0 limit do
    #|      current <- C.incr current 1
    #|    done
    #|  let pointer_read (pointer : ptr uint64) (limit : int32) : unit =
    #|    let ref value = 0 in
    #|    let ref index = 0 in
    #|    while Int32.(<) index limit do
    #|      value <- C.get_ofs pointer index;
    #|      index <- index
    #|    done
    #|  let condition_and_body (pointer : ptr uint64) : unit =
    #|    let ref value = 0 in
    #|    let ref cursor = C.incr pointer 0 in
    #|    while value = 0 do
    #|      value <- C.get cursor
    #|    done
    #|  let nested_pointer (pointer : pointer) : unit =
    #|    let ref value = 0 in
    #|    let ghost ref index = 0 in
    #|    let ref cursor = C.incr pointer 0 in
    #|    while value = 0 do
    #|      let combined = combine value 1 in
    #|      value <- C.get cursor
    #|    done
    #|  let explicit_update () : int =
    #|    let ref value = 0 in
    #|    value := 1;
    #|    value
    #|  let ghost_updates () : unit =
    #|    let ghost a = ref 1 in
    #|    let ghost c = ref 0 in
    #|    a := !c;
    #|    c := !a - !c;
    #|    ()
    #|  let make_counter () : counter =
    #|    let ref count = 1 in
    #|    count <- count + 1;
    #|    { count = count }
    #|  let make_bounded_counter () : bounded_counter =
    #|    let ref exp = 1 in
    #|    while false do
    #|      invariant { 0 <= exp }
    #|      exp <- exp + 1
    #|    done;
    #|    { exp = exp }
    #|  let return_uint64 () : uint64 =
    #|    let ref carry = 0 in
    #|    carry <- 1;
    #|    carry
    #|  let explicit_update_uint64 () : unit =
    #|    let carry = ref 0 in
    #|    let spare = ref 0 in
    #|    let high = ref 0 in
    #|    begin
    #|      ensures { !carry >= 0 /\ !spare >= 0 /\ !high >= 0 }
    #|      carry := return_uint64 ();
    #|      if true then high := 0 else high := !carry;
    #|      spare := !carry + !spare;
    #|      while false do
    #|        invariant { 0 <= !carry }
    #|        variant { 0 }
    #|      done
    #|    end
    #|  let explicit_return_uint64 () : uint64 =
    #|    let carry = ref 0 in
    #|    !carry
    #|  let inferred_machine_branch (limit : int32) : int32 =
    #|    let adjust = if true then 1 else 0 in
    #|    limit + adjust
    #|  let inferred_shadowed_machine_branch (flag : bool) : int32 =
    #|    let size = if flag then 1 else 0 in
    #|    let size = if flag then size else -size in
    #|    size
    #|  let inferred_return_machine_branch
    #|      (limit : int32) (flag : bool) : int32 =
    #|    let delta = if flag then 1 else 0 in
    #|    if flag then return limit - delta;
    #|    delta
    #|  let contracted_update () : unit =
    #|    let ref carry = 0 in
    #|    begin
    #|      ensures { true }
    #|      carry <- return_uint64 ()
    #|    end
    #|  let return_int32 () : int32 =
    #|    let ref index = 0 in
    #|    index
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-reference-inference.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      let location = match diagnostic.span {
        Some(span) => " at line \{span.view().start_line}"
        None => ""
      }
      fail(
        "reference content inference failed\{location}: \{diagnostic.message}",
      )
    }
    _ => fail("reference content inference raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"loop"], None))
  ignore(
    pmodule.export_namespace().find_routine([b"preserve_initializer"], None),
  )
  ignore(pmodule.export_namespace().find_routine([b"pointer_loop"], None))
  ignore(pmodule.export_namespace().find_routine([b"pointer_read"], None))
  ignore(pmodule.export_namespace().find_routine([b"condition_and_body"], None))
  ignore(pmodule.export_namespace().find_routine([b"nested_pointer"], None))
  ignore(pmodule.export_namespace().find_routine([b"explicit_update"], None))
  ignore(pmodule.export_namespace().find_routine([b"ghost_updates"], None))
  ignore(pmodule.export_namespace().find_routine([b"make_counter"], None))
  ignore(
    pmodule.export_namespace().find_routine([b"make_bounded_counter"], None),
  )
  ignore(pmodule.export_namespace().find_routine([b"return_uint64"], None))
  ignore(
    pmodule.export_namespace().find_routine([b"explicit_update_uint64"], None),
  )
  ignore(pmodule.export_namespace().find_routine([b"return_int32"], None))
}

///|
test "overloaded machine operators infer contextual integer literals from either operand" {
  let source =
    #|module MachineLiteralInference
    #|  use mach.int.UInt64
    #|  let divide (divisor : uint64) : uint64 =
    #|    0xffff_ffff_ffff_ffff / divisor
    #|  let compare (value : uint64) : bool =
    #|    2 <= value
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"machine-literal-inference.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("machine literal overload inference failed: \{diagnostic.message}")
    _ => fail("machine literal overload fixture raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"divide"], None))
  ignore(pmodule.export_namespace().find_routine([b"compare"], None))
}

///|
test "overloaded machine comparisons keep unconstrained local literals consistent" {
  let source =
    #|module MachineLocalLiteralInference
    #|  use mach.int.Int63
    #|  let compare () =
    #|    let left = 20 in
    #|    let right = 21 in
    #|    left < right
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"machine-local-literal-inference.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      let location = match diagnostic.span {
        Some(span) =>
          " at \{span.view().start_line}:\{span.view().start_column}"
        None => ""
      }
      fail(
        "machine local literal inference failed\{location}: \{diagnostic.message}",
      )
    }
    _ => fail("machine local literal inference raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"compare"], None))
}

///|
test "program relation chains share their typed middle operand" {
  let source =
    #|module ProgramRelationChain
    #|  use mach.int.Int63
    #|  let bounded (value : int63) : bool =
    #|    0 <= value < 10
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-relation-chain.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("program relation-chain typing failed: \{diagnostic.message}")
    _ => fail("program relation-chain fixture raised another error")
  }
  guard program_declarations(pmodule) is [PDlet(_, Cfun(_, Some(body)), _, _)] else {
    fail("expected one concrete relation-chain routine")
  }
  assert_true(terminal_program_expression(body).view() is Eif(_, _, _))
}

///|
test "pure program identifiers prefer local and global program variables" {
  let source =
    #|module PureProgramIdentifiers
    #|  use int.Int
    #|  type cell = { mutable value : int }
    #|  val global : cell
    #|  let capture (local : cell) : unit =
    #|    let ghost local_snapshot = { local } in
    #|    let ghost global_snapshot = { global } in
    #|    assert { local_snapshot.value = local.value };
    #|    assert { global_snapshot.value = global.value }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-pure-identifiers.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("pure program identifier lookup failed: \{diagnostic.message}")
    _ => fail("pure program identifier lookup raised another error")
  }
  let mut abstract_value : @mlw.Expr? = None
  for declaration in program_declarations(pmodule) {
    if declaration is PDvar(_, value, _, _) {
      abstract_value = Some(value)
    }
  }
  guard abstract_value is Some(value) else {
    fail("global program variable did not retain its abstract initializer")
  }
  assert_eq(value.origin().display_name(), b"")
  ignore(pmodule.export_namespace().find_routine([b"capture"], None))
}

///|
test "recursive routine inference sees top-level program variables" {
  let source =
    #|module RecursiveGlobal
    #|  use int.Int
    #|  use ref.Ref
    #|  val global : ref int
    #|  let rec countdown (steps : int) : unit
    #|    requires { !global >= 0 }
    #|    variant { steps }
    #|  = if steps <= 0 then () else countdown (steps - 1)
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-recursive-global.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("recursive global scope failed: \{diagnostic.message}")
    _ => fail("recursive global scope raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"countdown"], None))
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
test "postconditions infer an omitted result needed by early return" {
  let source =
    #|module ContractualEarlyReturn
    #|  use int.Int
    #|  let choose (value : int)
    #|    ensures { result >= -1 }
    #|  =
    #|    if value >= 0 then return value;
    #|    -1
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"contractual-early-return.mlw"),
  )
  let choose = pmodule.export_namespace().find_routine([b"choose"], None)
  guard choose.view().cty.view().result.view() is ItyApp(symbol, [], []) else {
    fail("postcondition did not infer a concrete early-return type")
  }
  assert_eq(symbol.view().logic_type.name(), b"int")
}

///|
test "return payloads infer an otherwise omitted routine result" {
  let source =
    #|module ReturnPayloadInference
    #|  let finish (early : bool) =
    #|    if early then return;
    #|    return ()
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"return-payload-inference.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("return payload inference failed: \{diagnostic.message}")
    @logic.TypeError(diagnostic) =>
      fail("return payload inference failed: \{diagnostic.message}")
    _ => fail("return payload inference raised another error")
  }
  let finish = pmodule.export_namespace().find_routine([b"finish"], None)
  guard finish.view().cty.view().result.view() is ItyApp(symbol, [], []) else {
    fail("return payload did not infer a concrete result")
  }
  assert_eq(symbol.view().logic_type.name(), b"tuple0")
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
    @why3_elab.TypeFailure(TypeMismatch),
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
  let context = shared_program_context()
  let environment = fresh_program_environment(context)
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    environment,
    parsed_program_unit(source, b"program-trusted-polymorphism.mlw"),
  )
  guard program_declarations(pmodule)
    is [
      PDlet(_, Cfun(_, Some(int_body)), _, _),
      PDlet(_, Cfun(_, Some(bool_body)), _, _),
    ] else {
    fail("expected two concrete equality routines")
  }
  guard int_body.view() is Eexec(int_computation, _) &&
    int_computation.view() is Cpur(int_equality, int_arguments) &&
    bool_body.view() is Eexec(bool_computation, _) &&
    bool_computation.view() is Cpur(bool_equality, bool_arguments) else {
    fail("trusted equality did not elaborate as pure applications")
  }
  let int_ity = int_body.ity()
  let bool_ity = bool_body.ity()
  assert_true(int_equality == bool_equality)
  assert_eq(int_arguments.length(), 2)
  assert_eq(bool_arguments.length(), 2)
  assert_true(int_arguments[0].view().ity != bool_arguments[0].view().ity)
  assert_true(int_ity == bool_ity)
}

///|
test "while and for loops retain contracts and termination effects" {
  let source =
    #|module Loop
    #|  use int.Int
    #|  let run () : unit =
    #|    while false do invariant { true } variant { 0 } () done;
    #|    for i = 0 to 2 do
    #|      invariant { 0 <= i }
    #|      check { i <= 2 }
    #|    done
    #|end
  let context = shared_program_context()
  let environment = fresh_program_environment(context)
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    environment,
    parsed_program_unit(source, b"program-loop.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("loop elaboration failed: \{diagnostic.message}")
    _ => fail("loop elaboration raised an unexpected error family")
  }
  guard program_declarations(pmodule) is [PDlet(_, Cfun(_, Some(body)), _, _)] &&
    body.view() is Elet(first, for_loop) &&
    first.view() is LDvar(_, while_loop) &&
    while_loop.view() is Ewhile(_, invariants, variants, _) else {
    fail("loop program did not preserve its while/for structure")
  }
  assert_eq(invariants.length(), 1)
  assert_eq(variants.length(), 1)
  assert_true(while_loop.effect().view().termination is Total)
  guard for_loop.view() is Elet(_, nested) &&
    nested.view() is Elet(_, final_loop) else {
    fail("for-loop bounds did not receive ordered ANF proxies")
  }
  assert_true(
    final_loop.view() is Efor(_, _, _, invariants, _) &&
    invariants.length() == 1,
  )
}

///|
test "recursive declarations retain contracts variants and internal calls" {
  let source =
    #|module Recursion
    #|  use int.Int
    #|  let rec countdown (value : int) : int
    #|    requires { value >= 0 }
    #|    ensures { result = 0 }
    #|    variant { value }
    #|  = if value = 0 then 0 else countdown (value - 1)
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-recursion.mlw"),
  )
  guard program_declarations(pmodule) is [PDrec([definition], _, _)] else {
    fail("recursive declaration did not remain grouped")
  }
  let recursive = definition.view()
  assert_eq(recursive.symbol.view().name, b"countdown")
  assert_eq(recursive.internal_symbol.view().name, b"countdown")
  assert_true(recursive.symbol != recursive.internal_symbol)
  assert_eq(recursive.variants.length(), 1)
  assert_eq(recursive.symbol.view().cty.view().preconditions.length(), 1)
  guard recursive.function_.view() is Cfun(body) &&
    body.view() is Eif(_, _, recursive_branch) &&
    terminal_program_expression(recursive_branch).view() is Eexec(call, _) &&
    call.view() is Capp(called, [_]) else {
    fail("recursive body did not retain its internal call")
  }
  assert_true(called == recursive.internal_symbol)
}

///|
test "exceptions ghost pure check and absurd elaborate into full Expr nodes" {
  let source =
    #|module Control
    #|  use int.Int
    #|  exception Stop int
    #|  let stop (x : int) : int =
    #|    if x = 0 then raise Stop x else x
    #|  let bound (x : int) : int =
    #|    match x with y -> y end
    #|  let caught (x : int) : int =
    #|    try raise Stop x with Stop y -> y end
    #|  let local () : int = exception Hidden int in 0
    #|  let checked (x : int) : unit = check { x = x }
    #|  let pure_formula (x : int) : bool = pure { x = x }
    #|  let ghost_checked (x : int) : unit = ghost (check { x = x })
    #|  let local_ghost () : int = let ghost y = 0 in y
    #|  let ghost top_ghost (ghost x : int) : unit = check { x = x }
    #|  let impossible () : int = absurd
    #|end
  let context = shared_program_context()
  let environment = fresh_program_environment(context)
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    environment,
    parsed_program_unit(source, b"program-control.mlw"),
  )
  let declarations = program_declarations(pmodule)
  assert_eq(declarations.length(), 11)
  assert_true(declarations[0] is PDexn(_, _, _))
  guard declarations[1] is PDlet(_, Cfun(_, Some(stop)), _, _) &&
    stop.view() is Eif(_, raised, _) else {
    fail("global exception raise did not elaborate")
  }
  assert_true(raised.view() is Eraise(_, _))
  guard declarations[2] is PDlet(_, Cfun(_, Some(bound)), _, _) else {
    fail("regular match did not elaborate")
  }
  assert_true(bound.view() is Ematch(_, branches, _) && branches.length() == 1)
  guard declarations[3] is PDlet(_, Cfun(_, Some(caught)), _, _) else {
    fail("exception match did not elaborate")
  }
  assert_true(caught.view() is Ematch(_, _, branches) && branches.length() == 1)
  guard declarations[4] is PDlet(_, Cfun(_, Some(local_body)), _, _) else {
    fail("local exception declaration did not elaborate")
  }
  assert_true(local_body.view() is Eexn(_, _))
  guard declarations[5] is PDlet(_, Cfun(_, Some(checked)), _, _) else {
    fail("check assertion routine did not elaborate")
  }
  assert_true(checked.view() is Eassert(@mlw.Check, _))
  guard declarations[6] is PDlet(_, Cfun(_, Some(pure)), _, _) else {
    fail("pure expression routine did not elaborate")
  }
  assert_true(pure.view() is Epure(_))
  guard declarations[7] is PDlet(_, Cfun(_, Some(ghost)), _, _) else {
    fail("ghost expression routine did not elaborate")
  }
  assert_true(ghost.view() is Eghost(_))
  guard declarations[8] is PDlet(_, Cfun(_, Some(local_ghost)), _, _) else {
    fail("ghost local binding did not elaborate")
  }
  assert_true(
    local_ghost.view() is Elet(definition, _) &&
    definition.view() is LDvar(variable, value) &&
    variable.view().ghost &&
    value.view() is Econst(_) &&
    !value.effect().view().ghost,
  )
  guard declarations[9] is PDlet(top_ghost, Cfun(cty, Some(_)), _, _) else {
    fail("ghost routine did not elaborate")
  }
  assert_true(top_ghost.is_ghost())
  assert_true(cty.view().arguments[0].view().ghost)
  guard declarations[10] is PDlet(_, Cfun(_, Some(absurd)), _, _) else {
    fail("absurd routine did not elaborate")
  }
  assert_true(absurd.view() is Eabsurd)
}

///|
test "match result inference can start after a bottom branch" {
  let source =
    #|module BottomMatch
    #|  type optional = Missing | Present int
    #|  let extract (value : optional) =
    #|    match value with
    #|    | Missing -> absurd
    #|    | Present result -> result
    #|    end
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-bottom-match.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("bottom-first match inference failed: \{diagnostic.message}")
    _ => fail("bottom-first match inference raised another error")
  }
  let routine = pmodule.export_namespace().find_routine([b"extract"], None)
  assert_true(
    routine.view().cty.view().result.view() is ItyApp(symbol, [], _) &&
    symbol.view().logic_type.name() == b"int",
  )
}

///|
test "non-exhaustive program matches gain an implicit absurd branch" {
  let source =
    #|module PartialMatch
    #|  type optional = Missing | Present int
    #|  let destruct (value : optional)
    #|    requires { value <> Missing }
    #|  =
    #|    match value with
    #|    | Present result -> result
    #|    end
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-partial-match.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("partial program match failed: \{diagnostic.message}")
    _ => fail("partial program match raised another error")
  }
  guard program_declarations(pmodule)
    is [PDtype([_], [_], []), PDlet(_, Cfun(_, Some(body)), _, _)] &&
    body.view() is Ematch(_, [selected, fallback], []) else {
    fail("partial match did not retain its implicit fallback")
  }
  assert_true(selected.view().pattern.view().pattern.view() is Papp(_, [_], _))
  assert_true(fallback.view().pattern.view().pattern.view() is Pwild(_))
  assert_true(fallback.view().body.view() is Eabsurd)
}

///|
test "match result inference prefers a concretely typed later branch" {
  let source =
    #|module ConcreteMatchBranch
    #|  use int.Int
    #|  use option.Option
    #|  let discard_key (source : option (int, int)) : option int =
    #|    match source with
    #|    | None -> None
    #|    | Some (_, value) -> Some value
    #|    end
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"concrete-match-branch.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("concrete match branch inference failed: \{diagnostic.message}")
    _ => fail("concrete match branch fixture raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"discard_key"], None))
}

///|
test "try result inference can start from a no-payload handler" {
  let source =
    #|module BottomTry
    #|  use option.Option
    #|  use array.Array
    #|  exception Done
    #|  exception NoSolution
    #|  val produce () : int
    #|  val search (values : array int) : unit
    #|  let recover (value : int) =
    #|    try
    #|      ();
    #|      raise Done
    #|    with Done -> value
    #|    end
    #|  let optional () =
    #|    try Some (produce ())
    #|    with Done -> None
    #|    end
    #|  let recover_array (values : array int)
    #|    ensures { result = values }
    #|  =
    #|    try search values; raise NoSolution
    #|    with Done -> values
    #|    end
    #|  let check_then_recover (values : array int)
    #|    ensures { result = values }
    #|  =
    #|    if true then recover_array values else raise NoSolution
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-bottom-try.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("bottom try inference failed: \{diagnostic.message}")
    _ => fail("bottom try inference raised another error")
  }
  let routine = pmodule.export_namespace().find_routine([b"recover"], None)
  assert_true(
    routine.view().cty.view().result.view() is ItyApp(symbol, [], _) &&
    symbol.view().logic_type.name() == b"int",
  )
  let optional = pmodule.export_namespace().find_routine([b"optional"], None)
  assert_true(
    optional.view().cty.view().result.view() is ItyApp(symbol, [element], _) &&
    symbol.view().logic_type.name() == b"option" &&
    element.view() is ItyApp(element_symbol, [], _) &&
    element_symbol.view().logic_type.name() == b"int",
  )
  ignore(pmodule.export_namespace().find_routine([b"recover_array"], None))
  ignore(pmodule.export_namespace().find_routine([b"check_then_recover"], None))
}

///|
test "modules retain pure logic inductive meta and nested scope declarations" {
  let source =
    #|module ModulePure
    #|  function identity (value : int) : int = value
    #|  inductive reachable (value : bool) =
    #|    | reachable_true : reachable True
    #|  lemma identity_reflexive : forall value : int. identity value = value
    #|  meta "remove_unused:keep" function identity
    #|  scope Nested
    #|    predicate valid (value : int) = identity value = value
    #|  end
    #|  let run (value : int) : int = identity value
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"module-pure.mlw"),
  )
  let declarations = program_declarations(pmodule)
  assert_eq(declarations.length(), 5)
  assert_true(declarations[0] is PDpure([_], []))
  assert_true(
    declarations[1] is PDpure([inductive], []) &&
    inductive.view() is Dind(Ind, [_]),
  )
  guard declarations[2] is PDlet(lemma_routine, Cany(_), [], []) else {
    fail("non-goal proposition did not create its ghost lemma routine")
  }
  assert_true(lemma_routine.is_ghost())
  assert_eq(lemma_routine.view().name, b"identity_reflexive'lemma")
  assert_true(
    declarations[3] is PDpure([lemma], []) &&
    lemma.view() is Dprop(Plemma, _, _),
  )
  guard declarations[4] is PDlet(_, Cfun(_, Some(body)), _, _) &&
    body.view() is Eexec(computation, _) &&
    computation.view() is Cpur(identity, [_]) else {
    fail("program body did not resolve the module-local pure function")
  }
  assert_eq(identity.view().name, b"identity")
  assert_true(
    pmodule.view().items.any(item => {
      item is Umeta(meta) && meta.view().name == b"remove_unused:keep"
    }),
  )
  assert_true(
    pmodule.view().items.any(item => {
      item is Uscope(name, [Udecl(PDpure([nested], []))]) &&
      name == b"Nested" &&
      nested.view() is Dlogic([_])
    }),
  )
  assert_eq(
    pmodule
    .pure_theory()
    .export_namespace()
    .find_logic([b"Nested", b"valid"], None)
    .view().name,
    b"valid",
  )
}

///|
test "program-value meta arguments retain routine identifiers" {
  let source =
    #|module ProgramValueMeta
    #|  let decision (value : int) : int = value
    #|  meta reflection val decision
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-value-meta.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("program-value meta typing failed: \{diagnostic.message}")
    _ => fail("program-value meta fixture raised another error")
  }
  guard pmodule.view().items.any(item => {
    item is Umeta(meta) &&
    meta.view().name == b"reflection" &&
    meta.view().arguments is [MetaIdentifier(name)] &&
    name.view().name == b"decision"
  }) else {
    fail("program-value meta did not retain its routine identifier")
  }
}

///|
test "reference initialization specializes an empty constructor from assignment" {
  let source =
    #|module ReferenceInference
    #|  use list.List
    #|  use ref.Ref
    #|  let singleton (item : int) : list int =
    #|    let values = ref Nil in
    #|    let selected, _ = (item, item) in
    #|    values := Cons selected !values;
    #|    !values
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"reference-inference.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("reference content type was not inferred from assignment")
    }
    _ => fail("reference inference raised another error")
  }
  guard program_declarations(pmodule) is [PDlet(_, Cfun(cty, Some(_)), _, _)] else {
    fail("reference inference fixture lost its routine")
  }
  assert_true(
    cty.view().result.view() is ItyApp(symbol, [argument], _) &&
    symbol.view().logic_type.name() == b"list" &&
    argument.view() is ItyApp(element, [], _) &&
    element.view().logic_type.name() == b"int",
  )
}

///|
test "simple source types populate both pure and program module namespaces" {
  let source =
    #|module ProgramTypes
    #|  type token
    #|  type byte = < range 0 255 >
    #|  type binary32 = < float 8 24 >
    #|  type choice = First int | Second bool
    #|  type pair = { first : int; second : bool }
    #|  type pair_alias = pair
    #|  let wrap (value : int) : choice = First value
    #|  let project (value : pair) : int = first value
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-types.mlw"),
  )
  let declarations = program_declarations(pmodule)
  assert_eq(declarations.length(), 8)
  guard declarations[0] is PDtype([_], [_], []) &&
    declarations[1] is PDtype([_], [_, _, _, _], range_metas) &&
    declarations[2] is PDtype([_], [_, _, _, _, _], float_metas) else {
    fail("source numeric types lost their derived logical declarations")
  }
  assert_true(
    range_metas is [range_meta, range_projection_meta] &&
    range_meta.view().name == b"range_type" &&
    range_projection_meta.view().name == b"model_projection",
  )
  assert_true(
    float_metas is [float_meta, float_projection_meta] &&
    float_meta.view().name == b"float_type" &&
    float_projection_meta.view().name == b"model_projection",
  )
  for index = 3; index < 6; index = index + 1 {
    assert_true(declarations[index] is PDtype([_], [_], []))
  }
  let program_exports = pmodule.export_namespace()
  let choice = program_exports.find_type([b"choice"], None)
  let pair = program_exports.find_type([b"pair"], None)
  let pair_alias = program_exports.find_type([b"pair_alias"], None)
  assert_true(choice.view().definition is ProgramNoDef)
  assert_true(pair.view().definition is ProgramNoDef)
  assert_true(pair_alias.view().definition is ProgramAlias(_))
  assert_true(
    program_exports.find_type([b"byte"], None).view().definition
    is ProgramRange(lower, upper) &&
    lower == BigInt::from_int(0) &&
    upper == BigInt::from_int(255),
  )
  assert_true(
    program_exports.find_type([b"binary32"], None).view().definition
    is ProgramFloat(8, 24),
  )
  let first_constructor = program_exports.find_routine([b"First"], None)
  let first_projection = program_exports.find_routine([b"first"], None)
  assert_true(
    first_constructor.view().logic is RLls(symbol) &&
    symbol.view().role is Constructor(2),
  )
  assert_true(
    first_projection.view().logic is RLls(symbol) &&
    symbol.view().role is Projection,
  )
  guard declarations[6] is PDlet(_, Cfun(_, Some(wrap)), _, _) &&
    wrap.view() is Eexec(wrap_computation, _) &&
    wrap_computation.view() is Capp(constructor_routine, [_]) else {
    fail("variant constructor was not callable as a program routine")
  }
  assert_true(constructor_routine == first_constructor)
  guard declarations[7] is PDlet(_, Cfun(_, Some(project)), _, _) &&
    project.view() is Eexec(project_computation, _) &&
    project_computation.view() is Capp(projection, [_]) else {
    fail("record projection was not callable as a program routine")
  }
  assert_true(projection == first_projection)
  let pure_exports = pmodule.pure_theory().export_namespace()
  assert_true(
    pure_exports.find_type([b"choice"], None) == choice.view().logic_type,
  )
  assert_true(pure_exports.find_type([b"pair"], None) == pair.view().logic_type)
}

///|
test "mutable and ghost source fields drive program type flags and regions" {
  let source =
    #|module StatefulTypes
    #|  type cell = { mutable contents : int; ghost stamp : int }
    #|  type token = Token (ghost int) int
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"stateful-types.mlw"),
  )
  guard program_declarations(pmodule)
    is [
      PDtype([cell_declaration], [_], []),
      PDtype([token_declaration], [_], []),
    ] else {
    fail("stateful type declarations did not retain their program payload")
  }
  let cell_view = cell_declaration.view()
  let cell_symbol = cell_view.symbol
  let flags = cell_symbol.view().flags
  assert_true(flags.mutable_)
  assert_eq(cell_symbol.view().mutable_fields.length(), 1)
  assert_eq(cell_symbol.view().immutable_fields.length(), 1)
  assert_eq(
    cell_symbol.view().mutable_fields[0].view().name.view().name,
    b"contents",
  )
  assert_true(cell_symbol.view().immutable_fields[0].view().ghost)
  assert_eq(cell_view.fields.length(), 2)
  assert_eq(cell_view.constructors.length(), 1)
  guard cell_view.fields.any(projection => {
    projection.view().name == b"stamp" &&
    projection.view().cty.view().effect.view().ghost &&
    projection.view().cty.view().mask is @mlw.Ghost
  }) else {
    fail("ghost field projection did not retain its ghost computation type")
  }
  let constructor_cty = cell_view.constructors[0].view().cty
  assert_true(constructor_cty.view().result.view() is ItyReg(_))
  assert_eq(constructor_cty.view().effect.view().resets.length(), 1)
  let token_view = token_declaration.view()
  assert_false(token_view.symbol.view().flags.mutable_)
  assert_eq(token_view.symbol.view().immutable_fields.length(), 2)
  assert_true(token_view.symbol.view().immutable_fields[0].view().ghost)
  assert_false(token_view.symbol.view().immutable_fields[1].view().ghost)
  assert_eq(token_view.constructors.length(), 1)
}

///|
test "private mutable record projections receive distinct fresh regions" {
  let source =
    #|module PrivateProjectionRegions
    #|  use int.Int
    #|  type buffer = private {
    #|    mutable ghost contents : int;
    #|    length : int;
    #|  } invariant { 0 <= length }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"private-projection-regions.mlw"),
  )
  let mut selected : @mlw.ProgramTypeDeclaration? = None
  for program_declaration in program_declarations(pmodule) {
    if program_declaration is PDtype([declaration], _, _) {
      selected = Some(declaration)
    }
  }
  guard selected is Some(declaration) else {
    fail("private mutable record did not retain its program declaration")
  }
  guard declaration.view().fields is [first, second] &&
    first.view().cty.view().arguments is [first_target] &&
    second.view().cty.view().arguments is [second_target] &&
    first_target.view().ity.view() is ItyReg(first_region) &&
    second_target.view().ity.view() is ItyReg(second_region) else {
    fail("private record projections did not receive regional targets")
  }
  assert_true(first_region != second_region)
}

///|
test "program records construct update pattern-match and assign by semantic field identity" {
  let source =
    #|module ProgramRecords
    #|  type pair = { first : int; second : bool }
    #|  type cell = { mutable contents : int; tag : bool }
    #|  let make () : pair = { second = true; first = 1 }
    #|  let update (value : pair) : pair = { value with second = false }
    #|  let pick (value : pair) : int =
    #|    match value with { first = selected } -> selected end
    #|  let create_cell () : cell = { contents = 0; tag = true }
    #|  let allocate () : unit =
    #|    let temporary = { contents = 0; tag = true } in ()
    #|  let set (value : cell) : unit = value.contents <- 1
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-records.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      let line = match diagnostic.span {
        Some(span) => span.view().start_line
        None => Int64::from_int(-1)
      }
      fail("record elaboration failed at line \{line}: \{diagnostic.message}")
    }
    _ => fail("record elaboration raised an unexpected error family")
  }
  guard program_declarations(pmodule)
    is [
      PDtype([pair_type], [_], []),
      PDtype([cell_type], [_], []),
      PDlet(_, Cfun(_, Some(make)), _, _),
      PDlet(_, Cfun(_, Some(update)), _, _),
      PDlet(_, Cfun(_, Some(pick)), _, _),
      PDlet(_, Cfun(_, Some(create_cell)), _, _),
      PDlet(_, Cfun(_, Some(allocate)), _, _),
      PDlet(_, Cfun(_, Some(set)), _, _),
    ] else {
    fail("record source forms did not elaborate into the expected declarations")
  }
  let pair_constructor = pair_type.view().constructors[0]
  let pair_fields = pair_type.view().fields
  guard terminal_program_expression(make).view() is Eexec(make_call, _) &&
    make_call.view() is Capp(make_symbol, make_arguments) else {
    fail("record construction did not call its generated constructor")
  }
  assert_true(make_symbol == pair_constructor)
  assert_eq(make_arguments.length(), 2)
  guard terminal_program_expression(update).view() is Eexec(update_call, _) &&
    update_call.view() is Capp(update_symbol, update_arguments) else {
    fail("record update did not rebuild through its generated constructor")
  }
  assert_true(update_symbol == pair_constructor)
  assert_eq(update_arguments.length(), 2)
  assert_true(
    outer_program_let_values(update).any(projected => {
      projected.view() is Eexec(projection_call, _) &&
      projection_call.view() is Capp(projection_symbol, [_]) &&
      projection_symbol == pair_fields[0]
    }),
  )
  guard pick.view() is Ematch(_, [branch], []) &&
    branch.view().pattern.view().pattern.view()
    is Papp(pattern_constructor, pattern_arguments, _) else {
    fail("record pattern did not lower to the generated constructor")
  }
  guard pair_constructor.view().logic is RLls(pair_constructor_logic) else {
    fail("record constructor lost its logical identity")
  }
  assert_true(pattern_constructor == pair_constructor_logic)
  assert_eq(pattern_arguments.length(), 2)
  assert_true(pattern_arguments[1].view() is Pwild(_))
  assert_true(create_cell.ity().view() is ItyReg(_))
  let cell_constructor = cell_type.view().constructors[0]
  guard terminal_program_expression(create_cell).view()
    is Eexec(inferred_call, _) &&
    inferred_call.view() is Capp(inferred_symbol, _) else {
    fail("inferred mutable record construction did not become a call")
  }
  assert_true(inferred_symbol == cell_constructor)
  guard allocate.view() is Elet(allocation_binding, _) &&
    allocation_binding.view() is LDvar(_, allocation) &&
    terminal_program_expression(allocation).view() is Eexec(allocation_call, _) &&
    allocation_call.view() is Capp(allocation_symbol, _) else {
    fail("context-free mutable record construction did not allocate a call")
  }
  assert_true(allocation_symbol == cell_constructor)
  assert_true(allocation.ity().view() is ItyReg(_))
  guard terminal_program_expression(set).view() is Eassign([assignment]) else {
    fail("mutable record field assignment did not become an assignment node")
  }
  assert_true(assignment.view().field == cell_type.view().fields[0])
  assert_eq(set.effect().view().writes.length(), 1)
}

///|
test "ghost-backed container assignments proxy model fields as ghost" {
  let source =
    #|module GhostBackedContainerAssignment
    #|  use mach.int.Int63
    #|  use mach.array.ArrayInt63
    #|  type holder = { data : array63 }
    #|  let write (value : holder) : unit
    #|  = value.data[0] <- 2
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"ghost-backed-container-assignment.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("ghost-backed container assignment failed: \{diagnostic.message}")
    _ => fail("ghost-backed container assignment raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"write"], None))
}

///|
test "failed ghost inference restores the surrounding visible context" {
  let source =
    #|module GhostInferenceContextRestoration
    #|  use int.Int
    #|  use mach.int.Int63
    #|  use mach.array.ArrayInt63
    #|  type holder = { data : array63 }
    #|  val consume (ghost value : int) : unit
    #|  let write (target : holder) : unit =
    #|    let witness = ghost absurd in
    #|    consume witness;
    #|    target.data[0] <- 2
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"ghost-inference-context-restoration.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("ghost inference context restoration failed: \{diagnostic.message}")
    _ => fail("ghost inference context restoration raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"write"], None))
}

///|
test "conditional mutable record literals share their contextual result region" {
  let source =
    #|module ContextualMutableRecordBranches
    #|  type cell = { mutable contents : int }
    #|  let choose (flag : bool) : cell =
    #|    if flag then { contents = 0 } else { contents = 1 }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"contextual-mutable-record-branches.mlw"),
  )
  guard program_declarations(pmodule)
    is [PDtype(_, _, _), PDlet(_, Cfun(_, Some(body)), _, _)] &&
    terminal_program_expression(body).view() is Eif(_, consequent, alternative) else {
    fail(
      "contextual mutable record branches did not elaborate as a conditional",
    )
  }
  assert_true(consequent.ity() == alternative.ity())
}

///|
test "program record forms preserve field and mutability diagnostics" {
  let missing =
    #|module MissingRecordField
    #|  type pair = { first : int; second : bool }
    #|  let bad () : pair = { first = 0 }
    #|end
  expect_program_elaboration_kind(
    missing,
    b"program-record-missing.mlw",
    @why3_elab.TypeFailure(RecordFieldMissing),
  )
  let duplicate =
    #|module DuplicateRecordField
    #|  type pair = { first : int; second : bool }
    #|  let bad () : pair = { first = 0; first = 1; second = true }
    #|end
  expect_program_elaboration_kind(
    duplicate,
    b"program-record-duplicate.mlw",
    @why3_elab.TypeFailure(DuplicateRecordField),
  )
  let foreign =
    #|module ForeignRecordField
    #|  type pair = { first : int; second : bool }
    #|  type foreign = { other : bool }
    #|  let bad () : pair = { first = 0; other = true }
    #|end
  expect_program_elaboration_kind(
    foreign,
    b"program-record-foreign.mlw",
    @why3_elab.TypeFailure(BadRecordField),
  )
  let immutable =
    #|module ImmutableRecordField
    #|  type pair = { first : int; second : bool }
    #|  let bad (value : pair) : unit = value.first <- 1
    #|end
  expect_program_elaboration_kind(
    immutable,
    b"program-record-immutable.mlw",
    @why3_elab.ProgramFailure(AssignSnapshot),
  )
}

///|
test "program type purification and string literals retain pure source types" {
  let source =
    #|module ProgramPureTypes
    #|  type cell = { mutable contents : int }
    #|  let snapshot (value : {cell}) : {cell} = value
    #|  let text () : string = "why3"
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-pure-types.mlw"),
  )
  guard program_declarations(pmodule)
    is [
      PDtype([_], [_], []),
      PDlet(_, Cfun(snapshot_cty, Some(snapshot)), _, _),
      PDlet(_, Cfun(_, Some(text)), _, _),
    ] else {
    fail("purified program types did not elaborate")
  }
  assert_true(
    snapshot_cty.view().arguments[0].view().ity.view() is ItyApp(_, _, _),
  )
  assert_true(snapshot_cty.view().arguments[0].view().ity.is_pure())
  assert_true(snapshot_cty.view().result.view() is ItyApp(_, _, _))
  assert_true(snapshot.view() is Evar(_))
  assert_true(text.view() is Econst(ConstStr(b"why3")))
}

///|
test "program contracts retain writes exceptional posts partiality and divergence" {
  let source =
    #|module ProgramEffects
    #|  use int.Int
    #|  type cell = { mutable contents : int }
    #|  exception Stop int
    #|  val write (value : cell) : unit writes { value.contents }
    #|  val partial may_fail (value : int) : int
    #|    raises { Stop result -> result >= 0 }
    #|  val diverging (value : int) : int diverges
    #|  let set (value : cell) : unit
    #|    writes { value.contents }
    #|  = value.contents <- 1
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-effects.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      let line = match diagnostic.span {
        Some(span) => span.view().start_line
        None => Int64::from_int(-1)
      }
      fail(
        "effect contract elaboration failed at line \{line}: \{diagnostic.message}",
      )
    }
    _ => fail("effect contract raised an unexpected error family")
  }
  guard program_declarations(pmodule)
    is [
      PDtype([cell], [_], []),
      PDexn(stop, _, _),
      PDlet(_, Cany(write), _, _),
      PDlet(_, Cany(may_fail), _, _),
      PDlet(_, Cany(diverging), _, _),
      PDlet(_, Cfun(set, Some(_)), _, _),
    ] else {
    fail("effectful contracts did not elaborate")
  }
  let write_effect = write.view().effect.view()
  assert_eq(write_effect.writes.length(), 1)
  assert_true(
    write_effect.writes[0].view().fields[0] ==
    cell.view().symbol.view().mutable_fields[0],
  )
  assert_eq(may_fail.view().exceptional_postconditions.length(), 1)
  assert_true(
    may_fail.view().exceptional_postconditions[0].view().exception == stop,
  )
  assert_eq(
    may_fail.view().exceptional_postconditions[0].view().postconditions.length(),
    1,
  )
  assert_true(
    may_fail.view().effect.view().raises is [raised] && raised == stop,
  )
  assert_true(may_fail.view().effect.view().termination is Partial)
  assert_true(diverging.view().effect.view().termination is Diverges)
  assert_eq(set.view().effect.view().writes.length(), 1)
}

///|
test "effect clauses resolve qualified global program variables" {
  let source =
    #|module GlobalEffectState
    #|  type state = private mutable { }
    #|  val s : state
    #|end
    #|
    #|module GlobalEffectUse
    #|  use GlobalEffectState as GlobalEffectState
    #|  val touch () : unit writes { GlobalEffectState.s }
    #|end
  let context = @identity.CompilationContext::new()
  let elaborated = @why3_elab.elaborate_file(
    context,
    isolated_program_environment(context),
    @parser.parse_mlw_file(
      @utf8.encode(source)[:],
      filename=b"qualified-global-effect.mlw",
    ),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("qualified global effect failed: \{diagnostic.message}")
    _ => fail("qualified global effect raised another error")
  }
  guard elaborated.units()
    is [@why3_elab.ElaboratedModule(_), @why3_elab.ElaboratedModule(target)] else {
    fail("qualified global effect fixture did not elaborate two modules")
  }
  let touch = target.export_namespace().find_routine([b"touch"], None)
  assert_eq(touch.view().cty.view().effect.view().writes.length(), 1)
}

///|
test "old terms in program postconditions bind retained pre-state snapshots" {
  let source =
    #|module ProgramOld
    #|  type cell = { mutable contents : int }
    #|  let remember (value : cell) : unit
    #|    ensures { old value.contents = value.contents }
    #|    writes { value.contents }
    #|  = value.contents <- value.contents
    #|  let stable (value : int) : int
    #|    ensures { result = old value }
    #|  = value
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-old.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      let line = match diagnostic.span {
        Some(span) => span.view().start_line
        None => Int64::from_int(-1)
      }
      fail(
        "old contract elaboration failed at line \{line}: \{diagnostic.message}",
      )
    }
    _ => fail("old contract raised an unexpected error family")
  }
  guard program_declarations(pmodule)
    is [
      PDtype([_], [_], []),
      PDlet(_, Cfun(remember, Some(_)), _, _),
      PDlet(_, Cfun(stable, Some(_)), _, _),
    ] else {
    fail("old postconditions did not elaborate")
  }
  assert_eq(remember.view().oldies.length(), 1)
  let oldie = remember.view().oldies[0].view()
  assert_true(oldie.snapshot.view().ghost)
  assert_true(oldie.snapshot.view().ity.is_pure())
  assert_true(oldie.snapshot.view().name.view().attributes.is_empty())
  assert_false(oldie.original.view().ity.is_pure())
  let free = remember.view().postconditions[0].view().formula.free_variables()
  assert_true(
    free.any(variable => variable == oldie.snapshot.view().pure_symbol),
  )
  assert_true(
    free.any(variable => variable == oldie.original.view().pure_symbol),
  )
  guard remember.view().postconditions[0].view().formula.view()
    is Tapp(_, _, [old_contents, _]) &&
    old_contents.view() is Tapp(_, _, [snapshot_term]) &&
    snapshot_term.view() is Tvar(snapshot) else {
    fail("old postcondition did not retain its expected projection shape")
  }
  assert_true(snapshot == oldie.snapshot.view().pure_symbol)
  assert_true(
    snapshot_term.attributes().any(attribute => attribute == b"at:'Old"),
  )
  assert_true(stable.view().oldies.is_empty())
}

///|
test "expression labels materialize only the state snapshots used by at terms" {
  let source =
    #|module ProgramLabel
    #|  type cell = { mutable contents : int }
    #|  let observe (value : cell) : unit =
    #|    label L in
    #|    value.contents <- 1;
    #|    check { value.contents = (value.contents at L) }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-label.mlw"),
  )
  guard program_declarations(pmodule)
    is [PDtype([_], [_], []), PDlet(_, Cfun(cty, Some(body)), _, _)] else {
    fail("labeled program expression did not elaborate")
  }
  guard body.view() is Elet(snapshot_definition, labeled_body) &&
    snapshot_definition.view() is LDvar(snapshot, snapshot_value) else {
    fail("used at-state did not create a local snapshot binding")
  }
  assert_true(snapshot.view().ghost)
  assert_true(snapshot.view().ity.is_pure())
  guard snapshot_value.view() is Epure(snapshot_term) &&
    snapshot_term.view() is Tvar(original) else {
    fail("label snapshot was not initialized from the original variable")
  }
  assert_true(original == cty.view().arguments[0].view().pure_symbol)
  assert_true(labeled_body.effect().view().reads.any(read => read == snapshot))
  assert_false(body.effect().view().reads.any(read => read == snapshot))
}

///|
test "destructuring postconditions lower exhaustive result patterns to a case" {
  let source =
    #|module ProgramPostPattern
    #|  type pair = { first : int; second : bool }
    #|  let make () : pair
    #|    returns { | { first = selected } -> selected = 1 }
    #|  = { first = 1; second = true }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-post-pattern.mlw"),
  )
  guard program_declarations(pmodule)
    is [PDtype([_], [_], []), PDlet(_, Cfun(cty, Some(_)), _, _)] else {
    fail("destructuring postcondition did not elaborate")
  }
  guard cty.view().postconditions is [postcondition] &&
    postcondition.view().formula.view() is Tcase(_, [branch]) &&
    branch.view().pattern.view() is Papp(_, arguments, _) else {
    fail("destructuring result pattern did not become a case formula")
  }
  assert_eq(arguments.length(), 2)
  assert_true(arguments[1].view() is Pwild(_))
}

///|
test "program tuples elaborate through the on-demand tuple module" {
  let source =
    #|module ProgramTuples
    #|  let swap (value : (int, bool)) : (bool, int) =
    #|    match value with
    #|    | (first, second) -> (second, first)
    #|    end
    #|end
  let context = shared_program_context()
  let environment = fresh_program_environment(context)
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    environment,
    parsed_program_unit(source, b"program-tuples.mlw"),
  )
  guard program_declarations(pmodule) is [PDlet(_, Cfun(cty, Some(body)), _, _)] else {
    fail("tuple routine did not elaborate")
  }
  assert_true(
    cty.view().arguments[0].view().ity.view() is ItyApp(symbol, [_, _], _) &&
    symbol.view().logic_type.name() == b"tuple2",
  )
  assert_true(
    cty.view().result.view() is ItyApp(symbol, [_, _], _) &&
    symbol.view().logic_type.name() == b"tuple2",
  )
  guard body.view() is Ematch(_, [branch], []) &&
    branch.view().pattern.view().pattern.view()
    is Papp(pattern_symbol, [_, _], _) else {
    fail("tuple match did not retain its generated constructor")
  }
  assert_eq(pattern_symbol.view().name, b"Tuple2")
  let branch_body = branch.view().body
  guard branch_body.view() is Eexec(computation, _) &&
    computation.view() is Capp(constructor_routine, arguments) else {
    fail("tuple result did not execute its generated routine")
  }
  assert_eq(constructor_routine.view().name, b"Tuple2")
  assert_eq(arguments.length(), 2)
}

///|
test "tuple constructors adopt existing mutable component regions" {
  let source =
    #|module TupleRegions
    #|  use array.Array
    #|  let pair
    #|    (first : array int)
    #|    (second : array bool)
    #|    : (array int, array bool)
    #|  = first, second
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"tuple-regions.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("tuple region typing failed: \{diagnostic.message}")
    _ => fail("tuple region typing raised another error")
  }
  guard program_declarations(pmodule) is [PDlet(_, Cfun(cty, Some(_)), _, _)] &&
    cty.view().arguments is [first, second] &&
    cty.view().result.view() is ItyApp(tuple, [left, right], _) else {
    fail("tuple region fixture did not retain its routine shape")
  }
  assert_eq(tuple.view().logic_type.name(), b"tuple2")
  assert_true(left == first.view().ity)
  assert_true(right == second.view().ity)
}

///|
test "lemma proof controls preload tuple results for existential witnesses" {
  let source =
    #|module LemmaWitnessTuple
    #|  lemma pair_witness :
    #|    (exists first second : int. first = 0 /\ second = 0)
    #|    by true
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"lemma-witness-tuple.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("existential lemma witness typing failed: \{diagnostic.message}")
    _ => fail("existential lemma witness typing raised another error")
  }
  let lemma = pmodule
    .export_namespace()
    .find_routine([b"pair_witness'lemma"], None)
  assert_true(
    lemma.view().cty.view().result.view() is ItyApp(symbol, [_, _], _) &&
    symbol.view().logic_type.name() == b"tuple2",
  )
}

///|
test "reference locals allocate assign and dereference through the Ref builtin" {
  let source =
    #|module ProgramReferences
    #|  let update () : int
    #|    ensures { result = 2 }
    #|  =
    #|    let ref cell = 1 in
    #|    cell <- 2;
    #|    cell
    #|end
  let context = shared_program_context()
  let environment = fresh_program_environment(context)
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    environment,
    parsed_program_unit(source, b"program-references.mlw"),
  )
  guard program_declarations(pmodule) is [PDlet(_, Cfun(_, Some(body)), _, _)] else {
    fail("reference routine did not elaborate")
  }
  guard body.view() is Elet(reference_definition, sequence) &&
    reference_definition.view() is LDvar(reference, allocation) else {
    fail("reference binding did not retain its allocation")
  }
  assert_true(reference.view().ity.view() is ItyReg(_))
  guard terminal_program_expression(allocation).view()
    is Eexec(allocation_call, _) &&
    allocation_call.view() is Capp(reference_routine, [_]) else {
    fail("reference allocation did not call the builtin routine")
  }
  assert_eq(reference_routine.view().name, b"ref")
  guard sequence.view() is Elet(assignment_definition, dereference) &&
    assignment_definition.view() is LDvar(_, assignment) &&
    terminal_program_expression(assignment).view() is Eassign([write]) else {
    fail("reference sequence did not retain its assignment")
  }
  assert_true(write.view().region == reference)
  assert_eq(write.view().field.view().name, b"contents")
  guard dereference.view() is Eexec(read_call, _) &&
    read_call.view() is Capp(projection, [read_target]) else {
    fail("reference use did not call the contents projection")
  }
  assert_eq(projection.view().name, b"contents")
  assert_true(read_target == reference)
}

///|
test "regionful any expressions initialize references without duplicate regions" {
  let source =
    #|module RegionfulAnyReference
    #|  type cell = abstract { mutable ok : bool }
    #|  let allocate () : unit =
    #|    let ghost ref slot = any cell in
    #|    ()
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"regionful-any-reference.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("regionful any reference failed: \{diagnostic.message}")
    @mlw.MlwError(diagnostic) =>
      fail("regionful any reference failed: \{diagnostic.message}")
    _ => fail("regionful any reference raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"allocate"], None))
}

///|
test "reference initializer inference sees loop-index assignment values" {
  let source =
    #|module LoopReferenceInference
    #|  use int.Int
    #|  use import set.Fset as FS
    #|  let ghost function build (limit : int) : fset int =
    #|    let ref acc = FS.empty in
    #|    for index = 0 to limit do
    #|      acc <- FS.singleton index
    #|    done;
    #|    return acc
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"loop-reference-inference.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("loop reference inference failed: \{diagnostic.message}")
    _ => fail("loop reference inference raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"build"], None))
}

///|
test "array initializers infer machine elements from loop writes" {
  let source =
    #|module LoopArrayInference
    #|  use mach.int.Int63
    #|  use mach.array.Array63
    #|  let fill (limit : int63) : unit =
    #|    let values = Array63.make limit 0 in
    #|    for index = 0 to limit - 1 do
    #|      values[index] <- index
    #|    done
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"loop-array-inference.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("loop array inference failed: \{diagnostic.message}")
    _ => fail("loop array inference raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"fill"], None))
}

///|
test "array initializers infer machine elements from later calls" {
  let source =
    #|module CallArrayInference
    #|  use mach.int.Int63
    #|  use mach.array.Array63
    #|  use mach.peano.Peano as P
    #|  use ref.Ref
    #|  let consume
    #|    (solutions : ref P.t) (values : array int63)
    #|    (limit position : int63) : unit = ()
    #|  let fill (limit : int63) : unit =
    #|    let solutions = ref P.zero in
    #|    let values = Array63.make limit 0 in
    #|    consume solutions values limit 0
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"call-array-inference.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("call array inference failed: \{diagnostic.message}")
    _ => fail("call array inference raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"fill"], None))
}

///|
test "local routines capture outer variables and remain callable in their body" {
  let source =
    #|module LocalRoutine
    #|  use int.Int
    #|  let outer (base : int) : int =
    #|    let add (delta : int) : int = base + delta in
    #|    add 2
    #|end
  let context = shared_program_context()
  let environment = fresh_program_environment(context)
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    environment,
    parsed_program_unit(source, b"program-local-routine.mlw"),
  )
  guard program_declarations(pmodule)
    is [PDlet(_, Cfun(outer_cty, Some(body)), _, _)] else {
    fail("outer routine did not elaborate")
  }
  let captured = outer_cty.view().arguments[0]
  guard body.view() is Elet(definition, call) &&
    definition.view() is LDsym(local_symbol, local_computation) &&
    local_computation.view() is Cfun(local_body) else {
    fail("local routine did not become a symbol definition")
  }
  assert_eq(local_symbol.view().name, b"add")
  assert_true(
    local_computation.cty().view().effect.view().reads.any(variable => {
      variable == captured
    }),
  )
  guard local_body.view() is Eexec(addition, _) &&
    addition.view() is Capp(add_symbol, add_arguments) else {
    fail("local routine body did not call integer addition")
  }
  assert_eq(add_symbol.view().name, b"infix +")
  assert_eq(add_arguments.length(), 2)
  guard terminal_program_expression(call).view() is Eexec(local_call, _) &&
    local_call.view() is Capp(called_symbol, [_]) else {
    fail("local routine was not callable from its enclosing body")
  }
  assert_true(called_symbol == local_symbol)
}

///|
test "mutual and local recursion preserve groups cross-calls and captures" {
  let source =
    #|module RecursiveGroups
    #|  use int.Int
    #|  let rec even (value : int) : bool
    #|    variant { value }
    #|  = if value = 0 then true else odd (value - 1)
    #|  with odd (value : int) : bool
    #|    variant { value }
    #|  = if value = 0 then false else even (value - 1)
    #|  let outer (base : int) : int =
    #|    let rec descend (value : int) : int
    #|      variant { value }
    #|    = if value = 0 then base else descend (value - 1)
    #|    in descend 2
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-recursive-groups.mlw"),
  )
  guard program_declarations(pmodule)
    is [
      PDrec([even_definition, odd_definition], _, _),
      PDlet(_, Cfun(outer_cty, Some(outer_body)), _, _),
    ] else {
    fail("recursive groups did not retain their declaration structure")
  }
  let even = even_definition.view()
  let odd = odd_definition.view()
  assert_eq(even.symbol.view().name, b"even")
  assert_eq(odd.symbol.view().name, b"odd")
  assert_eq(even.variants.length(), 1)
  assert_eq(odd.variants.length(), 1)
  guard even.function_.view() is Cfun(even_body) &&
    even_body.view() is Eif(_, _, even_recursive) &&
    terminal_program_expression(even_recursive).view() is Eexec(even_call, _) &&
    even_call.view() is Capp(even_callee, [_]) else {
    fail("even did not retain its recursive call")
  }
  assert_true(even_callee == odd.internal_symbol)
  guard odd.function_.view() is Cfun(odd_body) &&
    odd_body.view() is Eif(_, _, odd_recursive) &&
    terminal_program_expression(odd_recursive).view() is Eexec(odd_call, _) &&
    odd_call.view() is Capp(odd_callee, [_]) else {
    fail("odd did not retain its recursive call")
  }
  assert_true(odd_callee == even.internal_symbol)
  let captured = outer_cty.view().arguments[0]
  guard outer_body.view() is Elet(local_definition, local_call) &&
    local_definition.view() is LDrec([local_recursive]) else {
    fail("local recursive routine did not become an LDrec binding")
  }
  let local_view = local_recursive.view()
  assert_eq(local_view.symbol.view().name, b"descend")
  assert_true(
    local_view.internal_symbol.view().cty.view().effect.view().reads.any(variable => {
      variable == captured
    }),
  )
  guard terminal_program_expression(local_call).view() is Eexec(call, _) &&
    call.view() is Capp(callee, [_]) else {
    fail("local recursive routine was not callable after its group")
  }
  assert_true(callee == local_view.symbol)
}

///|
test "recursive conditionals infer an omitted result from a concrete branch" {
  let source =
    #|module RecursiveConditionalResult
    #|  use int.Int
    #|  let rec descend (value : int)
    #|    variant { value }
    #|  = if value <= 0 then 42 else descend (value - 1)
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"recursive-conditional-result.mlw"),
  )
  let descend = pmodule.export_namespace().find_routine([b"descend"], None)
  guard descend.view().cty.view().result.view() is ItyApp(symbol, [], []) else {
    fail("recursive conditional retained an unresolved result type")
  }
  assert_eq(symbol.view().logic_type.name(), b"int")
}

///|
test "mutually recursive tail calls share inferred result constraints" {
  let source =
    #|module MutualResultConstraint
    #|  use int.Int
    #|  let rec first (i : int) variant { i } =
    #|    if i = 0 then 0 else second (i - 1) (i - 1)
    #|  with second (i j : int) variant { i, j } =
    #|    if j = 0 then first i else second i (j - 1)
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"mutual-result-constraint.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("mutual result inference failed: \{diagnostic.message}")
    _ => fail("mutual result inference raised another error")
  }
  for name in [b"first", b"second"] {
    let routine = pmodule.export_namespace().find_routine([name], None)
    assert_true(
      routine.view().cty.view().result.view() is ItyApp(symbol, [], _) &&
      symbol.view().logic_type.name() == b"int",
    )
  }
}

///|
test "recursive match patterns infer omitted parameter shapes" {
  let source =
    #|module RecursivePatternParameters
    #|  use list.List
    #|  let consume_int (_value : int) : unit = ()
    #|  let rec walk items values : unit
    #|    variant { items }
    #|  = match items, values with
    #|    | Nil, Nil -> ()
    #|    | Cons _ rest, Cons value remaining ->
    #|        consume_int value;
    #|        walk rest remaining
    #|    | _ -> ()
    #|    end
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"recursive-pattern-parameters.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("recursive pattern parameter typing failed: \{diagnostic.message}")
    _ => fail("recursive pattern parameter fixture raised another error")
  }
  let walk = pmodule.export_namespace().find_routine([b"walk"], None)
  guard walk.view().cty.view().arguments is [items, values] &&
    items.view().ity.view() is ItyApp(items_type, [_], []) &&
    values.view().ity.view() is ItyApp(values_type, [value_type], []) &&
    value_type.view() is ItyApp(integer_type, [], []) else {
    fail("recursive match parameters retained unresolved shapes")
  }
  assert_eq(items_type.view().logic_type.name(), b"list")
  assert_eq(values_type.view().logic_type.name(), b"list")
  assert_eq(integer_type.view().logic_type.name(), b"int")
}

///|
test "recursive bodies outrank coerced postconditions for omitted results" {
  let source =
    #|module RecursiveMachineResult
    #|  use int.Int
    #|  use mach.int.Int63
    #|  let rec advance (current limit : int63)
    #|    ensures { current <= result <= limit }
    #|    variant { limit - current }
    #|  = if current >= limit then limit else advance (current + 1) limit
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"recursive-machine-result.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("recursive machine result typing failed: \{diagnostic.message}")
    _ => fail("recursive machine result fixture raised another error")
  }
  let advance = pmodule.export_namespace().find_routine([b"advance"], None)
  guard advance.view().cty.view().result.view() is ItyApp(symbol, [], []) else {
    fail("recursive machine result retained an unresolved type")
  }
  assert_eq(symbol.view().logic_type.name(), b"int63")
}

///|
test "recursive group members preserve annotated reference initializers" {
  let source =
    #|module RecursiveReference
    #|  use ref.Ref
    #|  use int.Int
    #|  use mach.int.Int32
    #|  let rec first (value : int) : int
    #|    variant { value }
    #|  = if value = 0 then 0 else first (value - 1)
    #|  with second (size : int32) : unit
    #|    variant { 0 }
    #|  =
    #|    let remaining = ref size in
    #|    if 4 * !remaining < 5 * size then ()
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"recursive-reference.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("recursive reference initialization failed: \{diagnostic.message}")
    _ => fail("recursive reference initialization raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"second"], None))
}

///|
test "recursive functions export checked logic definitions and specification propositions" {
  let source =
    #|module RecursiveFunctionAxioms
    #|  use int.Int
    #|  use list.List
    #|  let rec ghost function descend (values : list int) : int
    #|    variant { values }
    #|    ensures { 0 <= result }
    #|    ensures { result = result }
    #|  = match values with
    #|    | Nil -> 0
    #|    | Cons _ tail -> descend tail
    #|    end
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"recursive-function-axioms.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("recursive function axioms failed: \{diagnostic.message}")
    _ => fail("recursive function axioms raised another error")
  }
  guard program_declarations(pmodule) is [PDrec([recursive], pure, _)] &&
    recursive.view().symbol.view().logic is RLls(logic) else {
    fail("recursive function did not retain one recursive declaration")
  }
  let propositions : Array[Bytes] = []
  let mut checked_definition = false
  for declaration in pure {
    match declaration.view() {
      Dlogic([definition]) if definition.view().symbol == logic => {
        checked_definition = true
        assert_true(definition.view().body.contains_logic_symbol(logic))
      }
      Dprop(Paxiom, symbol, _) => propositions.push(symbol.view().name)
      _ => ()
    }
  }
  assert_true(checked_definition)
  assert_false(propositions.any(name => name == b"descend'def"))
  assert_true(propositions.any(name => name == b"descend'spec'0"))
  assert_true(propositions.any(name => name == b"descend'spec"))
}

///|
test "recursive pure functions with preconditions export guarded definition axioms" {
  let source =
    #|module RecursiveGuardedDefinition
    #|  use int.Int
    #|  let rec ghost function countdown (value : int) : int
    #|    requires { 0 <= value }
    #|    variant { value }
    #|  = if value = 0 then 0 else countdown (value - 1)
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"recursive-guarded-definition.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("recursive guarded definition failed: \{diagnostic.message}")
    _ => fail("recursive guarded definition raised another error")
  }
  guard program_declarations(pmodule) is [PDrec([recursive], pure, _)] &&
    recursive.view().symbol.view().logic is RLls(logic) else {
    fail("recursive guarded definition lost its logic symbol")
  }
  let mut parameter_seen = false
  let mut guarded_axiom_seen = false
  for declaration in pure {
    match declaration.view() {
      Dparam(symbol) if symbol == logic => parameter_seen = true
      Dlogic(_) =>
        fail("guarded recursive definition was emitted as a logic definition")
      Dprop(Paxiom, proposition, formula) if proposition.view().name ==
        b"countdown'def" => {
        guard formula.view() is Tquant(ForallQuantifier, [_], _, quantified) &&
          quantified.view() is Tbinop(Implies, _, _) else {
          fail(
            "guarded definition axiom did not close a precondition implication",
          )
        }
        guarded_axiom_seen = true
      }
      _ => ()
    }
  }
  assert_true(parameter_seen)
  assert_true(guarded_axiom_seen)
}

///|
test "recursive logic fallback keeps each definition's source identity" {
  let source =
    #|module RecursiveFunctionFallback
    #|  use int.Int
    #|  let rec ghost function guarded (value : int) : int
    #|    requires { true }
    #|    variant { value }
    #|  = value
    #|  with function diverging (value : int) : int
    #|    variant { value }
    #|  = diverging value
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"recursive-function-fallback.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("recursive function fallback failed: \{diagnostic.message}")
    _ => fail("recursive function fallback raised another error")
  }
  guard program_declarations(pmodule) is [PDrec([_, diverging], pure, _)] &&
    diverging.view().symbol.view().logic is RLls(diverging_logic) else {
    fail("recursive function fallback lost its recursive group")
  }
  let mut parameter_seen = false
  let mut axiom_line : Int64? = None
  for declaration in pure {
    match declaration.view() {
      Dparam(symbol) if symbol == diverging_logic => parameter_seen = true
      Dprop(Paxiom, proposition, _) if proposition.view().name ==
        b"diverging'def" =>
        axiom_line = proposition.view().origin
          .source_span()
          .map(span => span.view().start_line)
      _ => ()
    }
  }
  assert_true(parameter_seen)
  assert_eq(axiom_line, Some(7L))
}

///|
test "routine kinds and omitted result annotations retain semantic projections" {
  let source =
    #|module RoutineKinds
    #|  use int.Int
    #|  let function successor (value : int) = value + 1
    #|  let predicate nonnegative (value : int) = value >= 0
    #|  let lemma reflexive (value : int)
    #|    ensures { value = value }
    #|  = ()
    #|  let ordinary (value : int) = successor value
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-routine-kinds.mlw"),
  )
  guard program_declarations(pmodule)
    is [
      PDlet(successor, Cfun(successor_cty, Some(_)), [successor_pure], _),
      PDlet(nonnegative, Cfun(nonnegative_cty, Some(_)), [predicate_pure], _),
      PDlet(lemma, Cfun(lemma_cty, Some(_)), [lemma_pure], _),
      PDlet(_, Cfun(ordinary_cty, Some(ordinary)), [], _),
    ] else {
    fail("routine kinds did not elaborate with their pure projections")
  }
  guard successor.view().logic is RLls(successor_logic) &&
    successor_pure.view() is Dlogic([successor_definition]) &&
    successor_definition.view().symbol == successor_logic else {
    fail("function routine did not expose a logical function")
  }
  assert_true(successor.kind() is @mlw.RKfunc)
  assert_true(
    successor_cty.view().result.view() is ItyApp(symbol, [], _) &&
    symbol.view().logic_type.name() == b"int",
  )
  guard nonnegative.view().logic is RLls(predicate_logic) &&
    predicate_pure.view() is Dlogic([predicate_definition]) &&
    predicate_definition.view().symbol == predicate_logic else {
    fail("predicate routine did not expose a logical predicate")
  }
  assert_true(nonnegative.kind() is @mlw.RKpred)
  assert_true(
    nonnegative_cty.view().result.view() is ItyApp(symbol, [], _) &&
    symbol.view().logic_type.name() == b"bool",
  )
  assert_true(lemma.view().logic is RLlemma)
  assert_true(lemma_pure.view() is Dprop(Paxiom, _, _))
  assert_true(lemma.is_ghost())
  assert_false(lemma_cty.is_ghost())
  assert_true(ordinary_cty.view().result == successor_cty.view().result)
  guard terminal_program_expression(ordinary).view() is Eexec(call, _) &&
    call.view() is Capp(called, [_]) else {
    fail("ordinary routine did not call the projected function routine")
  }
  assert_true(called == successor)
}

///|
test "function and predicate specifications export derived spec axioms" {
  let source =
    #|module RoutineSpecAxioms
    #|  use int.Int
    #|  let function successor (value : int) : int
    #|    ensures { result = value + 1 }
    #|  = value + 1
    #|  let predicate nonnegative (value : int)
    #|    ensures { result <-> 0 <= value }
    #|  = value >= 0
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"routine-spec-axioms.mlw"),
  )
  guard program_declarations(pmodule)
    is [PDlet(_, _, [_, function_spec], _), PDlet(_, _, [_, predicate_spec], _)] &&
    function_spec.view() is Dprop(Paxiom, function_symbol, _) &&
    predicate_spec.view() is Dprop(Paxiom, predicate_symbol, _) else {
    fail("routine specifications did not produce derived spec axioms")
  }
  assert_eq(function_symbol.view().name, b"successor'spec")
  assert_eq(predicate_symbol.view().name, b"nonnegative'spec")
  assert_true(
    function_symbol.view().origin
    .attributes()
    .any(attribute => attribute == b"W:non_conservative_extension:N"),
  )
  assert_true(
    predicate_symbol.view().origin
    .attributes()
    .any(attribute => attribute == b"W:non_conservative_extension:N"),
  )
}

///|
test "value-returning lemmas export an existential postcondition axiom" {
  let source =
    #|module ValueReturningLemma
    #|  let lemma witness (value : int) : (result : int)
    #|    ensures { result = value }
    #|  = value
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"value-returning-lemma.mlw"),
  )
  guard program_declarations(pmodule)
    is [PDlet(_, Cfun(_, Some(_)), [axiom], _)] &&
    axiom.view() is Dprop(Paxiom, _, formula) &&
    formula.view() is Tquant(ForallQuantifier, _, _, quantified) &&
    quantified.view() is Tquant(ExistsQuantifier, [_], _, _) else {
    fail("value-returning lemma did not existentially close its result")
  }
}

///|
test "program function parameters apply through the synthesized HighOrd routine" {
  let source =
    #|module ProgramHigherOrder
    #|  let apply (f : int -> int) (value : int) : int = f value
    #|end
  let context = shared_program_context()
  let environment = fresh_program_environment(context)
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    environment,
    parsed_program_unit(source, b"program-higher-order.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("higher-order program elaboration failed")
    }
    _ => fail("higher-order program elaboration raised another error")
  }
  guard program_declarations(pmodule) is [PDlet(_, Cfun(cty, Some(body)), _, _)] else {
    fail("higher-order program routine did not elaborate")
  }
  assert_true(
    cty.view().arguments[0].view().ity.view() is ItyApp(symbol, [_, _], _) &&
    symbol.view().logic_type.name() == b"infix ->",
  )
  guard terminal_program_expression(body).view() is Eexec(application, _) &&
    application.view() is Capp(symbol, [_, _]) else {
    fail("program function application did not become a routine call")
  }
  assert_eq(symbol.view().name, b"infix @")
  assert_true(
    pmodule.view().items.any(item => {
      item is Uuse(key) && key == environment.high_order_module().key()
    }),
  )
}

///|
test "pre-applied projections load HighOrd for remaining arguments" {
  let source =
    #|module CurriedProjection
    #|  use int.Int
    #|  use matrix.Matrix
    #|  let observe (value : matrix int) : unit =
    #|    check { value.elts 0 0 = value.elts 0 0 }
    #|end
  let context = shared_program_context()
  let environment = fresh_program_environment(context)
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    environment,
    parsed_program_unit(source, b"curried-projection.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("curried projection failed: \{diagnostic.message}")
    _ => fail("curried projection raised another error")
  }
  assert_true(
    pmodule
    .pure_theory()
    .used_theories()
    .any(theory => {
      theory.key() == environment.high_order_module().pure_theory().key()
    }),
  )
}

///|
test "applications through cloned function aliases load HighOrd" {
  let source =
    #|module FunctionAlias
    #|  type vars = int -> int
    #|end
    #|module ClonedFunctionAlias
    #|  clone FunctionAlias as Alias
    #|  function apply (f : Alias.vars) (value : int) : int = f value
    #|end
  let context = shared_program_context()
  let environment = fresh_program_environment(context)
  let filename = b"cloned-function-alias.mlw"
  let parsed = @parser.parse_mlw_file(@utf8.encode(source)[:], filename~)
  let elaborated = @why3_elab.elaborate_file(context, environment, parsed) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("cloned function alias typing failed: \{diagnostic.message}")
    _ => fail("cloned function alias fixture raised another error")
  }
  assert_eq(elaborated.units().length(), 2)
}

///|
test "direct mixfix applications prefer function-valued aliases" {
  let source =
    #|module FunctionValuedMixfix
    #|  type table = { mutable contents : int }
    #|  val lookup (key : int) (table : table) : int
    #|  let ([]) = lookup
    #|  let run (table : table) : int = 1[table]
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"function-valued-mixfix.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("function-valued mixfix alias failed: \{diagnostic.message}")
    _ => fail("function-valued mixfix alias raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"run"], None))
}

///|
test "cloning a recursive local routine alias rebuilds its decrease predicate" {
  let source =
    #|module RecursiveAlias
    #|  type tree 'a = Leaf | Node (tree 'a)
    #|  let rec lemma walk (tree : tree 'a) : unit
    #|    variant { tree }
    #|  = let ghost again = walk in
    #|    match tree with
    #|    | Leaf -> ()
    #|    | Node child -> again child
    #|    end
    #|end
    #|module ClonedRecursiveAlias
    #|  clone RecursiveAlias as Alias
    #|end
  let context = shared_program_context()
  let environment = fresh_program_environment(context)
  let filename = b"cloned-recursive-alias.mlw"
  let parsed = @parser.parse_mlw_file(@utf8.encode(source)[:], filename~)
  let elaborated = @why3_elab.elaborate_file(context, environment, parsed) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("recursive alias clone failed: \{diagnostic.message}")
    _ => fail("recursive alias clone raised another error")
  }
  assert_eq(elaborated.units().length(), 2)
}

///|
test "anonymous program functions execute as HighOrd values" {
  let source =
    #|module AnonymousProgramFunction
    #|  let run (value : int) : int = (fun (item : int) -> item) value
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"anonymous-program-function.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("anonymous program function elaboration failed")
    }
    _ => fail("anonymous program function raised another error")
  }
  guard program_declarations(pmodule) is [PDlet(_, Cfun(_, Some(body)), _, _)] else {
    fail("anonymous program function did not elaborate")
  }
  guard body.view() is Elet(definition, application) &&
    definition.view() is LDvar(_, function_value) &&
    function_value.view() is Eexec(function_computation, function_cty) &&
    function_computation.view() is Cfun(_) else {
    fail("anonymous routine did not execute into a function-valued proxy")
  }
  assert_true(function_computation.cty().view().arguments.length() == 1)
  assert_true(function_cty.view().arguments.is_empty())
  assert_true(
    function_cty.view().result.view() is ItyApp(symbol, [_, _], _) &&
    symbol.view().logic_type.name() == b"infix ->",
  )
  guard terminal_program_expression(application).view() is Eexec(call, _) &&
    call.view() is Capp(symbol, [_, _]) else {
    fail("anonymous program function was not applied")
  }
  assert_eq(symbol.view().name, b"infix @")
}

///|
test "named routines become function values when passed to higher-order calls" {
  let source =
    #|module NamedProgramFunction
    #|  use int.Int
    #|  let increment (value : int) : int
    #|    ensures { result = value + 1 }
    #|  = value + 1
    #|  let apply (f : int -> int) (value : int) : int = f value
    #|  let run () : int = apply increment 0
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"named-program-function.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("named program function elaboration failed")
    }
    _ => fail("named program function raised another error")
  }
  guard program_declarations(pmodule)
    is [
      PDlet(increment, _, _, _),
      PDlet(apply, _, _, _),
      PDlet(_, Cfun(_, Some(run)), _, _),
    ] else {
    fail("named higher-order routines did not elaborate")
  }
  let mut partial_value : @mlw.Expr? = None
  for value in outer_program_let_values(run) {
    if value.view() is Eexec(partial_call, _) &&
      partial_call.view() is Capp(partial_symbol, []) &&
      partial_symbol == increment {
      partial_value = Some(value)
      break
    }
  }
  guard partial_value is Some(function_value) &&
    function_value.view() is Eexec(partial_call, executable_cty) &&
    partial_call.view() is Capp(partial_symbol, []) else {
    fail("routine argument did not become a partial function value")
  }
  assert_true(partial_symbol == increment)
  assert_true(partial_call.cty().view().arguments.length() == 1)
  assert_true(executable_cty.view().arguments.is_empty())
  assert_eq(executable_cty.view().postconditions.length(), 1)
  guard terminal_program_expression(run).view() is Eexec(call, _) &&
    call.view() is Capp(called, [_, _]) else {
    fail("higher-order routine was not called with its function value")
  }
  assert_true(called == apply)
}

///|
test "pure logic functions become function values when partially applied" {
  let source =
    #|module NamedLogicFunction
    #|  use int.Int
    #|  function successor (value : int) : int = value + 1
    #|  let ghost apply (f : int -> int) (value : int) : int = f value
    #|  let ghost run () : int = apply successor 0
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"named-logic-function.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("named logic function elaboration failed: \{diagnostic.message}")
    _ => fail("named logic function raised another error")
  }
  guard program_declarations(pmodule)
    is [PDpure(_, _), PDlet(_, _, _, _), PDlet(_, Cfun(_, Some(run)), _, _)] else {
    fail("named logic function declarations did not elaborate")
  }
  assert_true(
    run.ity().view() is ItyApp(integer, [], _) &&
    integer.view().logic_type.name() == b"int",
  )
  assert_true(
    pmodule.export_namespace().find_routine([b"run"], None).view().cty.view().result ==
    run.ity(),
  )
}

///|
test "routine results accept subsequent higher-order arguments" {
  let source =
    #|module CurriedProgramFunction
    #|  use int.Int
    #|  let add (base : int) : int -> int =
    #|    fun (value : int) -> base + value
    #|  let run () : int = add 1 2
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"curried-program-function.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("curried program function elaboration failed")
    }
    _ => fail("curried program function raised another error")
  }
  guard program_declarations(pmodule)
    is [PDlet(add, _, _, _), PDlet(_, Cfun(_, Some(run)), _, _)] else {
    fail("curried routines did not elaborate")
  }
  let mut direct_value : @mlw.Expr? = None
  for value in outer_program_let_values(run) {
    if terminal_program_expression(value).view() is Eexec(direct_computation, _) &&
      direct_computation.view() is Capp(direct_symbol, [_]) &&
      direct_symbol == add {
      direct_value = Some(value)
      break
    }
  }
  guard direct_value is Some(direct_call) &&
    terminal_program_expression(direct_call).view()
    is Eexec(direct_computation, _) &&
    direct_computation.view() is Capp(direct_symbol, [_]) else {
    fail("curried call did not retain its direct routine application")
  }
  assert_true(direct_symbol == add)
  guard terminal_program_expression(run).view() is Eexec(application, _) &&
    application.view() is Capp(symbol, [_, _]) else {
    fail("curried result did not receive its remaining argument")
  }
  assert_eq(symbol.view().name, b"infix @")
}

///|
test "recursive routines infer omitted parameter and result types from contracts" {
  let source =
    #|module RecursiveInference
    #|  use int.Int
    #|  let rec descend value
    #|    requires { value >= 0 }
    #|    variant { value }
    #|    ensures { result >= 0 }
    #|  = if value = 0 then 0 else descend (value - 1)
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"recursive-inference.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("recursive routine inference failed")
    }
    _ => fail("recursive routine inference raised another error")
  }
  guard program_declarations(pmodule) is [PDrec([definition], _, _)] else {
    fail("recursive routine did not retain its declaration group")
  }
  let view = definition.view()
  assert_eq(view.symbol.view().cty.view().arguments.length(), 1)
  assert_true(
    view.symbol.view().cty.view().arguments[0].view().ity.view()
    is ItyApp(symbol, [], _) &&
    symbol.view().logic_type.name() == b"int",
  )
  assert_true(
    view.symbol.view().cty.view().result.view() is ItyApp(symbol, [], _) &&
    symbol.view().logic_type.name() == b"int",
  )
}

///|
test "local recursive routines specialize an unconstrained result to unit" {
  let source =
    #|module RecursiveUnitInference
    #|  use list.List
    #|  let walk (values : list int) : unit =
    #|    let rec aux (current : list int) =
    #|      match current with
    #|      | Nil -> ()
    #|      | Cons _ rest -> step rest
    #|      end
    #|    with step (current : list int) = aux current
    #|    in
    #|    step values
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-recursive-unit-inference.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("recursive unit inference failed: \{diagnostic.message}")
    _ => fail("recursive unit inference raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"walk"], None))
}

///|
test "file elaboration checks a module implementation against its interface" {
  let source =
    #|module Signature
    #|  val identity (value : int) : int
    #|    ensures { result = value }
    #|end
    #|
    #|module Implementation : Signature
    #|  let identity value = value
    #|end
  let context = @identity.CompilationContext::new()
  let environment = isolated_program_environment(context)
  let parsed = @parser.parse_mlw_file(
    @utf8.encode(source)[:],
    filename=b"module-interface.mlw",
  )
  let elaborated = @why3_elab.elaborate_file(context, environment, parsed) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("module-interface elaboration failed")
    }
  }
  guard elaborated.units()
    is [
      @why3_elab.ElaboratedModule(interface_module),
      @why3_elab.ElaboratedModule(implementation_module),
    ] else {
    fail("module-interface file did not elaborate as two modules")
  }
  assert_eq(interface_module.key().view().name, b"Signature")
  assert_eq(implementation_module.key().view().name, b"Implementation")
  assert_eq(
    implementation_module
    .export_namespace()
    .find_routine([b"identity"], None)
    .view().cty.view().arguments.length(),
    1,
  )
}

///|
test "file theories retain a program module counterpart for later use" {
  let source =
    #|theory Shared
    #|  type token = Token int
    #|  function value (item : token) : int =
    #|    match item with Token result -> result end
    #|end
    #|
    #|module Client
    #|  use Shared
    #|  let unwrap (item : token) : int = value item
    #|end
  let context = @identity.CompilationContext::new()
  let parsed = @parser.parse_mlw_file(
    @utf8.encode(source)[:],
    filename=b"theory-module-use.mlw",
  )
  let environment = isolated_program_environment(context)
  let elaborated = @why3_elab.elaborate_file(context, environment, parsed) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("module could not use a preceding source theory")
    }
    _ => fail("theory/module elaboration raised another error")
  }
  guard elaborated.units()
    is [
      @why3_elab.ElaboratedTheory(theory),
      @why3_elab.ElaboratedModule(client),
    ] else {
    fail("theory/module file did not retain its source-level unit kinds")
  }
  assert_eq(theory.key().view().name, b"Shared")
  let shared_module = environment.resolve_module(
    @theory.TheoryKey::new([], b"Shared"),
    None,
  )
  assert_true(
    shared_module.export_namespace().view().types.any(entry => {
      entry.0 == b"token" &&
      entry.1.view().logic_type ==
      theory.export_namespace().find_type([b"token"], None)
    }),
  )
  let client_exports = client.export_namespace().view()
  assert_true(client_exports.routines.any(entry => entry.0 == b"unwrap"))
}

///|
test "local program declarations shadow names imported by use" {
  let source =
    #|module ImportedNames
    #|  use int.Int
    #|  type source = { data : int }
    #|  let rec fill (remaining : int) : int
    #|    variant { remaining }
    #|  = if remaining <= 0 then 0 else fill (remaining - 1)
    #|end
    #|
    #|module LocalShadows
    #|  use int.Int
    #|  use ImportedNames
    #|  type target = { data : int }
    #|    invariant { 0 <= data }
    #|    by { data = 0 }
    #|  let rec fill (remaining : int) : int
    #|    variant { remaining }
    #|  = if remaining <= 0 then 0 else fill (remaining - 1)
    #|  let call_local () : int =
    #|    let fill (value : int) : int = value in
    #|    fill 1
    #|end
  let context = @identity.CompilationContext::new()
  let parsed = @parser.parse_mlw_file(
    @utf8.encode(source)[:],
    filename=b"program-import-shadowing.mlw",
  )
  let elaborated = @why3_elab.elaborate_file(
    context,
    isolated_program_environment(context),
    parsed,
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("local program shadowing failed: \{diagnostic.message}")
    _ => fail("local program shadowing raised another error")
  }
  guard elaborated.units()
    is [
      @why3_elab.ElaboratedModule(imported),
      @why3_elab.ElaboratedModule(shadowing),
    ] else {
    fail("program shadowing fixture did not elaborate two modules")
  }
  assert_true(
    shadowing.export_namespace().find_routine([b"data"], None) !=
    imported.export_namespace().find_routine([b"data"], None),
  )
  assert_true(
    shadowing.export_namespace().find_routine([b"fill"], None) !=
    imported.export_namespace().find_routine([b"fill"], None),
  )
  ignore(shadowing.export_namespace().find_routine([b"call_local"], None))
}

///|
test "local pure routines expose mapping variables only to specifications" {
  let source =
    #|module LocalRoutineMappings
    #|  use int.Int
    #|  let verify (base : int) : unit =
    #|    let function local (value : int) : int = value + base in
    #|    let ghost function projected (value : int) : int
    #|      ensures { result = local value }
    #|    = local value
    #|    in
    #|    assert { local 1 = base + 1 };
    #|    assert { projected 2 = local 2 }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"local-routine-mappings.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("local routine mapping elaboration failed: \{diagnostic.message}")
    @mlw.MlwError(diagnostic) =>
      fail("local routine mapping elaboration failed: \{diagnostic.message}")
    @logic.TypeError(diagnostic) =>
      fail("local routine mapping elaboration failed: \{diagnostic.message}")
    _ => fail("local routine mapping elaboration raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"verify"], None))
}

///|
test "dot projections are not captured by same-named specification locals" {
  let source =
    #|module ProjectionLocalShadow
    #|  use int.Int
    #|  type bounds = private { max : int }
    #|  val create (max : int) : bounds
    #|    ensures { result.max = max }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"projection-local-shadow.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("projection/local shadow elaboration failed: \{diagnostic.message}")
    @logic.TypeError(diagnostic) =>
      fail("projection/local shadow elaboration failed: \{diagnostic.message}")
    _ => fail("projection/local shadow elaboration raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"create"], None))
}

///|
test "dot projections select fields from the receiver record type" {
  let source =
    #|module StoredProjection
    #|  use int.Int
    #|  use list.List
    #|  type stored 'a = { xs : list 'a }
    #|  let function empty (ignored : int) : stored 'a = { xs = Nil }
    #|end
    #|
    #|module ReceiverProjection
    #|  use int.Int
    #|  use list.List
    #|  use StoredProjection
    #|  type current 'a = {
    #|    xs : list 'a;
    #|    ghost prior : stored 'a;
    #|  } invariant {
    #|    prior.xs = xs
    #|  } by {
    #|    xs = Nil; prior = empty 0
    #|  }
    #|end
  let context = @identity.CompilationContext::new()
  let parsed = @parser.parse_mlw_file(
    @utf8.encode(source)[:],
    filename=b"receiver-projection.mlw",
  )
  let elaborated = @why3_elab.elaborate_file(
    context,
    isolated_program_environment(context),
    parsed,
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("receiver projection elaboration failed: \{diagnostic.message}")
    @logic.TypeError(diagnostic) =>
      fail("receiver projection elaboration failed: \{diagnostic.message}")
    _ => fail("receiver projection fixture raised another error")
  }
  guard elaborated.units()
    is [@why3_elab.ElaboratedModule(_), @why3_elab.ElaboratedModule(receiver)] else {
    fail("receiver projection fixture did not elaborate two modules")
  }
  ignore(receiver.export_namespace().find_type([b"current"], None))
}

///|
test "explicit pure functions shadow aliased record projections" {
  let source =
    #|module ProjectionSource
    #|  use int.Int
    #|  type source_model = { old_card : int }
    #|  type source = { ghost m : source_model }
    #|end
    #|
    #|module ProjectionFunctionShadow
    #|  use int.Int
    #|  clone ProjectionSource as Nested
    #|  type t = Nested.source
    #|  type m = { card : int }
    #|  function m (_value : t) : m = { card = 0 }
    #|  meta coercion function m
    #|  val empty () : t
    #|    ensures { result.m.card = 0 }
    #|  let lemma verify_shadow (value : t) : unit =
    #|    if value.m.card > 0 then ()
    #|end
  let context = @identity.CompilationContext::new()
  let parsed = @parser.parse_mlw_file(
    @utf8.encode(source)[:],
    filename=b"projection-function-shadow.mlw",
  )
  let elaborated = @why3_elab.elaborate_file(
    context,
    isolated_program_environment(context),
    parsed,
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("projection function shadowing failed: \{diagnostic.message}")
    _ => fail("projection function shadowing raised another error")
  }
  guard elaborated.units()
    is [@why3_elab.ElaboratedModule(_), @why3_elab.ElaboratedModule(shadow)] else {
    fail("projection function shadowing did not elaborate two modules")
  }
  ignore(shadow.export_namespace().find_routine([b"verify_shadow"], None))
}

///|
test "pattern binders shadow omitted routine parameters during inference" {
  let source =
    #|module PatternParameterShadow
    #|  use int.Int
    #|  use list.List
    #|  let zero (value : int) : bool = value = 0
    #|  let inspect (context : list 'a) value : unit =
    #|    match context, value with
    #|    | Nil, Nil -> ()
    #|    | Cons head tail, Cons value rest ->
    #|        if zero value then () else ()
    #|    | _ -> ()
    #|    end
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"pattern-parameter-shadow.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("pattern parameter shadowing failed: \{diagnostic.message}")
    @logic.TypeError(diagnostic) =>
      fail("pattern parameter shadowing failed: \{diagnostic.message}")
    _ => fail("pattern parameter shadowing raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"inspect"], None))
}

///|
test "match result refinement retypes earlier partial constructor branches" {
  let source =
    #|module PartialConstructorBranches
    #|  type sum 'a 'b = Left 'a | Right 'b
    #|  let normalize (value : sum 'a 'b) =
    #|    match value with
    #|    | Left left -> Left left
    #|    | Right right -> Right right
    #|    end
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"partial-constructor-branches.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail(
        "partial constructor branch refinement failed: \{diagnostic.message}",
      )
    _ => fail("partial constructor branch fixture raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"normalize"], None))
}

///|
test "match branches retain a shared inferred polymorphic result" {
  let source =
    #|module SharedMatchInference
    #|  type tag = First | Second
    #|  type high 'a
    #|  type weak 'a
    #|  type condition 'a
    #|  val base () : weak 'a
    #|  val tail () : weak ('a, int)
    #|  val (--) (left : weak 'a) (right : weak ('a, int)) : weak 'a
    #|  val (%) (value : weak 'a) (condition : condition 'a) : weak 'a
    #|  val guard () : condition 'a
    #|  val old_guard () : condition ('a, int)
    #|  val finish (value : weak 'a) : high 'a
    #|  let choose (tag : tag) : high 'a =
    #|    let selected = match tag with
    #|      | First ->
    #|          let code_false = base () in
    #|          let code_true = base () -- tail () in
    #|          code_true % guard () -- (code_false % old_guard ())
    #|      | Second -> base () -- tail ()
    #|      end in
    #|    finish selected
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"shared-match-inference.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("shared match inference failed: \{diagnostic.message}")
    @mlw.MlwError(diagnostic) =>
      fail("shared match inference failed: \{diagnostic.message}")
    _ => fail("shared match inference raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"choose"], None))
}

///|
test "nested conditional returns retain the routine result context" {
  let source =
    #|module NestedConditionalReturn
    #|  use int.Int
    #|  let compare (left right : int) : int =
    #|    if left = 0 then return left
    #|    else begin
    #|      let copy = left in
    #|      if copy = right then return 0;
    #|      if copy > right then return copy else return (- copy)
    #|    end
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"nested-conditional-return.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("nested conditional return failed: \{diagnostic.message}")
    @logic.TypeError(diagnostic) =>
      fail("nested conditional return failed: \{diagnostic.message}")
    _ => fail("nested conditional return raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"compare"], None))
}

///|
test "return payloads constrain untyped local numeric results" {
  let source =
    #|module ReturnPayloadLocal
    #|  use mach.int.Int32
    #|  let choose (flag : bool) : int32 =
    #|    let result = if flag then 0 else 1 in
    #|    return result
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"return-payload-local.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("return payload local inference failed: \{diagnostic.message}")
    @logic.TypeError(diagnostic) =>
      fail("return payload local inference failed: \{diagnostic.message}")
    _ => fail("return payload local inference raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"choose"], None))
}

///|
test "return payloads retain routine types in unit statement contexts" {
  let source =
    #|module ReturnPayloadStatement
    #|  use mach.int.Int32
    #|  let choose (flag : bool) : int32 =
    #|    if flag then begin
    #|      let result = if flag then 0 else 1 in
    #|      return result
    #|    end;
    #|    2
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"return-payload-statement.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("statement return payload failed: \{diagnostic.message}")
    @logic.TypeError(diagnostic) =>
      fail("statement return payload failed: \{diagnostic.message}")
    _ => fail("statement return payload raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"choose"], None))
}

///|
test "later reference assignments override default numeric reads" {
  let source =
    #|module ReferenceNumericAssignment
    #|  use int.Int
    #|  use mach.int.UInt32
    #|  let track (bits : uint32) : unit =
    #|    let ref shift = 1 + (bits - 1) in
    #|    while False do
    #|      invariant { 0 <= shift < 64 }
    #|      if shift = 0 then begin
    #|        shift <- bits
    #|      end
    #|    done
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"reference-numeric-assignment.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("reference numeric assignment failed: \{diagnostic.message}")
    @logic.TypeError(diagnostic) =>
      fail("reference numeric assignment failed: \{diagnostic.message}")
    _ => fail("reference numeric assignment raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"track"], None))
}

///|
test "reference comparisons do not default typed initializers to int" {
  let source =
    #|module ReferenceTypedInitializer
    #|  use int.Int
    #|  use mach.int.Int32
    #|  let count_down (size : int32) : unit =
    #|    let ref remaining = size - 1 in
    #|    while remaining >= 2 do
    #|      remaining <- remaining - 1
    #|    done
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"reference-typed-initializer.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("reference typed initializer failed: \{diagnostic.message}")
    @logic.TypeError(diagnostic) =>
      fail("reference typed initializer failed: \{diagnostic.message}")
    _ => fail("reference typed initializer raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"count_down"], None))
}

///|
test "nested typed arithmetic determines reference contents" {
  let source =
    #|module ReferenceNestedTypedArithmetic
    #|  use int.Int
    #|  use mach.int.UInt32
    #|  type parameters = { exponent : uint32 }
    #|  let count_down (size : uint32) (parameters : parameters) : unit =
    #|    let ref remaining = 1 + (size - 1) % parameters.exponent in
    #|    while (remaining <- remaining - 1; remaining) > 0 do
    #|      ()
    #|    done
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"reference-nested-typed-arithmetic.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("nested reference arithmetic failed: \{diagnostic.message}")
    @logic.TypeError(diagnostic) =>
      fail("nested reference arithmetic failed: \{diagnostic.message}")
    _ => fail("nested reference arithmetic raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"count_down"], None))
}

///|
test "generic calls determine reference contents from arguments" {
  let source =
    #|module ReferenceGenericCall
    #|  use mach.int.UInt64
    #|  let identity (value : 'a) : 'a = value
    #|  let copy (source : uint64) : unit =
    #|    let ref target = 0 in
    #|    target <- identity source
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"reference-generic-call.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("generic reference call failed: \{diagnostic.message}")
    @mlw.MlwError(diagnostic) =>
      fail("generic reference call failed: \{diagnostic.message}")
    _ => fail("generic reference call raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"copy"], None))
}

///|
test "reference lambda initializers retain downstream monomorphic constraints" {
  let source =
    #|module ReferenceLambdaConstraint
    #|  use int.Int
    #|  use map.Map
    #|  use ref.Ref
    #|  let update () : unit =
    #|    let ghost index = ref (fun item -> item) in
    #|    index := set !index 0 1
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"reference-lambda-constraint.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("reference lambda inference failed: \{diagnostic.message}")
    _ => fail("reference lambda fixture raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"update"], None))
}

///|
test "field assignments constrain initializers across local recursion" {
  let source =
    #|module RecursiveInitializerConstraint
    #|  use int.Int
    #|  use list.List
    #|  use list.Mem
    #|  use array.Array
    #|  type storage 'a = { mutable data : array (list 'a) }
    #|  let replace (target : storage 'a) : unit =
    #|    let fresh = make 1 Nil in
    #|    let rec inspect (index : int) : unit
    #|      requires { forall value : 'a. mem value fresh[0] -> true }
    #|      variant { index }
    #|    = if index <= 0 then () else inspect (index - 1)
    #|    in
    #|    inspect 0;
    #|    target.data <- fresh
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"recursive-initializer-constraint.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("recursive initializer inference failed: \{diagnostic.message}")
    _ => fail("recursive initializer fixture raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"replace"], None))
}

///|
test "field assignment constraints keep fresh mutable initializer regions" {
  let source =
    #|module FreshAssignedArrayRegion
    #|  use array.Array as A
    #|  type holder 'a = {
    #|    dummy : 'a;
    #|    mutable data : A.array 'a;
    #|  }
    #|  let replace (target : holder 'a) : unit =
    #|    let fresh = A.make 1 target.dummy in
    #|    A.blit target.data 0 fresh 0 0;
    #|    target.data <- fresh
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"fresh-assigned-array-region.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("fresh assigned array region failed: \{diagnostic.message}")
    _ => fail("fresh assigned array region fixture raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"replace"], None))
}

///|
test "immutable record constructors adopt mutable field regions" {
  let source =
    #|module ImmutableRecordFieldRegions
    #|  use int.Int
    #|  use array.Array
    #|  type pair = {
    #|    left : array int;
    #|    right : array int;
    #|  }
    #|  invariant { left.length = right.length }
    #|  by { left = Array.make 0 0; right = Array.make 0 0 }
    #|  let make_pair (left : array int) : pair =
    #|    let right = Array.make 1 0 in
    #|    { left = left; right = right }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"immutable-record-field-regions.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("immutable record field regions failed: \{diagnostic.message}")
    @mlw.MlwError(diagnostic) =>
      fail("immutable record field regions failed: \{diagnostic.message}")
    _ => fail("immutable record field regions raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"make_pair"], None))
}

///|
test "variant constructors preserve contextual mutable regions" {
  let source =
    #|module ContextualVariantRegion
    #|  use int.Int
    #|  use option.Option
    #|  use array.Array
    #|  let choose (empty : bool) : option (array int) =
    #|    if empty then None else Some (Array.make 1 0)
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"contextual-variant-region.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("contextual variant region failed: \{diagnostic.message}")
    @mlw.MlwError(diagnostic) =>
      fail("contextual variant region failed: \{diagnostic.message}")
    _ => fail("contextual variant region raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"choose"], None))
}

///|
test "clones preserve inferred regions across variant constructors" {
  let source =
    #|module InferredRegionCloneSource
    #|  use option.Option
    #|  use array.Array
    #|  type coeff
    #|  let wrap (seed : coeff) : option (array coeff) =
    #|    let values = Array.make 1 seed in
    #|    Some values
    #|end
    #|
    #|module InferredRegionCloneTarget
    #|  use int.Int
    #|  clone export InferredRegionCloneSource with type coeff = int
    #|end
  let context = shared_program_context()
  let parsed = @parser.parse_mlw_file(
    @utf8.encode(source)[:],
    filename=b"clone-inferred-variant-region.mlw",
  )
  let elaborated = @why3_elab.elaborate_file(
    context,
    fresh_program_environment(context),
    parsed,
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("inferred-region clone failed: \{diagnostic.message}")
    @mlw.MlwError(diagnostic) =>
      fail("inferred-region clone failed: \{diagnostic.message}")
    _ => fail("inferred-region clone raised another error")
  }
  assert_eq(elaborated.units().length(), 2)
}

///|
test "instantiated old snapshots follow inferred mutable arguments" {
  let source =
    #|module InferredOldSnapshot
    #|  use int.Int
    #|  use stack.Stack
    #|  let exercise () raises { Empty } =
    #|    let stack = create () in
    #|    push 1 stack
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"inferred-old-snapshot.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("inferred old snapshot failed: \{diagnostic.message}")
    @mlw.MlwError(diagnostic) =>
      fail("inferred old snapshot failed: \{diagnostic.message}")
    _ => fail("inferred old snapshot raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"exercise"], None))
}

///|
test "routine arguments are ordered by partial type dependencies" {
  let source =
    #|module PartialArgumentDependency
    #|  use set.Set
    #|  type item
    #|  let ghost function seconds (source : set (item, item)) : set item =
    #|    map
    #|      (fun pair -> let (_, right) = pair in right)
    #|      (filter source (fun _ -> true))
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"partial-argument-dependency.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("partial argument dependency failed: \{diagnostic.message}")
    _ => fail("partial argument dependency raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"seconds"], None))
}

///|
test "later concrete arguments constrain earlier nested polymorphic calls" {
  let source =
    #|module NestedArgumentConstraint
    #|  use option.Option
    #|  use seq.Seq
    #|  type split 'a = {
    #|    left : seq 'a;
    #|    middle : option 'a;
    #|    right : seq 'a;
    #|  }
    #|  let ghost function option_to_seq (value : option 'a) : seq 'a =
    #|    match value with
    #|    | Some item -> singleton item
    #|    | None -> empty
    #|    end
    #|  let ghost function rebuild (value : split 'a) : seq 'a =
    #|    value.left ++ option_to_seq value.middle ++ value.right
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"nested-argument-constraint.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("nested argument constraint failed: \{diagnostic.message}")
    _ => fail("nested argument constraint raised another error")
  }
  let rebuild = pmodule.export_namespace().find_routine([b"rebuild"], None)
  guard rebuild.view().logic is RLls(logic) else {
    fail("rebuild did not retain its logic symbol")
  }
  let mut definition_seen = false
  for declaration in program_declarations(pmodule) {
    if declaration is PDlet(symbol, _, pure, _) && symbol == rebuild {
      for logic_declaration in pure {
        if logic_declaration.view() is Dlogic([definition]) &&
          definition.view().symbol == logic {
          definition_seen = true
          assert_false(
            definition.view().body
            .free_type_variables()
            .any(variable => {
              variable
              .origin()
              .attributes()
              .any(attribute => attribute == b"mlw:inference_type_variable")
            }),
          )
        }
      }
    }
  }
  assert_true(definition_seen)
}

///|
test "loop invariants retain earlier inferred array bindings" {
  let source =
    #|module InferredArrayInvariantBinding
    #|  use int.Int
    #|  use array.Array
    #|  let initialize (n : int) : unit =
    #|    let values = begin
    #|      ensures { result.length = n }
    #|      make n false
    #|    end in
    #|    for i = 1 to n - 1 do
    #|      invariant { forall j. 1 <= j < i -> not values[j] }
    #|      values[i] <- false
    #|    done
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"inferred-array-invariant-binding.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("inferred array invariant binding failed: \{diagnostic.message}")
    _ => fail("inferred array invariant binding raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"initialize"], None))
}

///|
test "program type clones freshen target-only shareable regions" {
  let source =
    #|module RegionlessSpec
    #|  type t = private { mutable value : int }
    #|end
    #|
    #|module RegionfulImplementation
    #|  use ref.Ref
    #|  type t = { mutable value : int; backing : ref int }
    #|  clone RegionlessSpec with type t = t
    #|end
  let context = @identity.CompilationContext::new()
  let parsed = @parser.parse_mlw_file(
    @utf8.encode(source)[:],
    filename=b"program-clone-fresh-regions.mlw",
  )
  let elaborated = @why3_elab.elaborate_file(
    context,
    isolated_program_environment(context),
    parsed,
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("program clone region freshening failed: \{diagnostic.message}")
    _ => fail("program clone region freshening raised another error")
  }
  guard elaborated.units()
    is [
      @why3_elab.ElaboratedModule(_),
      @why3_elab.ElaboratedModule(implementation),
    ] else {
    fail("program clone region fixture did not elaborate two modules")
  }
  let target = implementation.export_namespace().find_type([b"t"], None)
  assert_eq(target.view().regions.length(), 1)
}

///|
test "program clones preserve imported mutable field identities" {
  let source =
    #|module ReferenceCloneSource
    #|  use ref.Ref
    #|  type item
    #|  val constant zero : item
    #|  let overwrite () : item =
    #|    let ref cell = zero in
    #|    cell <- zero;
    #|    cell
    #|end
    #|
    #|module ReferenceCloneTarget
    #|  use int.Int
    #|  let constant zero : int = 0
    #|  clone ReferenceCloneSource with
    #|    type item = int,
    #|    val zero = zero
    #|end
  let context = @identity.CompilationContext::new()
  let parsed = @parser.parse_mlw_file(
    @utf8.encode(source)[:],
    filename=b"program-clone-imported-field.mlw",
  )
  let elaborated = @why3_elab.elaborate_file(
    context,
    isolated_program_environment(context),
    parsed,
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("program clone imported field failed: \{diagnostic.message}")
    @mlw.MlwError(diagnostic) =>
      fail("program clone imported field failed: \{diagnostic.message}")
    _ => fail("program clone imported field raised another error")
  }
  guard elaborated.units()
    is [@why3_elab.ElaboratedModule(_), @why3_elab.ElaboratedModule(target)] else {
    fail("program clone imported-field fixture did not elaborate two modules")
  }
  assert_eq(target.key().view().name, b"ReferenceCloneTarget")
}

///|
test "clone export omits explicitly substituted symbols from its namespace" {
  let source =
    #|module CloneExportSource
    #|  use int.Int
    #|  use array.Array
    #|  type item
    #|  val constant blank : item
    #|  val (=) (left right : item) : bool
    #|    ensures { result <-> left = right }
    #|  let first (values : array item) : bool =
    #|    length values > 0 && values[0] = blank
    #|end
    #|
    #|module CloneExportTarget
    #|  use int.Int
    #|  use string.Char
    #|  use string.OCaml
    #|  use array.Array
    #|  let constant blank : char = chr 32
    #|  clone export CloneExportSource with
    #|    type item = char,
    #|    val blank = blank,
    #|    val (=) = eq_char
    #|end
  let context = @identity.CompilationContext::new()
  let elaborated = @why3_elab.elaborate_file(
    context,
    isolated_program_environment(context),
    @parser.parse_mlw_file(
      @utf8.encode(source)[:],
      filename=b"clone-export-explicit-namespace.mlw",
    ),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("clone export namespace filtering failed: \{diagnostic.message}")
    _ => fail("clone export namespace filtering raised another error")
  }
  guard elaborated.units()
    is [@why3_elab.ElaboratedModule(_), @why3_elab.ElaboratedModule(target)] else {
    fail("clone export namespace fixture did not elaborate two modules")
  }
  ignore(target.export_namespace().find_routine([b"first"], None))
}

///|
test "record type clone refinements reuse target field projections" {
  let source =
    #|module RecordRefinementSource
    #|  type cell = private {
    #|    mutable ghost contents : int;
    #|    tag : int;
    #|  }
    #|end
    #|
    #|module RecordRefinementTarget
    #|  type cell = {
    #|    tag : int;
    #|    mutable contents : int;
    #|    extra : int;
    #|  }
    #|  clone export RecordRefinementSource with type cell = cell
    #|end
  let context = @identity.CompilationContext::new()
  let elaborated = @why3_elab.elaborate_file(
    context,
    isolated_program_environment(context),
    @parser.parse_mlw_file(
      @utf8.encode(source)[:],
      filename=b"record-clone-refinement.mlw",
    ),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("record clone refinement failed: \{diagnostic.message}")
    @mlw.MlwError(diagnostic) =>
      fail("record clone refinement failed: \{diagnostic.message}")
    @logic.TypeError(diagnostic) =>
      fail("record clone refinement failed: \{diagnostic.message}")
    _ => fail("record clone refinement raised another error")
  }
  guard elaborated.units()
    is [@why3_elab.ElaboratedModule(_), @why3_elab.ElaboratedModule(target)] else {
    fail("record clone refinement fixture did not elaborate two modules")
  }
  let program_space = target.export_namespace()
  let symbol = program_space.find_type([b"cell"], None)
  let contents = symbol.view().mutable_fields[0]
  let projection = program_space.find_routine([b"contents"], None)
  assert_true(projection.view().field is Some(field) && field == contents)
}

///|
test "polymorphic record constructors instantiate field specifications" {
  let source =
    #|module PolymorphicRecordConstructor
    #|  use seq.Seq
    #|  type cursor 'a = {
    #|    visited : seq 'a;
    #|    collection : seq 'a;
    #|    index : int;
    #|  }
    #|  let create (items : seq 'a) : cursor 'a =
    #|    { visited = empty; collection = items; index = 0 }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"polymorphic-record-constructor.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("polymorphic record construction failed: \{diagnostic.message}")
    _ => fail("polymorphic record construction raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"create"], None))
}

///|
test "record fields constrain omitted routine parameter types before generalization" {
  let source =
    #|module InferredRecordParameters
    #|  use int.Int
    #|  type t 'a = { f1 : 'a; f2 : int }
    #|  let make value count = { f1 = value; f2 = count }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"inferred-record-parameters.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("record parameter inference failed: \{diagnostic.message}")
    _ => fail("record parameter inference raised another error")
  }
  let make = pmodule.export_namespace().find_routine([b"make"], None)
  let view = make.view().cty.view()
  guard view.arguments is [value, count] &&
    view.result.view() is ItyApp(_, [element], _) else {
    fail("inferred record routine lost its polymorphic shape")
  }
  assert_true(value.view().ity == element)
  assert_true(
    count.view().ity.to_ty(None) ==
    @logic.Ty::app(
      pmodule.pure_theory().export_namespace().find_type([b"int"], None),
      [],
      None,
    ),
  )
}

///|
test "local recursive routines shadow imported pure and program names" {
  let source =
    #|module ImportedSubstring
    #|  use int.Int
    #|  type text
    #|  function sub text int int : text
    #|  val sub (value : text) (offset count : int) : text
    #|    ensures { result = sub value offset count }
    #|end
    #|
    #|module RecursiveSubstring
    #|  use int.Int
    #|  use import ImportedSubstring as S
    #|  type rope = Leaf | Node rope
    #|  let rec sub (value : rope) (offset count : int) : rope
    #|    requires { 0 <= count }
    #|    variant { count }
    #|  = match value with
    #|    | Leaf -> value
    #|    | Node child ->
    #|        let remaining = count - 1 in
    #|        if remaining <= 0 then sub child offset remaining else value
    #|    end
    #|end
  let context = @identity.CompilationContext::new()
  let elaborated = @why3_elab.elaborate_file(
    context,
    isolated_program_environment(context),
    @parser.parse_mlw_file(
      @utf8.encode(source)[:],
      filename=b"recursive-program-shadowing.mlw",
    ),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("recursive program shadowing failed: \{diagnostic.message}")
    _ => fail("recursive program shadowing raised another error")
  }
  guard elaborated.units()
    is [@why3_elab.ElaboratedModule(_), @why3_elab.ElaboratedModule(recursive)] else {
    fail("recursive shadowing fixture did not elaborate two modules")
  }
  ignore(recursive.export_namespace().find_routine([b"sub"], None))
}

///|
test "recursive predicates prefer parameters over same-named globals" {
  let source =
    #|module RecursivePredicateShadow
    #|  use int.Int
    #|  type loc
    #|  val (=) (left right : loc) : bool
    #|    ensures { result <-> left = right }
    #|  val heap : loc
    #|  val unused : loc
    #|  let rec predicate path
    #|    (heap : loc) (current : loc) (last : loc) (steps : int)
    #|    variant { steps }
    #|  = if steps = 0 then current = last && heap = heap
    #|    else path heap current last (steps - 1)
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"recursive-predicate-shadow.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("recursive predicate shadowing failed: \{diagnostic.message}")
    _ => fail("recursive predicate shadowing raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"path"], None))
}

///|
test "local recursive logic symbols do not escape enclosing definitions" {
  let source =
    #|module LocalRecursiveLogic
    #|  use int.Int
    #|  let function greater (value : int) : int =
    #|    let rec function great (value : int) (remaining : int) : int
    #|      variant { remaining }
    #|    = if remaining = 0 then value
    #|      else great value (remaining - 1)
    #|    in
    #|    great value 1
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"local-recursive-logic.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("local recursive logic escaped: \{diagnostic.message}")
    _ => fail("local recursive logic fixture raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"greater"], None))
}

///|
test "pure projections can shadow incompatible program projections" {
  let source =
    #|module PureProjectionShadow
    #|  use fmap.Fmap
    #|  type loc
    #|  let read (memory : fmap loc loc) (root : loc) : loc =
    #|    memory.contents root
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"pure-projection-shadow.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("pure projection shadowing failed: \{diagnostic.message}")
    _ => fail("pure projection shadowing raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"read"], None))
}

///|
test "program clones reuse canonical translated type invariants" {
  let source =
    #|module InvariantSource
    #|  use int.Int
    #|  type cell = { value : int }
    #|    invariant { value >= 0 }
    #|    by { value = 0 }
    #|end
    #|
    #|module InvariantClone
    #|  clone export InvariantSource
    #|end
  let context = @identity.CompilationContext::new()
  let parsed = @parser.parse_mlw_file(
    @utf8.encode(source)[:],
    filename=b"program-clone-invariant.mlw",
  )
  let elaborated = @why3_elab.elaborate_file(
    context,
    isolated_program_environment(context),
    parsed,
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("program invariant clone failed: \{diagnostic.message}")
    _ => fail("program invariant clone raised another error")
  }
  guard elaborated.units()
    is [@why3_elab.ElaboratedModule(_), @why3_elab.ElaboratedModule(cloned)] else {
    fail("program clone fixture did not elaborate two modules")
  }
  let cell = cloned.export_namespace().find_type([b"cell"], None)
  assert_eq(cell.view().invariants.length(), 1)
}

///|
test "cloned constructors use substituted argument types through aliases" {
  let source =
    #|module ConstructorCloneSource
    #|  type coeff
    #|  type expr =
    #|    | Sum expr expr
    #|    | Prod expr cprod
    #|    | Coeff coeff
    #|  with cprod = C coeff | Times cprod cprod
    #|end
    #|
    #|module ConstructorCoefficientLibrary
    #|  use int.Int
    #|  type t = (int, int)
    #|end
    #|
    #|module ConstructorCloneTarget
    #|  use ConstructorCoefficientLibrary
    #|  type coeff = t
    #|  clone export ConstructorCloneSource with type coeff = t
    #|end
    #|
    #|module ConstructorCloneClient
    #|  use ConstructorCloneTarget as R
    #|  let make (value : R.coeff) : R.expr = R.Coeff value
    #|end
  let context = @identity.CompilationContext::new()
  let parsed = @parser.parse_mlw_file(
    @utf8.encode(source)[:],
    filename=b"program-clone-constructor-alias.mlw",
  )
  let elaborated = @why3_elab.elaborate_file(
    context,
    isolated_program_environment(context),
    parsed,
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("cloned constructor typing failed: \{diagnostic.message}")
    _ => fail("cloned constructor typing raised another error")
  }
  guard elaborated.units()
    is [
      @why3_elab.ElaboratedModule(_),
      @why3_elab.ElaboratedModule(_),
      @why3_elab.ElaboratedModule(target),
      @why3_elab.ElaboratedModule(client),
    ] else {
    fail("cloned constructor fixture did not elaborate four modules")
  }
  let coeff = target.export_namespace().find_type([b"coeff"], None)
  let expanded_coeff = @mlw.Ity::instantiate(coeff, [], [], None)
  let constructor_routine = target
    .export_namespace()
    .find_routine([b"Coeff"], None)
  assert_true(
    constructor_routine.view().cty.view().arguments is [argument] &&
    argument.view().ity == expanded_coeff,
  )
  let declarations = program_declarations(client)
  guard !declarations.is_empty() &&
    declarations[declarations.length() - 1]
    is PDlet(make, Cfun(_, Some(body)), _, _) else {
    fail("cloned constructor client did not retain its routine")
  }
  assert_false(make.is_ghost())
  guard terminal_program_expression(body).view() is Eexec(computation, _) &&
    computation.view() is Capp(called, [_]) else {
    fail("qualified cloned constructor fell back to a pure application")
  }
  assert_true(called == constructor_routine)
}

///|
test "field sugar is not shadowed by a same-named specification local" {
  let source =
    #|module FieldSugar
    #|  use int.Int
    #|  type item = { value : int }
    #|  let make (value : int) : item
    #|    ensures { result.value = value }
    #|  = { value = value }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"field-sugar-shadowing.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail(
        "field sugar was shadowed by its same-named local: \{diagnostic.message}",
      )
    _ => fail("field sugar shadowing fixture raised another error")
  }
  assert_eq(program_declarations(pmodule).length(), 2)
}

///|
test "ghost routines implicitly ghostify all formal parameters" {
  let source =
    #|module GhostRoutineParameters
    #|  use int.Int
    #|  use ref.Ref
    #|  type cell = abstract { mutable value : int }
    #|  val ghost clear (item : cell) : unit
    #|    writes { item }
    #|  let lemma local_state () : unit =
    #|    let cursor = ref 0 in
    #|    while !cursor < 1 do
    #|      invariant { 0 <= !cursor <= 1 }
    #|      variant { 1 - !cursor }
    #|      cursor := !cursor + 1
    #|    done
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"ghost-routine-parameters.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("ghost routine parameter typing failed: \{diagnostic.message}")
    _ => fail("ghost routine parameter fixture raised another error")
  }
  let clear = pmodule.export_namespace().find_routine([b"clear"], None)
  assert_true(clear.is_ghost())
  assert_true(clear.view().cty.view().arguments[0].view().ghost)
  let declarations = program_declarations(pmodule)
  guard declarations[declarations.length() - 1]
    is PDlet(local_state, Cfun(_, Some(body)), _, _) &&
    body.view() is Elet(definition, _) &&
    definition.view() is LDvar(cursor, _) else {
    fail("ghost routine did not retain its local reference")
  }
  assert_true(local_state.is_ghost())
  assert_true(cursor.view().ghost)
}

///|
test "ghost value bindings do not ghostify effectful initializers" {
  let source =
    #|module GhostValueBinding
    #|  type cell = { mutable contents : int }
    #|  val update (target : cell) : int
    #|    writes { target.contents }
    #|  let run (target : cell) : unit =
    #|    let ghost result = update target in
    #|    assert { result = result }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"ghost-value-binding.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("ghost value binding typing failed: \{diagnostic.message}")
    _ => fail("ghost value binding fixture raised another error")
  }
  let declarations = program_declarations(pmodule)
  guard declarations.length() == 3 &&
    declarations[2] is PDlet(_, Cfun(_, Some(body)), _, _) &&
    body.view() is Elet(definition, _) &&
    definition.view() is LDvar(result, initializer) else {
    fail("effectful ghost value binding was not retained")
  }
  assert_true(result.view().ghost)
  assert_false(initializer.effect().view().ghost)
  assert_false(initializer.effect().view().writes.is_empty())
}

///|
test "sequence discard binders inherit ghost initializer masks" {
  let source =
    #|module GhostSequenceBinder
    #|  use ref.Ref
    #|  let run (ghost target : ref int) : unit =
    #|    target := 1;
    #|    ()
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"ghost-sequence-binder.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("ghost sequence binder typing failed: \{diagnostic.message}")
    _ => fail("ghost sequence binder fixture raised another error")
  }
  let declarations = program_declarations(pmodule)
  guard declarations[declarations.length() - 1]
    is PDlet(_, Cfun(_, Some(body)), _, _) &&
    body.view() is Elet(definition, _) &&
    definition.view() is LDvar(discard, initializer) else {
    fail("ghost sequence was not retained as a let binding")
  }
  assert_true(initializer.mask().is_ghost())
  assert_true(discard.view().ghost)
}

///|
test "sequence discard binders inherit the enclosing ghost context" {
  let source =
    #|module GhostSequenceContext
    #|  use int.Int
    #|  let lemma verify (value : int) : unit =
    #|    assert { value = value };
    #|    assert { value = value }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"ghost-sequence-context.mlw"),
  )
  let declarations = program_declarations(pmodule)
  guard declarations[declarations.length() - 1]
    is PDlet(_, Cfun(_, Some(body)), _, _) &&
    body.view() is Elet(definition, _) &&
    definition.view() is LDvar(discard, initializer) else {
    fail("ghost-context sequence was not retained as a let binding")
  }
  assert_true(initializer.view() is Eassert(_, _))
  assert_false(initializer.mask().is_ghost())
  assert_true(discard.view().ghost)
}

///|
test "for-loop bound proxies do not inherit the enclosing ghost context" {
  let source =
    #|module GhostLoopBoundProxies
    #|  let lemma iterate () : unit =
    #|    for index = 0 to 1 do
    #|      ()
    #|    done
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"ghost-loop-bound-proxies.mlw"),
  )
  let declarations = program_declarations(pmodule)
  guard declarations[declarations.length() - 1]
    is PDlet(_, Cfun(_, Some(body)), _, _) &&
    body.view() is Elet(first_definition, rest) &&
    first_definition.view() is LDvar(first_bound, _) &&
    rest.view() is Elet(last_definition, loop_expression) &&
    last_definition.view() is LDvar(last_bound, _) &&
    loop_expression.view() is Efor(_, _, _, _, _) else {
    fail("for-loop bounds were not retained as proxy bindings")
  }
  assert_false(first_bound.view().ghost)
  assert_false(last_bound.view().ghost)
}

///|
test "temporary arguments inherit a formal parameter's ghost status" {
  let source =
    #|module GhostArgumentProxy
    #|  use ref.Ref
    #|  val consume (ghost item : ref int) : unit
    #|    writes { item }
    #|  let call () : unit =
    #|    consume (ref 0)
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"ghost-argument-proxy.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("ghost argument proxy typing failed: \{diagnostic.message}")
    _ => fail("ghost argument proxy fixture raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"call"], None))
}

///|
test "anonymous top-level declarations elaborate as the synthetic Top module" {
  let source =
    #|use int.Int
    #|let answer () : int = 42
  let context = @identity.CompilationContext::new()
  let parsed = @parser.parse_mlw_file(
    @utf8.encode(source)[:],
    filename=b"anonymous-top-level.mlw",
  )
  assert_true(parsed is Decls(_))
  let elaborated = @why3_elab.elaborate_file(
    context,
    isolated_program_environment(context),
    parsed,
  )
  guard elaborated.units() is [@why3_elab.ElaboratedModule(pmodule)] else {
    fail("anonymous declarations did not elaborate as a module")
  }
  assert_eq(pmodule.key().view().name, b"Top")
  assert_eq(
    pmodule.export_namespace().find_routine([b"answer"], None).view().name,
    b"answer",
  )
}

///|
test "top-level program variables are visible in routine old and at terms" {
  let source =
    #|module OldAt
    #|  use int.Int
    #|  use ref.Ref
    #|  val cell : ref int
    #|  let preserve () : unit
    #|    ensures { !cell = old !cell }
    #|  = label Before in
    #|    assert { !cell = !cell at Before }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"program-old-at.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("top-level old/at elaboration failed")
    }
    _ => fail("top-level old/at raised another error")
  }
  guard program_declarations(pmodule)
    is [PDvar(cell, _, _, _), PDlet(_, Cfun(cty, Some(_)), _, _)] else {
    fail("top-level variable and routine declarations were not preserved")
  }
  assert_eq(cty.view().oldies.length(), 1)
  assert_true(cty.view().oldies[0].view().original == cell)
}

///|
test "top-level val-ref declarations retain their implicit-read marker" {
  let source =
    #|module GlobalReferenceMarker
    #|  use int.Int
    #|  val ghost ref clock : int
    #|  val ghost tick () : unit
    #|    writes { clock }
    #|    ensures { clock = old clock + 1 }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"global-reference-marker.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("global reference marker typing failed: \{diagnostic.message}")
    _ => fail("global reference marker typing raised another error")
  }
  let clock = pmodule.export_namespace().find_variable([b"clock"], None)
  assert_true(
    clock.view().name.view().attributes.any(attribute => {
      attribute == b"mlw:reference_var"
    }),
  )
  guard program_declarations(pmodule)[0] is PDvar(_, initializer, _, _) else {
    fail("top-level ghost reference lost its abstract initializer")
  }
  assert_false(initializer.mask().is_ghost())
  assert_false(initializer.effect().view().ghost)
  guard program_declarations(pmodule)[1] is PDlet(_, Cany(tick), _, _) &&
    tick.view().oldies is [old_clock] else {
    fail("top-level ghost reference did not produce an old-value snapshot")
  }
  assert_true(
    old_clock.view().snapshot.view().name.view().attributes.any(attribute => {
      attribute == b"mlw:reference_var"
    }),
  )
}

///|
test "declared values specialize polymorphic contracted constructor bodies" {
  let source =
    #|module ConstructorResult
    #|  use list.List
    #|  let empty : list int = Nil
    #|    ensures { result = Nil }
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"constructor-result.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("constructor result typing failed: \{diagnostic.message}")
    _ => fail("constructor result typing raised another error")
  }
  guard program_declarations(pmodule) is [PDvar(variable, value, _, _)] &&
    value.view() is Eexec(_, cty) else {
    fail("expected one concrete contracted constructor value")
  }
  assert_true(variable.view().ity == value.ity())
  assert_eq(cty.view().postconditions.length(), 1)
  assert_true(
    value.ity().view() is ItyApp(list, [argument], _) &&
    list.view().logic_type.name() == b"list" &&
    argument.view() is ItyApp(integer, [], _) &&
    integer.view().logic_type.name() == b"int",
  )
}

///|
test "loop invariants specialize polymorphic local initializers" {
  let source =
    #|module InvariantInitializer
    #|  use int.Int
    #|  use import seq.Seq as S
    #|  use queue.Queue
    #|  use ref.Ref
    #|  use option.Option
    #|  type item = { payload : int }
    #|  predicate valid (items : seq item) =
    #|    forall index. 0 <= index < length items ->
    #|      items[index].payload >= 0
    #|  let run () : unit =
    #|    let ghost items = Queue.create () in
    #|    let ghost active = ref None in
    #|    while false do
    #|      invariant { valid items }
    #|      invariant { !active = (None : option item) }
    #|      ()
    #|    done
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"invariant-initializer.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("invariant initializer typing failed: \{diagnostic.message}")
    _ => fail("invariant initializer typing raised another error")
  }
  let declarations = program_declarations(pmodule)
  guard !declarations.is_empty() &&
    declarations[declarations.length() - 1]
    is PDlet(_, Cfun(_, Some(body)), _, _) &&
    body.view() is Elet(queue_definition, nested) &&
    queue_definition.view() is LDvar(items, _) &&
    nested.view() is Elet(reference_definition, _) &&
    reference_definition.view() is LDvar(active, _) else {
    fail("expected one routine with contextual local initializers")
  }
  assert_true(
    items.view().ity.view() is ItyReg(region) &&
    region.view().symbol.view().logic_type.name() == b"t" &&
    region.view().arguments is [element] &&
    element.view() is ItyApp(item, [], _) &&
    item.view().logic_type.name() == b"item",
  )
  assert_true(
    active.view().ity.view() is ItyReg(reference) &&
    reference.view().symbol.view().logic_type.name() == b"ref" &&
    reference.view().arguments is [content] &&
    content.view() is ItyApp(option, [element], _) &&
    option.view().logic_type.name() == b"option" &&
    element.view() is ItyApp(item, [], _) &&
    item.view().logic_type.name() == b"item",
  )
}

///|
test "nested block contracts inherit surrounding program-state labels" {
  let source =
    #|module NestedLabelContract
    #|  use ref.Ref
    #|  let preserve (cell : ref int) : unit =
    #|    label Before in
    #|    begin
    #|      ensures { !cell = !cell at Before }
    #|      cell := !cell
    #|    end
    #|  let local_old (cell : ref int) : unit =
    #|    let rec walk () : unit
    #|      requires { !cell = old !cell }
    #|    = ()
    #|    in walk ()
    #|end
  let context = shared_program_context()
  let pmodule = @why3_elab.elaborate_program_unit(
    context,
    fresh_program_environment(context),
    parsed_program_unit(source, b"nested-label-contract.mlw"),
  ) catch {
    @why3_elab.ElabError(diagnostic) =>
      fail("nested labeled contract failed: \{diagnostic.message}")
    _ => fail("nested labeled contract raised another error")
  }
  ignore(pmodule.export_namespace().find_routine([b"preserve"], None))
  ignore(pmodule.export_namespace().find_routine([b"local_old"], None))
}
