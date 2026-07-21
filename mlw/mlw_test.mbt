// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn snapshot_origin(
  name : BytesView,
  kind : @identity.SnapshotSymbolKind,
  item : UInt,
) -> @identity.Origin {
  @identity.Origin::snapshot(
    name,
    @identity.SnapshotSymbolKey::new(
      b"int.Int",
      item,
      0U,
      kind,
      Bytes::make(32, b'\x11'),
    ),
    [],
  )
}

///|
fn empty_program_flags() -> @mlw.ProgramTypeFlags {
  {
    nonfree: false,
    private_: false,
    mutable_: false,
    fragile: false,
    argument_flags: [],
    region_flags: [],
  }
}

///|
fn integer_program_type(
  context : @identity.CompilationContext,
) -> (@logic.TypeSymbol, @mlw.ProgramTypeSymbol, @mlw.Ity) raise {
  let logic_type = @logic.TypeSymbol::trusted_builtin(
    context,
    b"int",
    snapshot_origin(b"int", Type, 0U),
    BuiltinInteger,
    None,
  )
  let program_type = @mlw.ProgramTypeSymbol::trusted_new(
    context,
    logic_type,
    snapshot_origin(b"int", Program, 1U),
    empty_program_flags(),
    ProgramNoDef,
    [],
    [],
    None,
  )
  (logic_type, program_type, @mlw.Ity::app(program_type, [], None))
}

///|
test "snapshot routine preserves Cty and RLls identity" {
  let context = @identity.CompilationContext::new()
  let (logic_type, program_type, integer) = integer_program_type(context)
  let x = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"x", [], None),
    integer,
    false,
    None,
  )
  let pure_integer = @logic.Ty::app(logic_type, [], None)
  let logic_add = @logic.LSymbol::new_function(
    context,
    b"infix +",
    snapshot_origin(b"infix +", Logic, 2U),
    [pure_integer, pure_integer],
    pure_integer,
    None,
  )
  let result = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", None, []),
    pure_integer,
    None,
  )
  let cty = @mlw.Cty::trusted_new(
    program_type.semantic_id(),
    [x],
    [x],
    [@logic.Term::true_formula()],
    [@mlw.Postcondition::trusted_new(result, @logic.Term::true_formula(), None)],
    @mlw.Effect::pure(false),
    integer,
    Visible,
    None,
  )
  let routine = @mlw.RoutineSymbol::trusted_new(
    context,
    b"infix +",
    snapshot_origin(b"infix +", Program, 3U),
    cty,
    RLls(logic_add),
    None,
    None,
  )
  let program_space = @mlw.ProgramNamespace::empty()
    .add_type(b"int", program_type, None)
    .add_routine(b"infix +", routine, None)
  assert_true(program_space.find_type([b"int"], None) == program_type)
  assert_true(program_space.find_routine([b"infix +"], None) == routine)
  let view = routine.view()
  assert_true(view.logic is RLls(symbol) && symbol == logic_add)
  assert_eq(view.cty.view().arguments.length(), 1)
  assert_eq(view.cty.view().postconditions.length(), 1)
}

///|
test "program symbol construction requires snapshot origin" {
  let context = @identity.CompilationContext::new()
  let (logic_type, _, _) = integer_program_type(context)
  try
    @mlw.ProgramTypeSymbol::trusted_new(
      context,
      logic_type,
      @identity.Origin::user(b"bad", None, []),
      empty_program_flags(),
      ProgramNoDef,
      [],
      [],
      None,
    )
  catch {
    MlwError(diagnostic) =>
      assert_eq(diagnostic.kind, SnapshotProgramOriginRequired)
  } noraise {
    _ => fail("expected snapshot origin rejection")
  }
}
