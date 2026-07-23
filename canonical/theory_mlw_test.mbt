// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn canonical_test_name(name : BytesView) -> @theory.SemanticName {
  @theory.SemanticName::new(name, [], None)
}

///|
fn canonical_test_origin(name : BytesView) -> @identity.Origin {
  @identity.Origin::user(name, None, [])
}

///|
test "empty Theory and Pmodule canonical vectors are byte exact" {
  let context = @identity.CompilationContext::new()
  let key = @theory.TheoryKey::new([b"demo"], b"Empty")
  let theory = @theory.TheoryBuilder::new(
    context,
    key,
    canonical_test_name(b"Empty"),
  ).close()
  let expected_theory = b"[\"Theory\",[\"TheoryKey\",[\"64656d6f\"],\"456d707479\"],[\"Origin.User\",\"456d707479\",[\"none\"],[]],[],[\"Namespace\",[],[],[],[]]]\n"
  assert_eq(@canonical.encode_theory(theory).bytes(), expected_theory)
  let pmodule = @mlw.PmoduleBuilder::new(
    context,
    key,
    canonical_test_name(b"Empty"),
  ).close()
  assert_eq(
    @canonical.encode_pmodule(pmodule).bytes(),
    b"[\"Pmodule\",[\"PmoduleKey\",[\"64656d6f\"],\"456d707479\"]," +
    expected_theory[0:expected_theory.length() - 1].to_owned() +
    b",[],[\"ProgramNamespace\",[],[],[],[]]]\n",
  )
}

///|
test "Task item and goal-last canonical vector is byte exact" {
  let context = @identity.CompilationContext::new()
  let origin = canonical_test_origin(b"g")
  let declaration = @logic.Decl::proposition(
    context,
    origin,
    Pgoal,
    @logic.PrSymbol::new(context, b"g", origin),
    @logic.Term::true_formula(),
    None,
  )
  let task = @theory.Task::trusted_new(
    context.fresh_id(),
    [TheoryDecl(declaration)],
    None,
  )
  let origin_bytes = b"[\"Origin.User\",\"67\",[\"none\"],[]]"
  assert_eq(
    @canonical.encode_task(task).bytes(),
    b"[\"Task\",[[\"TaskItem.Decl\",[\"Decl\"," +
    origin_bytes +
    b",[],[\"Dprop.Pgoal\",[\"PrSymbol\",[\"proposition\",0],\"67\"," +
    origin_bytes +
    b"],[\"Ttrue\"]]]]]]\n",
  )
}

///|
fn canonical_program_origin() -> @identity.Origin {
  @identity.Origin::snapshot(
    b"int",
    @identity.SnapshotSymbolKey::new(
      b"demo.Int",
      1U,
      0U,
      Program,
      Bytes::make(32, b'\x00'),
    ),
    [],
  )
}

///|
fn canonical_program_type(
  context : @identity.CompilationContext,
) -> @mlw.ProgramTypeSymbol raise {
  let logic_type = @logic.TypeSymbol::trusted_builtin(
    context,
    b"int",
    @identity.Origin::snapshot(
      b"int",
      @identity.SnapshotSymbolKey::new(
        b"demo.Int",
        0U,
        0U,
        Type,
        Bytes::make(32, b'\x00'),
      ),
      [],
    ),
    BuiltinInteger,
    None,
  )
  @mlw.ProgramTypeSymbol::trusted_new(
    context,
    logic_type,
    canonical_program_origin(),
    {
      nonfree: false,
      private_: false,
      mutable_: false,
      fragile: false,
      argument_flags: [],
      region_flags: [],
    },
    ProgramNoDef,
    [],
    [],
    None,
  )
}

///|
test "minimal program type and Ity canonical vectors are byte exact" {
  let symbol = canonical_program_type(@identity.CompilationContext::new())
  let zero_digest = b"0000000000000000000000000000000000000000000000000000000000000000"
  let origin = b"[\"Origin.Snapshot\",\"696e74\",[\"SnapshotSymbolKey\",\"64656d6f2e496e74\",1,0,\"program\",\"" +
    zero_digest +
    b"\"],[]]"
  assert_eq(
    @canonical.encode_program_type_symbol(symbol).bytes(),
    b"[\"ProgramTypeSymbol\",[\"program\",0],[\"type\",0]," +
    origin +
    b",[false,false,false,false,[],[]],[\"TypeDefinition.NoDef\"]]\n",
  )
  assert_eq(
    @canonical.encode_ity(@mlw.Ity::app(symbol, [], None)).bytes(),
    b"[\"ItyApp\",[\"program\",0],[],[],[\"TyApp\",[\"type\",0],[]]]\n",
  )
}

///|
test "snapshot diagnostic locations stay outside semantic canonical bytes" {
  let key = @identity.SnapshotSymbolKey::new(
    b"demo.Int",
    0U,
    0U,
    Type,
    Bytes::make(32, b'\x01'),
  )
  let span = @identity.SourceSpan::new(b"demo.mlw", 1, 2, 1L, 1L, 1L, 2L)
  assert_eq(
    @canonical.encode_origin(@identity.Origin::snapshot(b"int", key, [])).bytes(),
    @canonical.encode_origin(
      @identity.Origin::snapshot_with_span(b"int", key, Some(span), []),
    ).bytes(),
  )
}
