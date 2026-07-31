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
test "v3 covers empty theories and modules" {
  let context = @identity.CompilationContext::new()
  let key = @theory.TheoryKey::new([b"demo"], b"Empty")
  let theory = @theory.TheoryBuilder::new(
    context,
    key,
    canonical_test_name(b"Empty"),
  ).close()
  let pmodule = @mlw.PmoduleBuilder::new(
    context,
    key,
    canonical_test_name(b"Empty"),
  ).close()
  assert_eq(@canonical.encode_theory(theory).bytes()[:10], b"[\"GraphV3\"")
  assert_eq(@canonical.encode_pmodule(pmodule).bytes()[:10], b"[\"GraphV3\"")
}

///|
test "v3 covers tasks" {
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
  assert_eq(@canonical.encode_task(task).bytes()[:10], b"[\"GraphV3\"")
}

///|
test "v3 task dependencies omit routine VCs but retain type VCs" {
  let context = @identity.CompilationContext::new()
  let dependency_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([b"demo"], b"Dependency"),
    canonical_test_name(b"Dependency"),
  )
  let routine_name = b"routine'vc"
  let routine_origin = @identity.Origin::user(
    routine_name,
    None,
    [b"expl:VC for routine"],
  )
  dependency_builder.add_decl(
    @logic.Decl::proposition(
      context,
      routine_origin,
      Pgoal,
      @logic.PrSymbol::new(
        context,
        routine_name,
        routine_origin,
      ),
      @logic.Term::true_formula(),
      None,
    ),
    None,
  )
  let generated_name = b"dependency'vc"
  let generated_origin = @identity.Origin::user(
    generated_name,
    None,
    [b"expl:VC for dependency"],
  )
  dependency_builder.add_decl(
    @logic.Decl::proposition(
      context,
      generated_origin,
      Pgoal,
      @logic.PrSymbol::new(
        context,
        generated_name,
        generated_origin,
      ),
      @logic.Term::true_formula(),
      None,
    ),
    None,
  )
  let dependency_type = @logic.TypeSymbol::new_abstract(
    context,
    b"dependency",
    canonical_test_origin(b"dependency"),
    [],
    None,
  )
  dependency_builder.add_decl(
    @logic.Decl::type_declaration(
      context,
      canonical_test_origin(b"dependency"),
      [dependency_type],
      None,
    ),
    None,
  )
  let task_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([b"demo"], b"Task"),
    canonical_test_name(b"Task"),
  )
  task_builder.add_use(dependency_builder.close(), false, None)
  let goal_origin = canonical_test_origin(b"goal")
  task_builder.add_decl(
    @logic.Decl::proposition(
      context,
      goal_origin,
      Pgoal,
      @logic.PrSymbol::new(context, b"goal", goal_origin),
      @logic.Term::true_formula(),
      None,
    ),
    None,
  )
  guard @theory.split_theory(context, task_builder.close(), None) is [task] else {
    fail("expected one task")
  }
  let encoded = @canonical.encode_task(task).bytes()
  assert_true(encoded.find(b"726f7574696e65277663") is None)
  assert_true(encoded.find(b"646570656e64656e6379277663") is Some(_))
}

///|
test "v3 covers program types and itys" {
  let context = @identity.CompilationContext::new()
  let logic_type = @logic.TypeSymbol::new_builtin(
    context,
    b"int",
    canonical_test_origin(b"int"),
    BuiltinInteger,
  )
  let symbol = @mlw.ProgramTypeSymbol::new(
    context,
    logic_type,
    canonical_test_origin(b"int"),
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
  assert_eq(
    @canonical.encode_program_type_symbol(symbol).bytes()[:10],
    b"[\"GraphV3\"",
  )
  assert_eq(
    @canonical.encode_ity(@mlw.Ity::app(symbol, [], None)).bytes()[:10],
    b"[\"GraphV3\"",
  )
}
