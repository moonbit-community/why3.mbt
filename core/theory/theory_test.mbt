// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn test_name(name : BytesView) -> @identity.Origin {
  @identity.Origin::user(name, None, [])
}

///|
fn test_theory_name(name : BytesView) -> @theory.SemanticName {
  @theory.SemanticName::new(name, [], None)
}

///|
test "namespace lookup is qualified and conflicting imports are rejected" {
  let context = @identity.CompilationContext::new()
  let left = @logic.TypeSymbol::new_abstract(
    context,
    b"t",
    test_name(b"t"),
    [],
    None,
  )
  let right = @logic.TypeSymbol::new_abstract(
    context,
    b"t",
    test_name(b"t"),
    [],
    None,
  )
  let inner = @theory.Namespace::empty().add_type(b"t", left, None)
  let outer = @theory.Namespace::empty().add_subspace(b"Inner", inner, None)
  assert_true(outer.find_type([b"Inner", b"t"], None) == left)
  let conflicting = @theory.Namespace::empty().add_type(b"t", right, None)
  try inner.merge(conflicting, None) catch {
    TheoryError(diagnostic) => assert_eq(diagnostic.kind, AmbiguousName)
  } noraise {
    _ => fail("expected ambiguous namespace import")
  }
}

///|
test "theory builder rejects cross-context imports" {
  let left_context = @identity.CompilationContext::new()
  let right_context = @identity.CompilationContext::new()
  let left = @theory.TheoryBuilder::new(
    left_context,
    @theory.TheoryKey::new([], b"Left"),
    test_theory_name(b"Left"),
  )
  let right = @theory.TheoryBuilder::new(
    right_context,
    @theory.TheoryKey::new([], b"Right"),
    test_theory_name(b"Right"),
  ).close()
  try left.add_use(right, true, None) catch {
    _ => ()
  } noraise {
    _ => fail("expected cross-context import rejection")
  }
}

///|
test "theory scopes inherit lookup and export only their local declarations" {
  let context = @identity.CompilationContext::new()
  let builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Scoped"),
    test_theory_name(b"Scoped"),
  )
  let outer = @logic.TypeSymbol::new_abstract(
    context,
    b"outer",
    test_name(b"outer"),
    [],
    None,
  )
  builder.add_decl(
    @logic.Decl::type_declaration(context, test_name(b"outer"), [outer], None),
    None,
  )
  builder.open_scope(b"Inner", None)
  assert_true(builder.current_namespace().find_type([b"outer"], None) == outer)
  let inner = @logic.TypeSymbol::new_abstract(
    context,
    b"inner",
    test_name(b"inner"),
    [],
    None,
  )
  builder.add_decl(
    @logic.Decl::type_declaration(context, test_name(b"inner"), [inner], None),
    None,
  )
  builder.close_scope(false, None)
  let exported = builder.close().export_namespace()
  assert_true(exported.find_type([b"outer"], None) == outer)
  assert_true(exported.find_type([b"Inner", b"inner"], None) == inner)
  try exported.find_type([b"inner"], None) catch {
    TheoryError(diagnostic) => assert_eq(diagnostic.kind, UnboundName)
  } noraise {
    _ => fail("expected the closed scope to remain qualified")
  }
}

///|
test "imported scope affects lookup without leaking into export" {
  let context = @identity.CompilationContext::new()
  let builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Scoped"),
    test_theory_name(b"Scoped"),
  )
  builder.open_scope(b"Inner", None)
  let inner = @logic.TypeSymbol::new_abstract(
    context,
    b"inner",
    test_name(b"inner"),
    [],
    None,
  )
  builder.add_decl(
    @logic.Decl::type_declaration(context, test_name(b"inner"), [inner], None),
    None,
  )
  builder.close_scope(false, None)
  builder.import_scope([b"Inner"], None)
  assert_true(builder.current_namespace().find_type([b"inner"], None) == inner)
  let exported = builder.close().export_namespace()
  try exported.find_type([b"inner"], None) catch {
    TheoryError(diagnostic) => assert_eq(diagnostic.kind, UnboundName)
  } noraise {
    _ => fail("expected scope import to remain resolution-only")
  }
}

///|
test "split_theory makes lemma goals and carries axioms forward" {
  let context = @identity.CompilationContext::new()
  let builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([b"demo"], b"Split"),
    test_theory_name(b"Split"),
  )
  let lemma_symbol = @logic.PrSymbol::new(
    context,
    b"lemma",
    test_name(b"lemma"),
  )
  let goal_symbol = @logic.PrSymbol::new(context, b"goal", test_name(b"goal"))
  builder.add_decl(
    @logic.Decl::proposition(
      context,
      test_name(b"lemma"),
      Plemma,
      lemma_symbol,
      @logic.Term::true_formula(),
      None,
    ),
    None,
  )
  builder.add_decl(
    @logic.Decl::proposition(
      context,
      test_name(b"goal"),
      Pgoal,
      goal_symbol,
      @logic.Term::true_formula(),
      None,
    ),
    None,
  )
  let tasks = @theory.split_theory(context, builder.close(), None)
  assert_eq(tasks.length(), 2)
  let first = tasks[0].view().items
  assert_eq(first.length(), 1)
  assert_true(first[0] is TheoryDecl(decl) && decl.view() is Dprop(Pgoal, _, _))
  let second = tasks[1].view().items
  assert_eq(second.length(), 2)
  assert_true(
    second[0] is TheoryDecl(decl) && decl.view() is Dprop(Paxiom, _, _),
  )
  assert_true(
    second[1] is TheoryDecl(decl) && decl.view() is Dprop(Pgoal, _, _),
  )
}

///|
test "task invariant requires exactly one final goal" {
  let context = @identity.CompilationContext::new()
  let anchor = context.fresh_id()
  try @theory.Task::trusted_new(anchor, [], None) catch {
    TheoryError(diagnostic) => assert_eq(diagnostic.kind, MissingGoal)
  } noraise {
    _ => fail("expected missing goal rejection")
  }
}
