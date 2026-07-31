// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn test_key(path : Array[Bytes], name : Bytes) -> @theory.TheoryKey raise {
  @theory.TheoryKey::new(path, name)
}

///|
test "embedded provider contains every one of the 53 upstream source files" {
  let paths = @stdlib.embedded_stdlib_paths()
  assert_eq(paths.length(), 53)
  for index, path in paths {
    for earlier in 0..<index {
      assert_true(path != paths[earlier])
    }
    let candidates = @stdlib.embedded_source_provider().candidates(path, [
      b"mlw", b"why",
    ])
    assert_eq(candidates.length(), 1)
    let source = candidates[0].view()
    assert_eq(source.provider_root, b"why3-1.7.2/stdlib")
    assert_eq(source.extension, b"mlw")
    assert_true(!source.contents.is_empty())
  }
}

///|
test "embedded environments install exact language builtins on demand" {
  let context = @identity.CompilationContext::new()
  let environment = @stdlib.embedded_environment_in_context(context)
  let view = environment.view()
  assert_eq(view.theory_keys.length(), 5)
  assert_eq(view.module_keys.length(), 5)
  assert_eq(view.visible_theory_aliases.length(), 9)
  assert_eq(view.visible_module_aliases.length(), 9)

  let builtin = environment.resolve_module(test_key([], b"BuiltIn"), None)
  guard builtin.view().items
    is [
      Udecl(PDtype([integer], [_], [])),
      Udecl(PDtype([real], [_], [])),
      Udecl(PDtype([string], [_], [])),
      Udecl(PDpure([equality_declaration], [])),
    ] else {
    fail("BuiltIn module declaration inventory drifted")
  }
  for
    entry in [
      (integer, b"int", @logic.BuiltinInteger),
      (real, b"real", @logic.BuiltinReal),
      (string, b"string", @logic.BuiltinString),
    ] {
    let symbol = entry.0.view().symbol.view().logic_type
    assert_eq(symbol.name(), entry.1)
    assert_true(symbol.builtin_kind() == Some(entry.2))
  }
  guard equality_declaration.view() is Dparam(equality) else {
    fail("BuiltIn equality is not a parameter")
  }
  assert_eq(equality.view().name, b"infix =")

  let boolean = environment.resolve_module(test_key([], b"Bool"), None)
  guard boolean.view().items is [Udecl(PDtype([boolean_type], [_], []))] else {
    fail("Bool module declaration inventory drifted")
  }
  assert_true(
    boolean_type.view().symbol.view().logic_type.builtin_kind() ==
    Some(@logic.BuiltinBoolean),
  )
  assert_eq(boolean_type.view().constructors.length(), 2)

  let unit = environment.resolve_module(test_key([], b"Unit"), None)
  guard unit.view().items is [Uuse(_), Udecl(PDtype([unit_type], [_], []))] else {
    fail("Unit module declaration inventory drifted")
  }
  assert_true(
    unit_type.view().symbol.view().definition is ProgramAlias(target) &&
    target.view() is ItyApp(symbol, [], _) &&
    symbol.view().logic_type.name() == b"tuple0",
  )

  let tuple = environment.tuple_module(2)
  guard tuple.view().items is [Udecl(PDtype([tuple_type], [_], []))] else {
    fail("Tuple2 module declaration inventory drifted")
  }
  assert_eq(tuple_type.view().constructors.length(), 1)
  assert_eq(tuple_type.view().constructors[0].view().name, b"Tuple2")
}

///|
test "embedded environments keep semantic identities context-local" {
  let left = @stdlib.embedded_environment()
  let right = @stdlib.embedded_environment()
  let key = test_key([], b"BuiltIn")
  let left_builtin = left.resolve_module(key, None)
  let right_builtin = right.resolve_module(key, None)
  assert_true(
    !left_builtin.context_anchor().same_context(right_builtin.context_anchor()),
  )
  assert_eq(
    left_builtin.pure_theory().view().name.view().name,
    right_builtin.pure_theory().view().name.view().name,
  )
}
