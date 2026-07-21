// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn test_key(path : Array[Bytes], name : Bytes) -> @theory.TheoryKey raise {
  @theory.TheoryKey::new(path, name)
}

///|
fn test_name(name : BytesView) -> @theory.SemanticName {
  @theory.SemanticName::new(name, [], None)
}

///|
fn catalog_origin(symbol : @stdlib.DriverSymbol) -> @identity.Origin {
  match symbol {
    DriverType(value) => value.origin()
    DriverLogic(value) => value.view().origin
    DriverProposition(value) => value.view().origin
    DriverProgramType(value) => value.view().origin
    DriverRoutine(value) => value.view().origin
  }
}

///|
test "minimal_env reconstructs the complete frozen closure and public roots" {
  let context = @identity.CompilationContext::new()
  let frozen = @stdlib.minimal_env(context) catch {
    @logic.TypeError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("snapshot reconstruction raised TypeError")
    }
    @stdlib.SnapshotError(diagnostic) => {
      debug_inspect(diagnostic)
      fail("snapshot reconstruction raised SnapshotError")
    }
    _ => fail("snapshot reconstruction raised another error")
  }
  let manifest = frozen.manifest()
  assert_eq(manifest.theory_count, 73)
  assert_eq(manifest.module_count, 25)
  assert_eq(manifest.symbol_count, 2317)
  assert_eq(manifest.type_variable_count, 10)
  assert_eq(manifest.why3_commit, b"1343338d3bb1941c0d4f134283bb0790816113c4")
  let environment = frozen.view()
  assert_eq(environment.theory_keys.length(), 73)
  assert_eq(environment.module_keys.length(), 25)
  assert_eq(environment.visible_theory_aliases.length(), 5)
  assert_eq(environment.visible_module_aliases.length(), 5)
  let catalog = frozen.driver_catalog()
  assert_eq(catalog.length(), 2317)
  catalog.validate_context(context)
}

///|
test "stdlib handles expose exact Int and Real program operators" {
  let context = @identity.CompilationContext::new()
  let frozen = @stdlib.minimal_env(context)
  let handles = frozen.handles().view()
  assert_eq(handles.int_type.view().logic_type.name(), b"int")
  assert_eq(handles.real_type.view().logic_type.name(), b"real")
  assert_eq(handles.bool_type.view().logic_type.name(), b"bool")
  assert_eq(handles.unit_type.view().logic_type.name(), b"unit")
  assert_eq(handles.int_negate.view().name, b"prefix -")
  assert_eq(handles.int_greater_equal.view().name, b"infix >=")
  assert_eq(handles.real_add.view().name, b"infix +")
  assert_eq(handles.real_divide.view().name, b"infix /")
  assert_true(handles.int_negate.view().logic is RLls(_))
  assert_true(handles.real_add.view().logic is RLls(_))
  assert_true(handles.real_divide.view().logic is RLnone)
  let qualified = @mlw.PmoduleBuilder::new(
    context,
    test_key([b"test"], b"Qualified"),
    test_name(b"Qualified"),
  )
  frozen.use_module(qualified, test_key([b"int"], b"Int"), false, None)
  assert_true(
    qualified.pure_namespace().find_type([b"Int", b"int"], None) ==
    handles.int_type.view().logic_type,
  )
  assert_true(
    qualified.program_namespace().find_routine([b"Int", b"prefix -"], None) ==
    handles.int_negate,
  )
  let imported = @mlw.PmoduleBuilder::new(
    context,
    test_key([b"test"], b"Imported"),
    test_name(b"Imported"),
  )
  frozen.use_module(imported, test_key([b"int"], b"Int"), true, None)
  assert_true(
    imported.pure_namespace().find_type([b"int"], None) ==
    handles.int_type.view().logic_type,
  )
  assert_true(
    imported.program_namespace().find_routine([b"infix >="], None) ==
    handles.int_greater_equal,
  )
  let completed = imported.close()
  assert_true(
    completed
    .pure_theory()
    .context_anchor()
    .same_context(completed.context_anchor()),
  )
  let foreign = @mlw.PmoduleBuilder::new(
    @identity.CompilationContext::new(),
    test_key([b"test"], b"Foreign"),
    test_name(b"Foreign"),
  )
  try frozen.use_module(foreign, test_key([b"int"], b"Int"), true, None) catch {
    @mlw.MlwError(diagnostic) => assert_eq(diagnostic.kind, MlwContextMismatch)
    _ => fail("unexpected cross-context module use error")
  } noraise {
    _ => fail("expected cross-context module use rejection")
  }
}

///|
test "driver-only and unknown roots remain distinct" {
  let frozen = @stdlib.minimal_env(@identity.CompilationContext::new())
  let hidden = [
    test_key([b"bv"], b"BV8"),
    test_key([b"ieee_float"], b"Float32"),
    test_key([b"map"], b"Map"),
    test_key([b"string"], b"String"),
  ]
  for key in hidden {
    try frozen.resolve_theory(key, None) catch {
      EnvironmentError(diagnostic) =>
        assert_eq(diagnostic.kind, DriverOnlyTheory)
    } noraise {
      _ => fail("expected driver-only theory rejection")
    }
  }
  try frozen.resolve_theory(test_key([b"missing"], b"Theory"), None) catch {
    @environment.EnvironmentError(diagnostic) =>
      assert_eq(diagnostic.kind, ResolveError)
    _ => fail("unexpected unknown-theory resolution error")
  } noraise {
    _ => fail("expected unknown theory rejection")
  }
  try frozen.resolve_module(test_key([b"algebra"], b"Assoc"), None) catch {
    @environment.EnvironmentError(diagnostic) =>
      assert_eq(diagnostic.kind, DriverOnlyTheory)
    _ => fail("unexpected driver-only module error")
  } noraise {
    _ => fail("expected driver-only module rejection")
  }
}

///|
test "catalog keys are portable but bound symbols are context-local" {
  let left_context = @identity.CompilationContext::new()
  let right_context = @identity.CompilationContext::new()
  let left_frozen = @stdlib.minimal_env(left_context)
  let left = left_frozen.driver_catalog()
  let right_frozen = @stdlib.minimal_env(right_context)
  let right = right_frozen.driver_catalog()
  let left_projection = left_frozen.semantic_projection()
  let right_projection = right_frozen.semantic_projection()
  assert_eq(
    @canonical.bytes_to_lower_hex(left_projection.theory_sha256),
    b"56cee7dfcb3c4e9579760b9a0dc9d08ea9678c5bda7b9a942a1b07b54489ede7",
  )
  assert_eq(
    @canonical.bytes_to_lower_hex(left_projection.module_sha256),
    b"15e8df6c89b12aab237c113ba1ddff4425f03d0d5675ae8ceea6547b1619b2fa",
  )
  assert_eq(left_projection.theory_sha256, right_projection.theory_sha256)
  assert_eq(left_projection.module_sha256, right_projection.module_sha256)
  assert_eq(left.keys(), right.keys())
  for key in left.keys() {
    let symbol = left.resolve_symbol(key)
    match catalog_origin(symbol).view() {
      SnapshotOrigin(_, origin_key, _) => assert_true(origin_key == key)
      _ => fail("catalog symbol lost snapshot provenance")
    }
  }
  let mut type_key : @identity.SnapshotSymbolKey? = None
  for key in left.keys() {
    if left.resolve_symbol(key) is DriverType(_) {
      type_key = Some(key)
      break
    }
  }
  guard type_key is Some(type_key) else {
    fail("frozen catalog has no logic type entry")
  }
  try left.resolve_logic(type_key) catch {
    BindError(diagnostic) => assert_eq(diagnostic.kind, SymbolKindMismatch)
  } noraise {
    _ => fail("expected catalog kind mismatch")
  }
  let missing = @identity.SnapshotSymbolKey::new(
    b"missing.Theory",
    0U,
    0U,
    Type,
    Bytes::make(32, b'\x00'),
  )
  try left.resolve_type(missing) catch {
    BindError(diagnostic) => assert_eq(diagnostic.kind, MissingSymbol)
  } noraise {
    _ => fail("expected missing catalog symbol")
  }
  let left_tasks = @theory.split_theory(
    left_context,
    left_frozen.resolve_theory(test_key([b"int"], b"Int"), None),
    None,
  )
  let right_tasks = @theory.split_theory(
    right_context,
    right_frozen.resolve_theory(test_key([b"int"], b"Int"), None),
    None,
  )
  assert_true(!left_tasks.is_empty())
  assert_eq(left_tasks.length(), right_tasks.length())
  for index = 0; index < left_tasks.length(); index = index + 1 {
    assert_eq(
      @canonical.encode_task(left_tasks[index]).bytes(),
      @canonical.encode_task(right_tasks[index]).bytes(),
    )
  }
  try left.validate_context(right_context) catch {
    BindError(diagnostic) => assert_eq(diagnostic.kind, CatalogContextMismatch)
  } noraise {
    _ => fail("expected catalog context mismatch")
  }
  let original = left.keys()[0].view()
  let changed = original.symbol_digest.to_array()
  changed[0] = changed[0] ^ b'\x01'
  let wrong = @identity.SnapshotSymbolKey::new(
    original.theory_key,
    original.theory_item_ordinal,
    original.declaration_inner_ordinal,
    original.symbol_kind,
    Bytes::from_array(changed),
  )
  try left.resolve_type(wrong) catch {
    BindError(diagnostic) => assert_eq(diagnostic.kind, SymbolDigestMismatch)
  } noraise {
    _ => fail("expected catalog digest mismatch")
  }
}
