// Structural checks for WhyML extensions accepted by pprint_whyml_sexp.

///|
async fn read_extension_fixture(path : String) -> @parser.MlwFile {
  let source = @fs.read_file(path).binary() catch {
    _ => abort("cannot read extension fixture")
  }
  @parser.parse_mlw_file(source, filename=@utf8.encode(path)) catch {
    ParseError(diagnostic) => abort(diagnostic.message)
  }
}

///|
fn assert_module_span(
  module_ : @parser.MlwModule,
  start_line : Int64,
  end_line : Int64,
) -> Unit raise {
  assert_eq(module_.span.start.line, start_line)
  assert_eq(module_.span.start.column, 0L)
  assert_eq(module_.span.end.line, end_line)
  assert_eq(module_.span.end.column, 3L)
}

///|
async test "module interface extension: extraction implementation structure" {
  guard read_extension_fixture(
      "fixtures/why3-1.7.2/bench/extraction/interface1/interface1.mlw",
    )
    is Modules([set, list_set, main]) else {
    fail("expected Set, ListSet, and Main modules")
  }
  assert_true(set.kind is Module)
  assert_eq(set.name.name, b"Set")
  assert_true(set.interface is None)
  assert_eq(set.declarations.length(), 6)
  assert_module_span(set, 1L, 18L)

  assert_true(list_set.kind is Module)
  assert_eq(list_set.name.name, b"ListSet")
  assert_true(list_set.interface is Some(Qident({ name: b"Set", .. })))
  assert_eq(list_set.declarations.length(), 13)
  assert_module_span(list_set, 22L, 81L)

  assert_true(main.kind is Module)
  assert_eq(main.name.name, b"Main")
  assert_true(main.interface is None)
  assert_eq(main.declarations.length(), 2)
  assert_module_span(main, 83L, 97L)
}

///|
async test "module interface extension: cursor implementation structure" {
  guard read_extension_fixture(
      "fixtures/why3-1.7.2/examples/cursor_examples.mlw",
    )
    is Modules([test_cursor, list_cursor, test_list, array_cursor, test_array]) else {
    fail("expected five cursor modules")
  }
  assert_true(test_cursor.kind is Module)
  assert_eq(test_cursor.name.name, b"TestCursor")
  assert_true(test_cursor.interface is None)
  assert_eq(test_cursor.declarations.length(), 6)
  assert_module_span(test_cursor, 9L, 33L)

  assert_true(list_cursor.kind is Module)
  assert_eq(list_cursor.name.name, b"ListCursorImpl")
  assert_true(
    list_cursor.interface
    is Some(Qdot(Qident({ name: b"cursor", .. }), { name: b"ListCursor", .. })),
  )
  assert_eq(list_cursor.declarations.length(), 10)
  assert_module_span(list_cursor, 39L, 99L)

  assert_true(test_list.kind is Module)
  assert_eq(test_list.name.name, b"TestListCursor")
  assert_true(test_list.interface is None)
  assert_eq(test_list.declarations.length(), 11)
  assert_module_span(test_list, 101L, 130L)

  assert_true(array_cursor.kind is Module)
  assert_eq(array_cursor.name.name, b"ArrayCursorImpl")
  assert_true(
    array_cursor.interface
    is Some(Qdot(Qident({ name: b"cursor", .. }), { name: b"ArrayCursor", .. })),
  )
  assert_eq(array_cursor.declarations.length(), 12)
  assert_module_span(array_cursor, 136L, 187L)

  assert_true(test_array.kind is Module)
  assert_eq(test_array.name.name, b"TestArrayCursor")
  assert_true(test_array.interface is None)
  assert_eq(test_array.declarations.length(), 9)
  assert_module_span(test_array, 189L, 219L)
}
