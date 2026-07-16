///|
fn raise_public_parse_error(
  diagnostic : @parser.ParseDiagnostic,
) -> Unit raise @parser.ParseError {
  raise ParseError(diagnostic)
}

///|
test "diagnostic: ParseError is catchable through the public package" {
  let at = @parser.SourcePos::{
    filename: b"input.mlw",
    byte_offset: 0,
    line: 1L,
    column: 0L,
  }
  let diagnostic = @parser.ParseDiagnostic::{
    kind: UnexpectedEof,
    span: { start: at, end: at },
    actual: None,
    expected: ["term"],
    message: "unexpected end of input; expected term",
  }
  try raise_public_parse_error(diagnostic) catch {
    ParseError(caught) => assert_eq(caught, diagnostic)
  } noraise {
    _ => fail("expected ParseError")
  }
}

///|
fn public_term_error(
  source : BytesView,
  filename? : BytesView = b"",
) -> @parser.ParseDiagnostic {
  try @parser.parse_term(source, filename~) catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected public term parse error")
  }
}

///|
fn public_term_text_error(
  source : StringView,
  filename? : BytesView = b"",
) -> @parser.ParseDiagnostic {
  try @parser.parse_term_text(source, filename~) catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected public text parse error")
  }
}

///|
fn unsafe_fixed_utf16_string(code_units : FixedArray[UInt16]) -> String = "%string.unsafe_from_uint16_fixedarray"

///|
fn unsafe_test_utf16_string(code_units : ArrayView[Int]) -> String {
  unsafe_fixed_utf16_string(
    FixedArray::makei(code_units.length(), index => {
      code_units[index].to_uint16()
    }),
  )
}

///|
fn public_last_ident(path : @parser.QualId) -> @parser.Ident {
  match path {
    Qident(ident) | Qdot(_, ident) => ident
  }
}

///|
test "bytes API exposes all eight EOF-enforcing entry points" {
  let file = @parser.parse_mlw_file(
    b"module Implementation : Library.Interface end",
    filename=b"file\xff.mlw",
  )
  guard file is Modules([module_]) else { fail("expected one parsed module") }
  assert_true(module_.kind is Module)
  assert_eq(module_.name.name, b"Implementation")
  assert_true(
    module_.interface is Some(interface) &&
    public_last_ident(interface).name == b"Interface",
  )
  assert_eq(module_.span.start.filename, b"file\xff.mlw")
  let term = @parser.parse_term(b"true", filename=b"\xff")
  assert_true(term.desc is Ttrue)
  assert_eq(term.span.start.filename, b"\xff")
  let expression = @parser.parse_expr(b"1; 2")
  assert_true(expression.desc is Esequence(_, _))
  assert_eq(expression.span.start.filename, b"")
  assert_true(@parser.parse_decl(b"type t") is Dtype([_]))
  let terms = @parser.parse_term_list(b"a, b")
  assert_eq(terms.length(), 2)
  assert_true(terms[0].desc is Tident(_))
  let qualified = @parser.parse_qualid(b"A.B.value")
  assert_eq(public_last_ident(qualified).name, b"value")
  let qualified_list = @parser.parse_list_qualid(b"A.x, B.y")
  assert_eq(qualified_list.length(), 2)
  assert_eq(public_last_ident(qualified_list[1]).name, b"y")
  let identifiers = @parser.parse_list_ident(b"x, Y")
  assert_eq(identifiers.length(), 2)
  assert_eq(identifiers[0].name, b"x")
  assert_eq(identifiers[1].name, b"Y")
}

///|
test "text wrappers agree with byte entry points for every result kind" {
  assert_eq(
    @parser.parse_mlw_file_text("theory T end"),
    @parser.parse_mlw_file(b"theory T end"),
  )
  assert_eq(@parser.parse_term_text("a = a"), @parser.parse_term(b"a = a"))
  assert_eq(
    @parser.parse_expr_text("if true then 1 else 0"),
    @parser.parse_expr(b"if true then 1 else 0"),
  )
  assert_eq(
    @parser.parse_decl_text("constant zero : int = 0"),
    @parser.parse_decl(b"constant zero : int = 0"),
  )
  assert_eq(
    @parser.parse_term_list_text("a, b"),
    @parser.parse_term_list(b"a, b"),
  )
  assert_eq(
    @parser.parse_qualid_text("A.value"),
    @parser.parse_qualid(b"A.value"),
  )
  assert_eq(
    @parser.parse_list_qualid_text("A.x, B.y"),
    @parser.parse_list_qualid(b"A.x, B.y"),
  )
  assert_eq(
    @parser.parse_list_ident_text("x, Y"),
    @parser.parse_list_ident(b"x, Y"),
  )
  let unicode = @parser.parse_term_text("(*😀*) true")
  assert_true(unicode.desc is Ttrue)
  assert_eq(unicode.span.start.byte_offset, 9)
  assert_eq(unicode.span.start.column, 6L)
}

///|
test "UTF-16 validation reports prefix-relative byte and logical positions" {
  let isolated_high = unsafe_test_utf16_string([0xd800])
  let high_error = public_term_text_error(isolated_high[:], filename=b"\xff")
  assert_true(high_error.kind is InvalidUtf16)
  assert_eq(high_error.span.start, high_error.span.end)
  assert_eq(high_error.span.start.filename, b"\xff")
  assert_eq(high_error.span.start.byte_offset, 0)
  assert_eq(high_error.span.start.line, 1L)
  assert_eq(high_error.span.start.column, 0L)
  let high_then_plain = unsafe_test_utf16_string([0x00e9, 0xd800, 0x78])
  let pair_error = public_term_text_error(high_then_plain[:])
  assert_true(pair_error.kind is InvalidUtf16)
  assert_eq(pair_error.span.start.byte_offset, 2)
  assert_eq(pair_error.span.start.column, 1L)
  let isolated_low = unsafe_test_utf16_string([0x78, 0x0a, 0xdc00])
  let low_error = public_term_text_error(isolated_low[:])
  assert_true(low_error.kind is InvalidUtf16)
  assert_eq(low_error.span.start.byte_offset, 2)
  assert_eq(low_error.span.start.line, 2L)
  assert_eq(low_error.span.start.column, 0L)
}

///|
test "UTF-16 validation honors a nonzero StringView start offset" {
  let invalid_prefix = unsafe_test_utf16_string([0xd800, 0x74, 0x72, 0x75, 0x65])
  let term = @parser.parse_term_text(invalid_prefix[1:])
  assert_true(term.desc is Ttrue)
  assert_eq(term.span.start.byte_offset, 0)
  let invalid_in_view = unsafe_test_utf16_string([0x78, 0x78, 0xd800])
  let diagnostic = public_term_text_error(invalid_in_view[2:])
  assert_true(diagnostic.kind is InvalidUtf16)
  assert_eq(diagnostic.span.start.byte_offset, 0)
  assert_eq(diagnostic.span.start.column, 0L)
}

///|
test "public pipeline gives syntax and EOF failures priority at committed reads" {
  let trailing = public_term_error(b"true type")
  assert_true(trailing.kind is UnexpectedToken)
  assert_eq(trailing.span.start.byte_offset, 5)
  assert_eq(trailing.actual, Some("type"))
  assert_eq(trailing.expected, ["end of input"])
  assert_eq(trailing.message, "unexpected type; expected end of input")
  let eof = public_term_error(b"if true then")
  assert_true(eof.kind is UnexpectedEof)
  assert_eq(eof.actual, Some("end of input"))
  assert_eq(eof.expected, ["lowercase identifier"])
  assert_eq(
    eof.message,
    "unexpected end of input; expected lowercase identifier",
  )
  let early = public_term_error(b"if then (*")
  assert_true(early.kind is UnexpectedToken)
  assert_eq(early.span.start.byte_offset, 3)
}
