///|
test "location: initial and empty EOF span" {
  let at = initial_source_pos(b"input.mlw")
  assert_eq(at, { filename: b"input.mlw", byte_offset: 0, line: 1L, column: 0L })
  let span = Span::empty(at)
  assert_true(span.is_empty())
  assert_eq(span, { start: at, end: at })
}

///|
test "location: ASCII and mixed newline advancement" {
  let start = initial_source_pos(b"")
  let after_ascii = start.advance_raw(3)
  assert_eq(after_ascii.byte_offset, 3)
  assert_eq(after_ascii.column, 3L)
  let after_lf = after_ascii.advance_newline(1)
  assert_eq(after_lf.byte_offset, 4)
  assert_eq(after_lf.line, 2L)
  assert_eq(after_lf.column, 0L)
  let after_crlf = after_lf.advance_newline(2)
  assert_eq(after_crlf.byte_offset, 6)
  assert_eq(after_crlf.line, 3L)
  assert_eq(after_crlf.column, 0L)
}

///|
test "location: Lexlib-compatible UTF-8 adjustment" {
  let start = initial_source_pos(b"")
  let chinese = start.advance_lexlib_fragment(b"\xe4\xb8\xad")
  assert_eq(chinese.byte_offset, 3)
  assert_eq(chinese.column, 1L)
  let combining = start.advance_lexlib_fragment(b"e\xcc\x81")
  assert_eq(combining.byte_offset, 3)
  assert_eq(combining.column, 2L)
  let continuation = start.advance_lexlib_fragment(b"\x80")
  assert_eq(continuation.column, 1L)
  let latin1_lead = start.advance_lexlib_fragment(b"\xe9")
  assert_eq(latin1_lead.byte_offset, 1)
  assert_eq(latin1_lead.column, -1L)
  let truncated_four_byte = start.advance_comment_byte(b'\xf0')
  assert_eq(truncated_four_byte.byte_offset, 1)
  assert_eq(truncated_four_byte.column, -2L)
}

///|
test "location: logical filename switch preserves physical offset" {
  let before = initial_source_pos(b"physical.mlw").advance_raw(12)
  let switched = before.switch_logical_location(
    Some(b"logical\xff.mlw"),
    0L,
    65536L,
  )
  assert_eq(switched.filename, b"logical\xff.mlw")
  assert_eq(switched.byte_offset, 12)
  assert_eq(switched.line, 0L)
  assert_eq(switched.column, 65536L)
  let retained = switched.switch_logical_location(None, 4L, 2L)
  assert_eq(retained.filename, b"logical\xff.mlw")
}

///|
test "location: span join crosses logical filenames by byte offsets" {
  let physical = initial_source_pos(b"physical.mlw")
  let left = Span::{
    start: physical.advance_raw(2),
    end: physical.advance_raw(5),
  }
  let logical = physical
    .advance_raw(6)
    .switch_logical_location(Some(b"generated.mlw"), 40L, 0L)
  let right = Span::{ start: logical, end: logical.advance_raw(4) }
  let joined = right.join(left)
  assert_eq(joined.start, left.start)
  assert_eq(joined.end, right.end)
  assert_eq(joined.start.filename, b"physical.mlw")
  assert_eq(joined.end.filename, b"generated.mlw")
}

///|
test "diagnostic: expected tokens are stable and deduplicated" {
  let at = initial_source_pos(b"")
  let diagnostic = make_parse_diagnostic(
    UnexpectedToken,
    Span::empty(at),
    actual="END",
    expected=["term", "identifier", "term"],
  )
  assert_eq(diagnostic.expected, ["term", "identifier"])
  assert_eq(diagnostic.message, "unexpected END; expected term, identifier")
}

///|
fn SourcePos::advance_lexlib_fragment(
  self : SourcePos,
  fragment : BytesView,
) -> SourcePos {
  let advanced = self.advance_raw(fragment.length())
  {
    ..advanced,
    column: advanced.column - lexlib_utf8_adjustment(fragment).to_int64(),
  }
}
