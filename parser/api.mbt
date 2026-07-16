// Public byte and validated-text parsing entry points.

///|
fn invalid_utf16_at(
  filename : BytesView,
  byte_offset : Int,
  line : Int64,
  column : Int64,
) -> Bytes raise ParseError {
  let position = SourcePos::{
    filename: filename.to_owned(),
    byte_offset,
    line,
    column,
  }
  fail_with_diagnostic(
    make_parse_diagnostic(InvalidUtf16, Span::empty(position)),
  )
}

///|
fn encode_valid_utf16(
  source : StringView,
  filename : BytesView,
) -> Bytes raise ParseError {
  let mut index = 0
  let mut byte_offset = 0
  let mut line = 1L
  let mut column = 0L
  while index < source.length() {
    let code = source.unsafe_get(index).to_int()
    if code >= 0xd800 && code <= 0xdbff {
      if index + 1 >= source.length() {
        return invalid_utf16_at(filename, byte_offset, line, column)
      }
      let trailing = source.unsafe_get(index + 1).to_int()
      if trailing < 0xdc00 || trailing > 0xdfff {
        return invalid_utf16_at(filename, byte_offset, line, column)
      }
      index = index + 2
      byte_offset = byte_offset + 4
      column = column + 1L
      continue
    }
    if code >= 0xdc00 && code <= 0xdfff {
      return invalid_utf16_at(filename, byte_offset, line, column)
    }
    index = index + 1
    byte_offset = byte_offset +
      (if code < 0x80 { 1 } else if code < 0x800 { 2 } else { 3 })
    if code == 0x0a {
      line = line + 1L
      column = 0L
    } else {
      column = column + 1L
    }
  }
  @utf8.encode(source)
}

///|
/// Parses a complete WhyML file from raw bytes.
pub fn parse_mlw_file(
  source : BytesView,
  filename? : BytesView = b"",
) -> MlwFile raise ParseError {
  parse_mlw_file_entry(source, filename~)
}

///|
/// Parses one logical term from raw bytes.
pub fn parse_term(
  source : BytesView,
  filename? : BytesView = b"",
) -> Term raise ParseError {
  parse_term_entry(source, filename~)
}

///|
/// Parses one program expression from raw bytes.
pub fn parse_expr(
  source : BytesView,
  filename? : BytesView = b"",
) -> Expr raise ParseError {
  parse_expr_entry(source, filename~)
}

///|
/// Parses one pure or program declaration from raw bytes.
pub fn parse_decl(
  source : BytesView,
  filename? : BytesView = b"",
) -> Decl raise ParseError {
  parse_decl_entry(source, filename~)
}

///|
/// Parses a nonempty comma-separated list of logical terms from raw bytes.
pub fn parse_term_list(
  source : BytesView,
  filename? : BytesView = b"",
) -> Array[Term] raise ParseError {
  parse_term_list_entry(source, filename~)
}

///|
/// Parses one qualified identifier from raw bytes.
pub fn parse_qualid(
  source : BytesView,
  filename? : BytesView = b"",
) -> QualId raise ParseError {
  parse_qualid_entry(source, filename~)
}

///|
/// Parses a nonempty comma-separated list of qualified identifiers.
pub fn parse_list_qualid(
  source : BytesView,
  filename? : BytesView = b"",
) -> Array[QualId] raise ParseError {
  parse_qualid_list_entry(source, filename~)
}

///|
/// Parses a nonempty comma-separated list of identifiers.
pub fn parse_list_ident(
  source : BytesView,
  filename? : BytesView = b"",
) -> Array[Ident] raise ParseError {
  parse_ident_list_entry(source, filename~)
}

///|
/// Parses a complete WhyML file from validated UTF-16 text.
///
/// ```mbt check
/// test {
///   let file = @parser.parse_mlw_file_text("module Demo end")
///   assert_true(file is Modules([_]))
/// }
/// ```
pub fn parse_mlw_file_text(
  source : StringView,
  filename? : BytesView = b"",
) -> MlwFile raise ParseError {
  parse_mlw_file(encode_valid_utf16(source, filename), filename~)
}

///|
/// Parses one logical term from validated UTF-16 text.
///
/// ```mbt check
/// test {
///   let term = @parser.parse_term_text("forall x : int. x = x")
///   assert_true(term.desc is Tquant(DTforall, _, _, _))
/// }
/// ```
pub fn parse_term_text(
  source : StringView,
  filename? : BytesView = b"",
) -> Term raise ParseError {
  parse_term(encode_valid_utf16(source, filename), filename~)
}

///|
/// Parses one program expression from validated UTF-16 text.
///
/// ```mbt check
/// test {
///   let expression = @parser.parse_expr_text("let x = 1 in x")
///   assert_true(expression.desc is Elet(_, _, _, _, _))
///   try @parser.parse_expr_text("let") catch {
///     ParseError(_) => ()
///   } noraise {
///     _ => fail("expected a parse error")
///   }
/// }
/// ```
pub fn parse_expr_text(
  source : StringView,
  filename? : BytesView = b"",
) -> Expr raise ParseError {
  parse_expr(encode_valid_utf16(source, filename), filename~)
}

///|
/// Parses one pure or program declaration from validated UTF-16 text.
pub fn parse_decl_text(
  source : StringView,
  filename? : BytesView = b"",
) -> Decl raise ParseError {
  parse_decl(encode_valid_utf16(source, filename), filename~)
}

///|
/// Parses a nonempty comma-separated list of terms from validated text.
pub fn parse_term_list_text(
  source : StringView,
  filename? : BytesView = b"",
) -> Array[Term] raise ParseError {
  parse_term_list(encode_valid_utf16(source, filename), filename~)
}

///|
/// Parses one qualified identifier from validated UTF-16 text.
pub fn parse_qualid_text(
  source : StringView,
  filename? : BytesView = b"",
) -> QualId raise ParseError {
  parse_qualid(encode_valid_utf16(source, filename), filename~)
}

///|
/// Parses a nonempty comma-separated list of qualified identifiers from text.
pub fn parse_list_qualid_text(
  source : StringView,
  filename? : BytesView = b"",
) -> Array[QualId] raise ParseError {
  parse_list_qualid(encode_valid_utf16(source, filename), filename~)
}

///|
/// Parses a nonempty comma-separated list of identifiers from validated text.
pub fn parse_list_ident_text(
  source : StringView,
  filename? : BytesView = b"",
) -> Array[Ident] raise ParseError {
  parse_list_ident(encode_valid_utf16(source, filename), filename~)
}
