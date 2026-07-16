///|
/// A logical source position paired with its absolute offset in the original
/// byte input. Logical filenames may change across position directives while
/// `byte_offset` remains monotonic within one parse.
pub(all) struct SourcePos {
  filename : Bytes
  byte_offset : Int
  line : Int64
  column : Int64
} derive(Debug, Eq)

///|
/// A half-open source range `[start, end)`.
pub(all) struct Span {
  start : SourcePos
  end : SourcePos
} derive(Debug, Eq)

///|
fn initial_source_pos(filename : BytesView) -> SourcePos {
  { filename: filename.to_owned(), byte_offset: 0, line: 1L, column: 0L }
}

///|
fn SourcePos::advance_raw(self : SourcePos, byte_count : Int) -> SourcePos {
  {
    ..self,
    byte_offset: self.byte_offset + byte_count,
    column: self.column + byte_count.to_int64(),
  }
}

///|
fn utf8_extra_bytes(byte : Byte) -> Int {
  let value = byte.to_int()
  if value <= 0x7f {
    0
  } else if value >= 0xc0 && value <= 0xdf {
    1
  } else if value >= 0xe0 && value <= 0xef {
    2
  } else if value >= 0xf0 && value <= 0xf7 {
    3
  } else {
    -1
  }
}

///|
fn lexlib_utf8_adjustment(fragment : BytesView) -> Int {
  for i = 0, adjustment = 0; i < fragment.length(); {
    let extra = utf8_extra_bytes(fragment[i])
    if extra >= 0 {
      continue i + 1 + extra, adjustment + extra
    } else {
      continue i + 1, adjustment
    }
  } nobreak {
    adjustment
  }
}

///|
/// Applies only Lexlib's post-scan UTF-8 column correction. This is used for
/// attribute labels: ocamllex has already advanced over the complete
/// directive before `adjust_pos_utf8` is called.
fn SourcePos::adjust_lexlib_fragment(
  self : SourcePos,
  fragment : BytesView,
) -> SourcePos {
  { ..self, column: self.column - lexlib_utf8_adjustment(fragment).to_int64() }
}

///|
fn SourcePos::advance_comment_byte(self : SourcePos, byte : Byte) -> SourcePos {
  let advanced = self.advance_raw(1)
  let extra = utf8_extra_bytes(byte)
  if extra > 0 {
    { ..advanced, column: advanced.column - extra.to_int64() }
  } else {
    advanced
  }
}

///|
fn SourcePos::advance_newline(
  self : SourcePos,
  consumed_bytes : Int,
) -> SourcePos {
  {
    ..self,
    byte_offset: self.byte_offset + consumed_bytes,
    line: self.line + 1L,
    column: 0L,
  }
}

///|
fn SourcePos::switch_logical_location(
  self : SourcePos,
  filename : Bytes?,
  line : Int64,
  column : Int64,
) -> SourcePos {
  let filename = match filename {
    Some(filename) => filename
    None => self.filename
  }
  { ..self, filename, line, column }
}

///|
pub fn Span::empty(at : SourcePos) -> Span {
  { start: at, end: at }
}

///|
pub fn Span::is_empty(self : Span) -> Bool {
  self.start.byte_offset == self.end.byte_offset
}

///|
/// Returns the smallest offset-based span covering both inputs. Logical
/// filenames are deliberately not required to match because a `[## ...]`
/// directive may occur between the two endpoints.
pub fn Span::join(self : Span, other : Span) -> Span {
  let start = if self.start.byte_offset <= other.start.byte_offset {
    self.start
  } else {
    other.start
  }
  let end = if self.end.byte_offset >= other.end.byte_offset {
    self.end
  } else {
    other.end
  }
  { start, end }
}
