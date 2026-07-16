///|
/// Mutable byte cursor used by the lexer. `index` always denotes an absolute
/// offset relative to the supplied `BytesView`, while `position` additionally
/// carries the logical filename/line selected by source directives.
priv struct LexerCursor {
  input : BytesView
  mut index : Int
  mut position : SourcePos
  mut token_start : SourcePos
  mut comment_depth : Int
  mut byte_advance_count : Int
}

///|
fn LexerCursor::new(input : BytesView, filename : BytesView) -> LexerCursor {
  let position = initial_source_pos(filename)
  {
    input,
    index: 0,
    position,
    token_start: position,
    comment_depth: 0,
    byte_advance_count: 0,
  }
}

///|
fn LexerCursor::at_end(self : LexerCursor) -> Bool {
  self.index >= self.input.length()
}

///|
fn LexerCursor::peek(self : LexerCursor, offset? : Int = 0) -> Byte? {
  let index = self.index + offset
  if index >= 0 && index < self.input.length() {
    Some(self.input[index])
  } else {
    None
  }
}

///|
fn LexerCursor::starts_with(self : LexerCursor, text : BytesView) -> Bool {
  if self.index + text.length() > self.input.length() {
    return false
  }
  for i = 0; i < text.length(); i = i + 1 {
    if self.input[self.index + i] != text[i] {
      return false
    }
  }
  true
}

///|
fn LexerCursor::mark_token_start(self : LexerCursor) -> Unit {
  self.token_start = self.position
}

///|
fn LexerCursor::current_span(self : LexerCursor) -> Span {
  { start: self.token_start, end: self.position }
}

///|
fn LexerCursor::empty_span(self : LexerCursor) -> Span {
  Span::empty(self.position)
}

///|
fn LexerCursor::view(self : LexerCursor, start : Int, end : Int) -> BytesView {
  self.input[start:end]
}

///|
fn LexerCursor::advance_raw(self : LexerCursor, count : Int) -> Unit {
  self.index = self.index + count
  self.byte_advance_count = self.byte_advance_count + count
  self.position = self.position.advance_raw(count)
}

///|
fn LexerCursor::advance_comment_byte(self : LexerCursor) -> Unit {
  guard self.peek() is Some(byte) else { return }
  self.index = self.index + 1
  self.byte_advance_count = self.byte_advance_count + 1
  self.position = self.position.advance_comment_byte(byte)
}

///|
fn LexerCursor::advance_newline(self : LexerCursor, count : Int) -> Unit {
  self.index = self.index + count
  self.byte_advance_count = self.byte_advance_count + count
  self.position = self.position.advance_newline(count)
}

///|
fn LexerCursor::adjust_attribute_label(
  self : LexerCursor,
  label : BytesView,
) -> Unit {
  self.position = self.position.adjust_lexlib_fragment(label)
}

///|
fn LexerCursor::switch_logical_location(
  self : LexerCursor,
  filename : Bytes?,
  line : Int64,
  column : Int64,
) -> Unit {
  self.position = self.position.switch_logical_location(filename, line, column)
}
