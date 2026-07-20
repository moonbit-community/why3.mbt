// Lazy parser cursor, syntax failures, checkpoints, and list helpers.

///|
const DEFAULT_MAX_NESTING : Int = 256

///|
priv struct SyntaxFailureInfo {
  token_index : Int
  span : Span
  actual : String
  expected : Array[String]
} derive(Debug)

///|
priv suberror SyntaxFailure {
  SyntaxFailure(SyntaxFailureInfo)
} derive(Debug)

///|
fn SyntaxFailureInfo::merge(
  self : SyntaxFailureInfo,
  other : SyntaxFailureInfo,
) -> SyntaxFailureInfo {
  if self.token_index > other.token_index {
    self
  } else if other.token_index > self.token_index {
    other
  } else {
    {
      token_index: self.token_index,
      span: self.span,
      actual: self.actual,
      expected: stable_expected(self.expected + other.expected),
    }
  }
}

///|
fn SyntaxFailureInfo::to_diagnostic(
  self : SyntaxFailureInfo,
) -> ParseDiagnostic {
  make_parse_diagnostic(
    if self.actual == "end of input" {
      UnexpectedEof
    } else {
      UnexpectedToken
    },
    self.span,
    actual=self.actual,
    expected=self.expected,
  )
}

///|
priv struct Parser {
  lexer : LazyLexer
  mut index : Int
  mut advance_count : Int
  mut nesting_depth : Int
  mut max_nesting_observed : Int
  max_nesting : Int
  mut list_push_count : Int
  mut list_finalize_count : Int
  mut application_fold_count : Int
}

///|
fn Parser::new(
  input : BytesView,
  filename? : BytesView = b"<input>",
  max_nesting? : Int = DEFAULT_MAX_NESTING,
) -> Parser {
  {
    lexer: LazyLexer::new(input, filename),
    index: 0,
    advance_count: 0,
    nesting_depth: 0,
    max_nesting_observed: 0,
    max_nesting,
    list_push_count: 0,
    list_finalize_count: 0,
    application_fold_count: 0,
  }
}

///|
/// Speculative lookahead only populates the monotonic cache.
fn Parser::peek_item_n(self : Parser, offset : Int) -> LexItem {
  self.lexer.ensure(self.index + offset)
}

///|
fn Parser::peek_kind_n(self : Parser, offset : Int) -> TokenKind? {
  match self.peek_item_n(offset) {
    Token(token) => Some(token.kind)
    DeferredLexError(_) => None
  }
}

///|
fn Parser::peek(self : Parser) -> LocatedToken raise ParseError {
  self.lexer.committed(self.index)
}

///|
fn Parser::advance(self : Parser) -> LocatedToken raise ParseError {
  let token = self.peek()
  if !(token.kind is Eof) {
    self.index = self.index + 1
    self.advance_count = self.advance_count + 1
  }
  token
}

///|
fn Parser::mark(self : Parser) -> Int {
  self.index
}

///|
fn Parser::restore(self : Parser, mark : Int) -> Unit {
  self.index = mark
}

///|
fn Parser::span_from(self : Parser, mark : Int) -> Span {
  let first = match self.lexer.ensure(mark) {
    Token(token) => token.span
    DeferredLexError(diagnostic) => diagnostic.span
  }
  if self.index <= mark {
    return Span::empty(first.start)
  }
  let last = match self.lexer.ensure(self.index - 1) {
    Token(token) => token.span
    DeferredLexError(diagnostic) => diagnostic.span
  }
  first.join(last)
}

///|
fn Parser::empty_span_at_cursor(self : Parser) -> Span raise ParseError {
  if self.index == 0 {
    return Span::empty(self.peek().span.start)
  }
  let previous = match self.lexer.ensure(self.index - 1) {
    Token(token) => token
    DeferredLexError(diagnostic) => return fail_with_diagnostic(diagnostic)
  }
  Span::empty(previous.span.end)
}

///|
fn Parser::at_keyword(self : Parser, keyword : Keyword) -> Bool {
  self.peek_kind_n(0) is Some(Keyword(actual)) && actual == keyword
}

///|
fn Parser::at_symbol(self : Parser, symbol : Symbol) -> Bool {
  self.peek_kind_n(0) is Some(Symbol(actual)) && actual == symbol
}

///|
fn Parser::consume_kind(
  self : Parser,
  kind : TokenKind,
) -> LocatedToken? raise ParseError {
  let token = self.peek()
  if token.kind == kind {
    ignore(self.advance())
    Some(token)
  } else {
    None
  }
}

///|
fn Parser::consume_keyword(
  self : Parser,
  keyword : Keyword,
) -> LocatedToken? raise ParseError {
  let token = self.peek()
  if token.kind is Keyword(actual) && actual == keyword {
    ignore(self.advance())
    Some(token)
  } else {
    None
  }
}

///|
fn Parser::consume_symbol(
  self : Parser,
  symbol : Symbol,
) -> LocatedToken? raise ParseError {
  let token = self.peek()
  if token.kind is Symbol(actual) && actual == symbol {
    ignore(self.advance())
    Some(token)
  } else {
    None
  }
}

///|
fn[A] Parser::fail_syntax(self : Parser, expected : String) -> A raise {
  let token = self.peek()
  raise SyntaxFailure({
    token_index: self.index,
    span: token.span,
    actual: token.actual,
    expected: [expected],
  })
}

///|
fn Parser::expect_kind(
  self : Parser,
  kind : TokenKind,
  expected : String,
) -> LocatedToken raise {
  if self.consume_kind(kind) is Some(token) {
    token
  } else {
    self.fail_syntax(expected)
  }
}

///|
fn Parser::expect_keyword(
  self : Parser,
  keyword : Keyword,
) -> LocatedToken raise {
  if self.consume_keyword(keyword) is Some(token) {
    token
  } else {
    self.fail_syntax(keyword.spelling())
  }
}

///|
fn Parser::expect_symbol(self : Parser, symbol : Symbol) -> LocatedToken raise {
  if self.consume_symbol(symbol) is Some(token) {
    token
  } else {
    self.fail_syntax(symbol.spelling())
  }
}

///|
fn Parser::expect_eof(self : Parser) -> Unit raise {
  ignore(self.expect_kind(Eof, "end of input"))
}

///|
fn Parser::enter_nesting(self : Parser, span : Span) -> Unit raise ParseError {
  if self.nesting_depth >= self.max_nesting {
    fail_with_diagnostic(make_parse_diagnostic(NestingTooDeep, span))
  }
  self.nesting_depth = self.nesting_depth + 1
  if self.nesting_depth > self.max_nesting_observed {
    self.max_nesting_observed = self.nesting_depth
  }
}

///|
fn Parser::leave_nesting(self : Parser) -> Unit {
  self.nesting_depth = self.nesting_depth - 1
}

///|
fn Parser::record_list_push(self : Parser) -> Unit {
  self.list_push_count = self.list_push_count + 1
}

///|
fn Parser::record_list_finalize(self : Parser) -> Unit {
  self.list_finalize_count = self.list_finalize_count + 1
}

///|
fn Parser::record_application_fold(self : Parser) -> Unit {
  self.application_fold_count = self.application_fold_count + 1
}

///|
fn[A] parse_alternative(
  parser : Parser,
  first : (Parser) -> A raise,
  second : (Parser) -> A raise,
) -> A raise {
  let mark = parser.mark()
  first(parser) catch {
    SyntaxFailure(first_failure) => {
      // Local grammar ambiguity: restoring the token index never rewinds the
      // lexer cursor or its cache.
      parser.restore(mark)
      second(parser) catch {
        SyntaxFailure(second_failure) =>
          raise SyntaxFailure(first_failure.merge(second_failure))
        other => raise other
      }
    }
    other => raise other
  }
}

///|
fn[A] parse_comma_list0(
  parser : Parser,
  starts : (Parser) -> Bool,
  parse_item : (Parser) -> A raise,
) -> Array[A] raise {
  let result : Array[A] = []
  if !starts(parser) {
    parser.record_list_finalize()
    return result
  }
  result.push(parse_item(parser))
  parser.record_list_push()
  while parser.consume_symbol(Comma) is Some(_) {
    guard starts(parser) else { parser.fail_syntax("list item") }
    result.push(parse_item(parser))
    parser.record_list_push()
  }
  parser.record_list_finalize()
  result
}

///|
fn[A] parse_comma_list1(
  parser : Parser,
  starts : (Parser) -> Bool,
  parse_item : (Parser) -> A raise,
  expected? : String = "list item",
) -> Array[A] raise {
  guard starts(parser) else { parser.fail_syntax(expected) }
  parse_comma_list0(parser, starts, parse_item)
}

///|
fn[A] parse_comma_list2(
  parser : Parser,
  starts : (Parser) -> Bool,
  parse_item : (Parser) -> A raise,
  expected? : String = "list item",
  first? : A? = None,
) -> Array[A] raise {
  let result : Array[A] = []
  if first is Some(item) {
    result.push(item)
    parser.record_list_push()
  } else {
    guard starts(parser) else { parser.fail_syntax(expected) }
    result.push(parse_item(parser))
    parser.record_list_push()
    ignore(parser.expect_symbol(Comma))
  }
  guard starts(parser) else { parser.fail_syntax(expected) }
  result.push(parse_item(parser))
  parser.record_list_push()
  while parser.consume_symbol(Comma) is Some(_) {
    guard starts(parser) else { parser.fail_syntax(expected) }
    result.push(parse_item(parser))
    parser.record_list_push()
  }
  parser.record_list_finalize()
  result
}

///|
fn[A] parse_semicolon_list1(
  parser : Parser,
  starts : (Parser) -> Bool,
  parse_item : (Parser) -> A raise,
  expected? : String = "list item",
) -> Array[A] raise {
  guard starts(parser) else { parser.fail_syntax(expected) }
  let result : Array[A] = [parse_item(parser)]
  parser.record_list_push()
  while parser.consume_symbol(Semicolon) is Some(_) {
    if !starts(parser) {
      break
    }
    result.push(parse_item(parser))
    parser.record_list_push()
  }
  parser.record_list_finalize()
  result
}

///|
fn[A] parse_bar_list1(
  parser : Parser,
  starts : (Parser) -> Bool,
  parse_item : (Parser) -> A raise,
  expected? : String = "list item",
) -> Array[A] raise {
  ignore(parser.consume_symbol(Bar))
  guard starts(parser) else { parser.fail_syntax(expected) }
  let result : Array[A] = [parse_item(parser)]
  parser.record_list_push()
  while parser.consume_symbol(Bar) is Some(_) {
    guard starts(parser) else { parser.fail_syntax(expected) }
    result.push(parse_item(parser))
    parser.record_list_push()
  }
  parser.record_list_finalize()
  result
}

///|
fn[A] parse_with_list1(
  parser : Parser,
  starts : (Parser) -> Bool,
  parse_item : (Parser) -> A raise,
  expected? : String = "list item",
) -> Array[A] raise {
  guard starts(parser) else { parser.fail_syntax(expected) }
  let result : Array[A] = [parse_item(parser)]
  parser.record_list_push()
  while parser.consume_keyword(With) is Some(_) {
    guard starts(parser) else { parser.fail_syntax(expected) }
    result.push(parse_item(parser))
    parser.record_list_push()
  }
  parser.record_list_finalize()
  result
}

///|
fn[A] parse_mapping_list_with_default(
  parser : Parser,
  starts : (Parser) -> Bool,
  parse_item : (Parser) -> A raise,
  expected? : String = "mapping item",
) -> (Array[(A, A)], A?) raise {
  let mappings : Array[(A, A)] = []
  if parser.consume_symbol(Underscore) is Some(_) {
    ignore(parser.expect_symbol(EqualArrow))
    let default = parse_item(parser)
    ignore(parser.consume_symbol(Semicolon))
    parser.record_list_finalize()
    return (mappings, Some(default))
  }
  guard starts(parser) else { parser.fail_syntax(expected) }
  while true {
    let key = parse_item(parser)
    ignore(parser.expect_symbol(EqualArrow))
    let value = parse_item(parser)
    mappings.push((key, value))
    parser.record_list_push()
    guard parser.consume_symbol(Semicolon) is Some(_) else {
      parser.record_list_finalize()
      return (mappings, None)
    }
    if parser.consume_symbol(Underscore) is Some(_) {
      ignore(parser.expect_symbol(EqualArrow))
      let default = parse_item(parser)
      ignore(parser.consume_symbol(Semicolon))
      parser.record_list_finalize()
      return (mappings, Some(default))
    }
    if !starts(parser) {
      return (mappings, None)
    }
  }
  abort("unreachable mapping-list state")
}

///|
priv enum PrattAssociativity {
  PrattLeft
  PrattRight
  PrattNonassoc
}

///|
fn pratt_binding(
  kind : TokenKind,
  expression : Bool,
) -> (Int, PrattAssociativity)? {
  match kind {
    Symbol(Semicolon) if expression => Some((10, PrattLeft))
    Symbol(LArrow) if expression => Some((20, PrattNonassoc))
    Symbol(Comma) => Some((30, PrattNonassoc))
    Symbol(Colon) => Some((40, PrattNonassoc))
    Symbol(Arrow | LRArrow) if !expression => Some((50, PrattRight))
    Keyword(By | So) if !expression => Some((50, PrattRight))
    Symbol(Or | BarBar) => Some((60, PrattRight))
    Symbol(And | AmpAmp) => Some((70, PrattRight))
    Symbol(Equal | LtGt | Lt | Gt) | Op1(_) => Some((90, PrattRight))
    Keyword(At | Old) => Some((100, PrattNonassoc))
    Op2(_) | Symbol(Minus) => Some((110, PrattLeft))
    Op3(_) => Some((120, PrattLeft))
    Op4(_) => Some((130, PrattLeft))
    _ => None
  }
}

///|
fn negation_binding_power() -> Int {
  80
}

///|
fn ordinary_prefix_binding_power() -> Int {
  140
}

///|
fn signed_numeral_binding_power() -> Int {
  150
}

///|
fn postfix_binding_power() -> Int {
  160
}

///|
fn tight_prefix_binding_power() -> Int {
  170
}
