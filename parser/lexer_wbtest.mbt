///|
fn lex_all(
  input : BytesView,
  filename? : BytesView = b"<lexer-test>",
) -> Array[LocatedToken] raise ParseError {
  let lexer = LazyLexer::new(input, filename)
  let tokens : Array[LocatedToken] = []
  let mut index = 0
  while true {
    let token = lexer.committed(index)
    tokens.push(token)
    if token.kind is Eof {
      return tokens
    }
    index = index + 1
  }
  abort("unreachable token collection state")
}

///|
fn lex_kinds(input : BytesView) -> Array[TokenKind] raise ParseError {
  let kinds : Array[TokenKind] = []
  for token in lex_all(input) {
    if !(token.kind is Eof) {
      kinds.push(token.kind)
    }
  }
  kinds
}

///|
fn lex_error(input : BytesView) -> ParseDiagnostic {
  try lex_all(input) catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected lexical error")
  }
}

///|
fn Keyword::is_contextual(self : Keyword) -> Bool {
  self is (Float | Range | Ref)
}

///|
impl Debug for TokenKind with fn to_repr(self) {
  Debug::to_repr(self.actual())
}

///|
fn all_keywords() -> Array[Keyword] {
  [
    Abstract,
    Absurd,
    Alias,
    Any,
    As,
    Assert,
    Assume,
    At,
    Axiom,
    Begin,
    Break,
    By,
    Check,
    Clone,
    Coinductive,
    Constant,
    Continue,
    Diverges,
    Do,
    Done,
    Downto,
    Else,
    End,
    Ensures,
    Epsilon,
    Exception,
    Exists,
    Export,
    False,
    For,
    Forall,
    Fun,
    Function,
    Ghost,
    Goal,
    If,
    Import,
    In,
    Inductive,
    Invariant,
    Label,
    Lemma,
    Let,
    Match,
    Meta,
    Module,
    Mutable,
    Not,
    Old,
    Partial,
    Predicate,
    Private,
    Pure,
    Raise,
    Raises,
    Reads,
    Rec,
    Requires,
    Return,
    Returns,
    Scope,
    So,
    Then,
    Theory,
    To,
    True,
    Try,
    Type,
    Use,
    Val,
    Variant,
    While,
    With,
    Writes,
    Float,
    Range,
    Ref,
  ]
}

///|
test "keywords: all 74 plain and 3 contextual spellings round-trip" {
  let keywords = all_keywords()
  assert_eq(keywords.length(), 77)
  let mut contextual = 0
  for keyword in keywords {
    let spelling = keyword.spelling()
    let bytes = @utf8.encode(spelling[:])
    guard keyword_of(bytes) is Some(looked_up) else {
      fail("missing keyword {spelling}")
    }
    assert_true(looked_up == keyword)
    let tokens = lex_kinds(bytes)
    assert_eq(tokens, [Keyword(keyword)])
    if keyword.is_contextual() {
      contextual = contextual + 1
    }
  }
  assert_eq(contextual, 3)
  assert_true(keyword_of(b"Float") is None)
  assert_true(keyword_of(b"ranges") is None)
}

///|
test "identifiers: suffix, core, quoted, keyword boundary, and underscore" {
  assert_eq(lex_kinds(b"x x1_2 x''' X X9 _ _x type types"), [
    Lident(b"x"),
    Lident(b"x1_2"),
    Lident(b"x'''"),
    Uident(b"X"),
    Uident(b"X9"),
    Symbol(Underscore),
    Lident(b"_x"),
    Keyword(Type),
    Lident(b"types"),
  ])
  assert_eq(lex_kinds(b"foo'bar Foo''bar'baz 'alpha9_''"), [
    CoreLident(b"foo'bar"),
    CoreUident(b"Foo''bar'baz"),
    QuoteLident(b"alpha9_''"),
  ])
  try lex_kinds(b"'Alpha") catch {
    ParseError(diagnostic) => assert_true(diagnostic.kind is IllegalCharacter)
  } noraise {
    _ => fail("expected IllegalCharacter")
  }
  let actual = lex_all(b"foo +++")[0].actual
  assert_eq(actual, "lowercase identifier `foo`")
  let quoted = lex_all(b"'alpha")
  assert_true(quoted[0].kind is QuoteLident(b"alpha"))
  assert_eq(
    (quoted[0].span.start.byte_offset, quoted[0].span.end.byte_offset),
    (0, 6),
  )
}

///|
test "numbers: integer bases, separators, long values, and range backjump" {
  let long = b"9".repeat(120)
  let source = b"0 1__ 0xA_f__ 0o7_ 0b1__ " + long + b" 123.. 0xAB.."
  let tokens = lex_kinds(source)
  assert_eq(tokens.length(), 10)
  assert_true(
    tokens[0] is Integer({ kind: ILitDec, value }) && value.to_string() == "0",
  )
  assert_true(
    tokens[1] is Integer({ kind: ILitDec, value }) && value.to_string() == "1",
  )
  assert_true(
    tokens[2] is Integer({ kind: ILitHex, value }) && value.to_string() == "175",
  )
  assert_true(
    tokens[3] is Integer({ kind: ILitOct, value }) && value.to_string() == "7",
  )
  assert_true(
    tokens[4] is Integer({ kind: ILitBin, value }) && value.to_string() == "1",
  )
  assert_true(
    tokens[5] is Integer({ value, .. }) && value.to_string().length() == 120,
  )
  assert_true(tokens[6] is Integer({ value, .. }) && value.to_string() == "123")
  assert_eq(tokens[7], Symbol(DotDot))
  assert_true(
    tokens[8] is Integer({ kind: ILitHex, value }) && value.to_string() == "171",
  )
  assert_eq(tokens[9], Symbol(DotDot))
}

///|
test "numbers: decimal and hexadecimal real forms and underscore splitting" {
  let tokens = lex_kinds(
    b".5 1. 1e2 1.25e-2 0x1.p2 0x.8p0 1_0.0 1.0_0 0xA_B.p0",
  )
  assert_true(tokens[0] is Real({ kind: RLitDec(0L), .. }))
  assert_true(tokens[1] is Real({ kind: RLitDec(0L), .. }))
  assert_true(tokens[2] is Real({ kind: RLitDec(2L), .. }))
  assert_true(tokens[3] is Real({ kind: RLitDec(-2L), .. }))
  assert_true(tokens[4] is Real({ kind: RLitHex(2L), .. }))
  assert_true(tokens[5] is Real({ kind: RLitHex(0L), .. }))
  assert_true(tokens[6] is Integer({ value, .. }) && value.to_string() == "10")
  assert_true(tokens[7] is Real(_))
  assert_true(tokens[8] is Real(_))
  assert_eq(tokens[9], Lident(b"_0"))
  assert_true(tokens[10] is Integer({ kind: ILitHex, .. }))
  assert_eq(tokens[11], Symbol(Dot))
  assert_eq(tokens[12], Lident(b"p0"))
  assert_eq(lex_kinds(b"0x 0o 0b 1e 0x.p"), [
    Integer({ kind: ILitDec, value: BigInt::from_int(0) }),
    Lident(b"x"),
    Integer({ kind: ILitDec, value: BigInt::from_int(0) }),
    Lident(b"o"),
    Integer({ kind: ILitDec, value: BigInt::from_int(0) }),
    Lident(b"b"),
    Integer({ kind: ILitDec, value: BigInt::from_int(1) }),
    Lident(b"e"),
    Integer({ kind: ILitDec, value: BigInt::from_int(0) }),
    Lident(b"x"),
    Symbol(Dot),
    Lident(b"p"),
  ])
}

///|
test "operators: every reserved symbol and longest-match generic levels" {
  let symbols = [
    (b"/\\", And),
    (b"->", Arrow),
    (b"=>", EqualArrow),
    (b"&", Amp),
    (b"|", Bar),
    (b":", Colon),
    (b",", Comma),
    (b".", Dot),
    (b"..", DotDot),
    (b"=", Equal),
    (b"<", Lt),
    (b">", Gt),
    (b"<>", LtGt),
    (b"-", Minus),
    (b"(", LeftPar),
    (b"[", LeftSq),
    (b"[|", LeftSqBar),
    (b"<-", LArrow),
    (b"<->", LRArrow),
    (b"\\/", Or),
    (b")", RightPar),
    (b"]", RightSq),
    (b"|]", BarRightSq),
    (b"_", Underscore),
    (b"&&", AmpAmp),
    (b"||", BarBar),
    (b"{", LeftBrc),
    (b"}", RightBrc),
    (b";", Semicolon),
  ]
  for pair in symbols {
    assert_eq(lex_kinds(pair.0), [Symbol(pair.1)])
  }
  assert_eq(lex_kinds(b"!! !+ != ++' **' $$"), [
    OpPref(b"!!"),
    Op2(b"!+"),
    Op1(b"!="),
    Op2(b"++'"),
    Op3(b"**'"),
    Op4(b"$$"),
  ])
  let lexer = LazyLexer::new(b"$'", b"operators.mlw")
  assert_true(lexer.ensure(0) is Token({ kind: Op4(b"$"), .. }))
  assert_true(
    lexer.ensure(1) is DeferredLexError({ kind: IllegalCharacter, span, .. }) &&
    span.start.byte_offset == 1,
  )
}

///|
test "operators: mixfix payload boundaries, spans, arrow quote, and comment lookalike" {
  let tokens = lex_all(b"]'' )'spec )_spec")
  assert_true(tokens[0].kind is RightSqQuote(b"''"))
  assert_eq(
    (tokens[0].span.start.byte_offset, tokens[0].span.end.byte_offset),
    (0, 3),
  )
  assert_true(tokens[1].kind is RightParQuote(b"'spec"))
  assert_eq(
    (tokens[1].span.start.byte_offset, tokens[1].span.end.byte_offset),
    (4, 10),
  )
  assert_true(tokens[2].kind is RightParUscore(b"_spec"))
  assert_eq(
    (tokens[2].span.start.byte_offset, tokens[2].span.end.byte_offset),
    (11, 17),
  )
  let arrow = LazyLexer::new(b"->'", b"operators.mlw")
  assert_true(
    arrow.ensure(0) is Token({ kind: Symbol(Arrow), span, .. }) &&
    span.start.byte_offset == 0 &&
    span.end.byte_offset == 2,
  )
  assert_true(
    arrow.ensure(1) is DeferredLexError({ kind: IllegalCharacter, .. }),
  )
  assert_eq(lex_kinds(b"(*)"), [Symbol(LeftPar), Op3(b"*"), Symbol(RightPar)])
}

///|
test "strings: simple, decimal, hexadecimal, and octal escapes preserve bytes" {
  let simple = Bytes::from_array([
    b'"', b'a', b'\\', b'n', b'\\', b'r', b'\\', b't', b'\\', b'b', b'\\', b'\'',
    b'\\', b'"', b'\\', b'\\', b'"',
  ])
  let tokens = lex_kinds(simple)
  assert_eq(tokens, [
    StringToken(
      Bytes::from_array([b'a', b'\n', b'\r', b'\t', b'\b', b'\'', b'"', b'\\']),
    ),
  ])
  let numeric = Bytes::from_array([
    b'"', b'\\', b'2', b'5', b'5', b'\\', b'x', b'F', b'f', b'\\', b'o', b'3', b'7',
    b'7', b'"',
  ])
  assert_eq(lex_kinds(numeric), [
    StringToken(Bytes::from_array([b'\xff', b'\xff', b'\xff'])),
  ])
}

///|
test "strings: LF, CRLF, and repeated-CR continuations reset logical line" {
  let cases = [
    Bytes::from_array([b'"', b'x', b'\\', b'\n', b' ', b'\t', b'y', b'"']),
    Bytes::from_array([b'"', b'x', b'\\', b'\r', b'\n', b' ', b'y', b'"']),
    Bytes::from_array([
      b'"', b'x', b'\\', b'\r', b'\r', b'\n', b'\t', b'y', b'"',
    ]),
  ]
  let expected_columns = [4L, 3L, 3L]
  for index, source in cases {
    let tokens = lex_all(source)
    assert_true(tokens[0].kind is StringToken(b"xy"))
    assert_eq(tokens[0].span.end.line, 2L)
    assert_eq(tokens[0].span.end.column, expected_columns[index])
  }
}

///|
test "strings: lexical error classes use escape, byte, and EOF-local spans" {
  let illegal_escape = lex_error(
    Bytes::from_array([b'"', b'a', b'\\', b'q', b'"']),
  )
  assert_true(illegal_escape.kind is IllegalEscape)
  assert_eq(
    (illegal_escape.span.start.byte_offset, illegal_escape.span.end.byte_offset),
    (2, 4),
  )
  let illegal_byte = lex_error(Bytes::from_array([b'"', b'a', b'\n', b'"']))
  assert_true(illegal_byte.kind is IllegalStringByte)
  assert_eq(
    (illegal_byte.span.start.byte_offset, illegal_byte.span.end.byte_offset),
    (2, 3),
  )
  let unterminated = lex_error(b"\"abc")
  assert_true(unterminated.kind is UnterminatedString)
  assert_eq(
    (unterminated.span.start.byte_offset, unterminated.span.end.byte_offset),
    (4, 4),
  )
  let trailing_slash = lex_error(Bytes::from_array([b'"', b'\\']))
  assert_true(trailing_slash.kind is UnterminatedString)
  assert_eq(trailing_slash.span.start.byte_offset, 2)
  for
    source in [
      Bytes::from_array([b'"', b'\\', b'2', b'5', b'6', b'"']),
      Bytes::from_array([b'"', b'\\', b'x', b'F', b'"']),
      Bytes::from_array([b'"', b'\\', b'o', b'4', b'0', b'0', b'"']),
      Bytes::from_array([b'"', b'\\', b'\r', b'"']),
    ] {
    let diagnostic = lex_error(source)
    assert_true(diagnostic.kind is IllegalEscape)
    assert_eq(
      diagnostic.span.end.byte_offset - diagnostic.span.start.byte_offset,
      2,
    )
  }
}

///|
test "comments: trivia, nesting, CRLF, special lookalike, and arbitrary bytes" {
  let nested = lex_all(b" \t\r\n(* a (* b (* c *) *)\r\n *)x")
  assert_true(nested[0].kind is Lident(b"x"))
  assert_eq(nested[0].span.start.line, 3L)
  assert_eq(nested[0].span.start.column, 3L)
  assert_eq(lex_kinds(b"(**)x"), [Lident(b"x")])
  assert_eq(lex_kinds(b"(*)"), [Symbol(LeftPar), Op3(b"*"), Symbol(RightPar)])
  let unicode = lex_all(
    Bytes::from_array([b'(', b'*', b'\xc3', b'\xa9', b'*', b')', b'x']),
  )
  assert_eq(unicode[0].span.start.byte_offset, 6)
  assert_eq(unicode[0].span.start.column, 5L)
  let latin1 = lex_all(
    Bytes::from_array([b'(', b'*', b'\xe9', b'*', b')', b'x']),
  )
  assert_eq(latin1[0].span.start.byte_offset, 5)
  assert_eq(latin1[0].span.start.column, 3L)
  let continuation = lex_all(
    Bytes::from_array([b'(', b'*', b'\x80', b'*', b')', b'x']),
  )
  assert_eq(continuation[0].span.start.column, 5L)
  let truncated = lex_all(
    Bytes::from_array([b'(', b'*', b'\xf0', b'*', b')', b'x']),
  )
  assert_eq(truncated[0].span.start.byte_offset, 5)
  assert_eq(truncated[0].span.start.column, 2L)
}

///|
test "comments: unterminated error remains fixed to opening delimiter" {
  let diagnostic = lex_error(b"abc (* nested (* still open")
  assert_true(diagnostic.kind is UnterminatedComment)
  assert_eq(
    (diagnostic.span.start.byte_offset, diagnostic.span.end.byte_offset),
    (4, 6),
  )
}

///|
test "positions: trivia and line directives preserve physical offsets" {
  let trivia = lex_all(b" \t\r\nx\r\n y")
  assert_eq(
    (
      trivia[0].span.start.byte_offset,
      trivia[0].span.start.line,
      trivia[0].span.start.column,
    ),
    (4, 2L, 0L),
  )
  assert_eq(
    (
      trivia[1].span.start.byte_offset,
      trivia[1].span.start.line,
      trivia[1].span.start.column,
    ),
    (8, 3L, 1L),
  )
  let source = Bytes::from_array([
    b'[', b'#', b'#', b' ', b'"', b'f', b'\xff', b'"', b' ', b'7', b' ', b'3', b']',
    b'x',
  ])
  let switched = lex_all(source, filename=b"original.mlw")
  assert_eq(switched[0].span.start.filename, Bytes::from_array([b'f', b'\xff']))
  assert_eq(switched[0].span.start.byte_offset, 13)
  assert_eq(
    (switched[0].span.start.line, switched[0].span.start.column),
    (7L, 3L),
  )
  let retained = lex_all(b"[## 9 4]x", filename=b"original.mlw")
  assert_eq(retained[0].span.start.filename, b"original.mlw")
  assert_eq(
    (retained[0].span.start.line, retained[0].span.start.column),
    (9L, 4L),
  )
  let zero = lex_all(b"[## 0 0]x")
  assert_eq((zero[0].span.start.line, zero[0].span.start.column), (0L, 0L))
  let maximum = lex_all(b"[## 4611686018427387903 4611686018427387903]x")
  assert_eq(
    (maximum[0].span.start.line, maximum[0].span.start.column),
    (4611686018427387903L, 4611686018427387903L),
  )
}

///|
test "positions: position attributes compress large columns and do not switch cursor" {
  let source = Bytes::from_array([
    b'[', b'#', b' ', b'"', b'f', b'\xff', b'"', b' ', b'6', b' ', b'6', b'5', b'5',
    b'3', b'6', b' ', b'8', b' ', b'4', b']', b'x',
  ])
  let tokens = lex_all(source, filename=b"outer.mlw")
  guard tokens[0].kind is PositionToken(position) else {
    fail("expected POSITION token")
  }
  assert_eq(position.start.filename, Bytes::from_array([b'f', b'\xff']))
  assert_eq((position.start.line, position.start.column), (7L, 0L))
  assert_eq((position.end.line, position.end.column), (8L, 4L))
  assert_eq(tokens[0].span.start.byte_offset, 0)
  assert_eq(tokens[0].span.end.byte_offset, 20)
  assert_eq(tokens[1].span.start.filename, b"outer.mlw")
  assert_eq(tokens[1].span.start.column, 20L)
  let boundaries = lex_all(
    b"[# \"f\" 140737488355327 4611686018427387903 0 65535]",
  )
  assert_true(boundaries[0].kind is PositionToken(_))
}

///|
test "positions: attributes trim only ordinary spaces and adjust label UTF-8" {
  let source = Bytes::from_array([
    b'[', b'@', b' ', b'\t', b'\r', b'f', b'o', b'o', b' ', b'b', b'a', b'r', b'\t',
    b'\r', b' ', b' ', b']', b'x',
  ])
  let tokens = lex_all(source)
  assert_true(tokens[0].kind is AttributeToken(b"foo bar\t\r"))
  assert_eq(
    (tokens[0].span.start.byte_offset, tokens[0].span.end.byte_offset),
    (0, 17),
  )
  let unicode = lex_all(
    Bytes::from_array([b'[', b'@', b'\xc3', b'\xa9', b']', b'x']),
  )
  assert_true(
    unicode[0].kind is AttributeToken(value) &&
    value == Bytes::from_array([b'\xc3', b'\xa9']),
  )
  assert_eq(unicode[1].span.start.byte_offset, 5)
  assert_eq(unicode[1].span.start.column, 4L)
  let arbitrary = lex_all(Bytes::from_array([b'[', b'@', b'\xff', b']', b'x']))
  assert_true(
    arbitrary[0].kind is AttributeToken(value) &&
    value == Bytes::from_array([b'\xff']),
  )
}

///|
test "errors: malformed directives, numeric overflow, and illegal bytes are structured" {
  for
    source in [
      b"[## -1 0]", b"[# \"f\" 1 2 3]", b"[@ ]", b"[@x\n]", b"[@unterminated",
    ] {
    let diagnostic = lex_error(source)
    assert_true(diagnostic.kind is InvalidPositionDirective)
  }
  let line_overflow = lex_error(b"[# \"f\" 140737488355328 0 1 0]")
  assert_true(line_overflow.kind is NumericOverflow)
  let directive_overflow = lex_error(b"[## 4611686018427387904 0]")
  assert_true(directive_overflow.kind is NumericOverflow)
  let exponent_overflow = lex_error(b"1e4611686018427387904")
  assert_true(exponent_overflow.kind is NumericOverflow)
  let illegal = lex_error(Bytes::from_array([b'\xff']))
  assert_true(illegal.kind is IllegalCharacter)
  assert_eq(
    (illegal.span.start.byte_offset, illegal.span.end.byte_offset),
    (0, 1),
  )
}

///|
test "errors: lazy cache defers sentinels and never scans beyond a terminal item" {
  let source = Bytes::from_array([b'x', b' ', b'\xff', b' ', b'y'])
  let lexer = LazyLexer::new(source, b"lazy.mlw")
  assert_eq(lexer.scan_count, 0)
  assert_true(lexer.ensure(0) is Token({ kind: Lident(b"x"), .. }))
  assert_eq(lexer.scan_count, 1)
  assert_true(
    lexer.ensure(2) is DeferredLexError({ kind: IllegalCharacter, .. }),
  )
  assert_eq(lexer.scan_count, 2)
  assert_eq(lexer.cache.length(), 2)
  assert_true(lexer.ensure(3) is DeferredLexError(_))
  assert_eq(lexer.scan_count, 2)
  try lexer.committed(1) catch {
    ParseError(diagnostic) => assert_true(diagnostic.kind is IllegalCharacter)
  } noraise {
    _ => fail("committed access must raise deferred error")
  }
  assert_eq(lexer.commit_count, 1)
  let complete = LazyLexer::new(b"x y", b"lazy.mlw")
  assert_true(complete.ensure(20) is Token({ kind: Eof, .. }))
  assert_eq(complete.scan_count, 3)
  assert_true(
    complete.ensure(21) is Token({ kind: Eof, span, actual }) &&
    span.is_empty() &&
    actual == "end of input",
  )
  assert_eq(complete.scan_count, 3)
}
