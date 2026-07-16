///|
fn literal_test_span() -> Span {
  Span::empty(initial_source_pos(b"literal.mlw"))
}

///|
test "literal: integer kinds and bases" {
  let span = literal_test_span()
  assert_eq(make_int_constant(ILitBin, b"1010_0110", span~), {
    kind: ILitBin,
    value: BigInt::from_int(166),
  })
  assert_eq(
    make_int_constant(ILitOct, b"000_777", span~).value,
    BigInt::from_int(511),
  )
  assert_eq(
    make_int_constant(ILitDec, b"001_234", span~).value,
    BigInt::from_int(1234),
  )
  assert_eq(
    make_int_constant(ILitHex, b"ff_FF", span~).value,
    BigInt::from_int(65535),
  )
  assert_eq(
    make_int_constant(ILitDec, b"42", negative=true, span~).value,
    BigInt::from_int(-42),
  )
  let unknown = IntConstant::{ kind: ILitUnk, value: BigInt::from_int(0) }
  assert_true(unknown.kind is ILitUnk)
}

///|
test "literal: hundreds of digits never narrow through Int" {
  let digits = Bytes::make(300, b'9')
  let parsed = make_int_constant(ILitDec, digits, span=literal_test_span())
  assert_eq(parsed.value.to_string(), "9".repeat(300))
}

///|
test "literal: invalid digits are structured errors" {
  let span = literal_test_span()
  try make_int_constant(ILitBin, b"102", span~) catch {
    ParseError(diagnostic) => {
      assert_true(diagnostic.kind is InvalidNumericLiteral)
      assert_eq(diagnostic.span, span)
    }
  } noraise {
    _ => fail("expected InvalidNumericLiteral")
  }
}

///|
test "literal: decimal real normalization" {
  let span = literal_test_span()
  let one_eighth = make_real_constant(10, b"0", b"125", 0L, span~)
  assert_true(one_eighth.kind is RLitDec(0L))
  assert_eq(one_eighth.value.significand(), BigInt::from_int(1))
  assert_eq(one_eighth.value.pow2(), BigInt::from_int(-3))
  assert_eq(one_eighth.value.pow5(), BigInt::from_int(0))
  let scaled = make_real_constant(10, b"12", b"34", -5L, span~)
  assert_eq(scaled.value.significand(), BigInt::from_int(617))
  assert_eq(scaled.value.pow2(), BigInt::from_int(-6))
  assert_eq(scaled.value.pow5(), BigInt::from_int(-7))
}

///|
test "literal: hexadecimal and negative real normalization" {
  let span = literal_test_span()
  let hexadecimal = make_real_constant(16, b"9A", b"B", 5L, span~)
  assert_true(hexadecimal.kind is RLitHex(5L))
  assert_eq(hexadecimal.value.significand(), BigInt::from_int(99))
  assert_eq(hexadecimal.value.pow2(), BigInt::from_int(1))
  assert_eq(hexadecimal.value.pow5(), BigInt::from_int(2))
  let negative = make_real_constant(10, b"0", b"125", 0L, negative=true, span~)
  assert_eq(negative.value.significand(), BigInt::from_int(-1))
  assert_eq(negative.negated(), make_real_constant(10, b"0", b"125", 0L, span~))
}

///|
test "literal: zero and long significand normalization" {
  let span = literal_test_span()
  let zero = make_real_constant(10, b"0", b"000", 100L, span~).value
  assert_eq(zero.significand(), BigInt::from_int(0))
  assert_eq(zero.pow2(), BigInt::from_int(0))
  assert_eq(zero.pow5(), BigInt::from_int(0))
  let power_of_ten = b"1" + Bytes::make(100, b'0')
  let normalized = make_real_constant(10, power_of_ten, b"", 0L, span~).value
  assert_eq(normalized.significand(), BigInt::from_int(1))
  assert_eq(normalized.pow2(), BigInt::from_int(100))
  assert_eq(normalized.pow5(), BigInt::from_int(100))
  let unknown = RealConstant::{ kind: RLitUnk, value: zero }
  assert_true(unknown.kind is RLitUnk)
}

///|
test "literal: OCaml int boundaries" {
  let span = literal_test_span()
  assert_eq(
    checked_ocaml_int(BigInt::from_string("-4611686018427387904"), span),
    OCAML_INT_MIN,
  )
  assert_eq(
    checked_ocaml_int(BigInt::from_string("4611686018427387903"), span),
    OCAML_INT_MAX,
  )
  for text in ["-4611686018427387905", "4611686018427387904"] {
    try checked_ocaml_int(BigInt::from_string(text), span) catch {
      ParseError(diagnostic) => assert_true(diagnostic.kind is NumericOverflow)
    } noraise {
      _ => fail("expected NumericOverflow")
    }
  }
}

///|
test "literal: Why3 line and compressed column boundaries" {
  let span = literal_test_span()
  assert_eq(
    checked_directive_number(BigInt::from_string("4611686018427387903"), span),
    OCAML_INT_MAX,
  )
  for text in ["-1", "4611686018427387904"] {
    try checked_directive_number(BigInt::from_string(text), span) catch {
      ParseError(diagnostic) => assert_true(diagnostic.kind is NumericOverflow)
    } noraise {
      _ => fail("expected NumericOverflow")
    }
  }
  assert_eq(
    checked_why3_line(BigInt::from_string("140737488355327"), span),
    WHY3_MAX_LINE,
  )
  try checked_why3_line(BigInt::from_string("140737488355328"), span) catch {
    ParseError(diagnostic) => assert_true(diagnostic.kind is NumericOverflow)
  } noraise {
    _ => fail("expected NumericOverflow")
  }
  assert_eq(why3_decode_line_column(7L, 65535L), (7L, 65535L))
  assert_eq(why3_decode_line_column(6L, 65536L), (7L, 0L))
  assert_eq(
    why3_decode_line_column(0L, OCAML_INT_MAX),
    (70368744177663L, 65535L),
  )
  assert_eq(
    why3_decode_line_column(WHY3_MAX_LINE, OCAML_INT_MAX),
    (WHY3_MAX_LINE, 65535L),
  )
}

///|
test "literal: bytes string constant is lossless" {
  let constant = ConstStr(b"\xff")
  assert_true(constant is ConstStr(bytes) && bytes == b"\xff")
}
