// White-box tests for parser state, identifiers, and operator notation.

///|
fn qualid_segments(qualid : QualId) -> Array[Bytes] {
  match qualid {
    Qident(ident) => [ident.name]
    Qdot(prefix, ident) => qualid_segments(prefix) + [ident.name]
  }
}

///|
fn qualid_error(input : BytesView) -> ParseDiagnostic {
  try parse_qualid_entry(input) catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected qualified-identifier error")
  }
}

///|
fn parse_test_word(parser : Parser) -> Bytes raise {
  let token = parser.peek()
  match token.kind {
    Lident(word) => {
      ignore(parser.advance())
      word
    }
    _ => parser.fail_syntax("test word")
  }
}

///|
fn starts_test_word(parser : Parser) -> Bool {
  parser.peek_kind_n(0) is Some(Lident(_))
}

///|
fn fail_test_syntax(parser : Parser, expected : String) -> Unit raise {
  parser.fail_syntax(expected)
}

///|
fn captured_syntax_failure(work : () -> Unit raise) -> SyntaxFailureInfo {
  try work() catch {
    SyntaxFailure(failure) => failure
    _ => abort("expected syntax failure")
  } noraise {
    _ => abort("expected syntax failure")
  }
}

///|
fn captured_parse_error(work : () -> Unit raise) -> ParseDiagnostic {
  try work() catch {
    ParseError(diagnostic) => diagnostic
    _ => abort("expected parse error")
  } noraise {
    _ => abort("expected parse error")
  }
}

///|
test "parser state: speculative lookahead and restore preserve monotonic lexer state" {
  let parser = Parser::new(b"x y")
  assert_true(parser.peek_item_n(1) is Token({ kind: Lident(b"y"), .. }))
  assert_eq(parser.lexer.scan_count, 2)
  let mark = parser.mark()
  ignore(parser.advance())
  parser.restore(mark)
  assert_eq(parser.index, 0)
  assert_eq(parser.lexer.scan_count, 2)
  assert_eq(parser.lexer.cache.length(), 2)
  assert_eq(parser.advance().kind, Lident(b"x"))
  assert_eq(parser.lexer.scan_count, 2)
  assert_true(parser.peek_item_n(50) is Token({ kind: Eof, .. }))
  ignore(parser.advance())
  let eof_index = parser.index
  ignore(parser.advance())
  assert_eq(parser.index, eof_index)
}

///|
test "parser state: speculative lexical sentinel is committed only by parser operations" {
  let parser = Parser::new(Bytes::from_array([b'x', b' ', b'\xff']))
  assert_true(parser.peek_item_n(1) is DeferredLexError(_))
  assert_eq(parser.index, 0)
  ignore(parser.advance())
  try parser.peek() catch {
    ParseError(diagnostic) => assert_true(diagnostic.kind is IllegalCharacter)
  } noraise {
    _ => fail("expected deferred lexical error")
  }
}

///|
test "parser state: syntax failures merge stable expectations at the farthest token" {
  let parser = Parser::new(b"x")
  let same = captured_syntax_failure(() => {
    ignore(
      parse_alternative(parser, parser => fail_test_syntax(parser, "alpha"), parser => {
        fail_test_syntax(parser, "beta")
      }),
    )
  })
  assert_eq(same.expected, ["alpha", "beta"])
  let parser = Parser::new(b"x")
  let farthest = captured_syntax_failure(() => {
    ignore(
      parse_alternative(
        parser,
        parser => {
          ignore(parser.advance())
          fail_test_syntax(parser, "dot")
        },
        parser => fail_test_syntax(parser, "uppercase identifier"),
      ),
    )
  })
  assert_eq(farthest.token_index, 1)
  assert_eq(farthest.expected, ["dot"])
}

///|
test "parser state: semantic and lexical errors are never alternative failures" {
  let span = Span::empty(initial_source_pos(b"state.mlw"))
  let semantic = captured_parse_error(() => {
    ignore(
      parse_alternative(
        Parser::new(b"x"),
        _ => fail_with_diagnostic(make_parse_diagnostic(DoubleReference, span)),
        _ => 42,
      ),
    )
  })
  assert_true(semantic.kind is DoubleReference)
  let lexical = captured_parse_error(() => {
    ignore(
      parse_alternative(
        Parser::new(Bytes::from_array([b'\xff'])),
        parser => {
          ignore(parser.expect_symbol(Dot))
          1
        },
        _ => 2,
      ),
    )
  })
  assert_true(lexical.kind is IllegalCharacter)
}

///|
test "error coverage table names evidence for every public ParseErrorKind" {
  let coverage : Array[(ParseErrorKind, String)] = [
    (InvalidUtf16, "api_test: UTF-16 validation"),
    (IllegalCharacter, "lexer_wbtest: error ranges"),
    (UnterminatedComment, "lexer_wbtest: nested comments"),
    (UnterminatedString, "lexer_wbtest: strings"),
    (IllegalEscape, "lexer_wbtest: strings"),
    (IllegalStringByte, "lexer_wbtest: strings"),
    (InvalidNumericLiteral, "literal_wbtest: exact integers"),
    (InvalidPositionDirective, "lexer_wbtest: directives"),
    (UnexpectedToken, "api_test: public pipeline"),
    (UnexpectedEof, "api_test: public pipeline"),
    (NestingTooDeep, "parse_type_pattern_wbtest: nesting budget"),
    (NumericOverflow, "literal/lexer/decl tests"),
    (DuplicateVariant, "parse_expr_wbtest: specification union"),
    (InvalidAssignment, "parse_expr/desugar tests"),
    (InvalidParallelAssignment, "parse_expr/desugar tests"),
    (GhostPartialConflict, "parse_expr_wbtest: modifiers"),
    (InvalidPartialDeclaration, "desugar_wbtest: partial forms"),
    (DoubleReference, "parse_type_pattern_wbtest: binders"),
    (AnonymousReference, "parse_type_pattern_wbtest: binders"),
    (UndeterminedParameterType, "parse_type_pattern_wbtest: params"),
    (IllegalKindQualifier, "parse_expr/desugar tests"),
    (RestrictedAnySpec, "parse_expr_wbtest: any specification"),
    (ReservedCoreIdentifier, "parse_ident/type-pattern tests"),
    (UnsupportedEpsilon, "parse_term_wbtest: epsilon"),
    (NestedModule, "parse_decl_wbtest: file states"),
  ]
  assert_eq(coverage.length(), 25)
  let seen : Array[ParseErrorKind] = []
  for entry in coverage {
    let (kind, evidence) = entry
    assert_false(seen.contains(kind))
    assert_false(evidence.is_empty())
    seen.push(kind)
  }
}

///|
test "parser state: committed first error stops before every unneeded tail byte" {
  let syntax_first = Parser::new(b"if then (* unterminated")
  let syntax = try
    finish_internal_entry(syntax_first, parser => parser.parse_expr())
  catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected syntax failure before lexical tail")
  }
  assert_true(syntax.kind is UnexpectedToken)
  assert_eq(syntax.actual, Some("then"))
  assert_eq(syntax.expected, ["lowercase identifier"])
  assert_eq(syntax.message, "unexpected then; expected lowercase identifier")
  assert_eq(syntax_first.lexer.scan_count, 2)
  assert_eq(syntax_first.lexer.cache_push_count, 2)
  assert_eq(syntax_first.lexer.cursor.byte_advance_count, 7)

  let lexical_first = Parser::new(Bytes::from_array([b'\xff', b' ', b't']))
  let lexical = try
    finish_internal_entry(lexical_first, parser => parser.parse_expr())
  catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected lexical failure before syntax")
  }
  assert_true(lexical.kind is IllegalCharacter)
  assert_eq(lexical_first.lexer.scan_count, 1)
  assert_eq(lexical_first.lexer.cache_push_count, 1)
  assert_eq(lexical_first.lexer.cursor.byte_advance_count, 1)
}

///|
fn make_repeated_source(
  item : String,
  separator : String,
  count : Int,
) -> Bytes {
  let builder = StringBuilder(
    size_hint=(item.length() + separator.length()) * count,
  )
  for index = 0; index < count; index = index + 1 {
    if index > 0 {
      builder.write_string(separator)
    }
    builder.write_string(item)
  }
  @utf8.encode(builder.to_string())
}

///|
test "parser complexity: 2.5k/5k/10k flat application, declaration, and comma lists stay linear" {
  for size in [2500, 5000, 10000] {
    let application_source = make_repeated_source("x", " ", size)
    let application = Parser::new(application_source)
    ignore(finish_internal_entry(application, parser => parser.parse_expr()))
    assert_eq(
      application.lexer.cursor.byte_advance_count,
      application_source.length(),
    )
    assert_eq(application.lexer.cache_push_count, size + 1)
    assert_eq(application.lexer.scan_count, size + 1)
    assert_eq(application.advance_count, size)
    assert_eq(application.application_fold_count, size - 1)
    assert_eq(application.nesting_depth, 0)
    assert_eq(application.max_nesting_observed, 0)

    let declaration_source = make_repeated_source("type t", " ", size)
    let declarations = Parser::new(declaration_source)
    ignore(
      finish_internal_entry(declarations, parser => parser.parse_mlw_file()),
    )
    assert_eq(
      declarations.lexer.cursor.byte_advance_count,
      declaration_source.length(),
    )
    assert_eq(declarations.lexer.cache_push_count, size * 2 + 1)
    assert_eq(declarations.lexer.scan_count, size * 2 + 1)
    assert_eq(declarations.advance_count, size * 2)
    assert_eq(declarations.list_push_count, size)
    assert_eq(declarations.list_finalize_count, 1)
    assert_eq(declarations.nesting_depth, 0)
    assert_eq(declarations.max_nesting_observed, 0)

    let comma_source = make_repeated_source("x", ",", size)
    let comma_list = Parser::new(comma_source)
    let identifiers = finish_internal_entry(comma_list, parser => {
      parse_comma_list1(
        parser,
        parser => starts_ident(parser),
        parser => parser.parse_ident(),
        expected="identifier",
      )
    })
    assert_eq(identifiers.length(), size)
    assert_eq(comma_list.lexer.cursor.byte_advance_count, comma_source.length())
    assert_eq(comma_list.lexer.cache_push_count, size * 2)
    assert_eq(comma_list.lexer.scan_count, size * 2)
    assert_eq(comma_list.advance_count, size * 2 - 1)
    assert_eq(comma_list.list_push_count, size)
    assert_eq(comma_list.list_finalize_count, 1)
    assert_eq(comma_list.nesting_depth, 0)
    assert_eq(comma_list.max_nesting_observed, 0)
  }
}

///|
test "list helpers: comma zero, one, and two enforce their cardinalities" {
  let empty = Parser::new(b"")
  assert_eq(parse_comma_list0(empty, starts_test_word, parse_test_word), [])
  let single = Parser::new(b"x")
  assert_eq(parse_comma_list1(single, starts_test_word, parse_test_word), [b"x"])
  single.expect_eof()
  let multiple = Parser::new(b"x,y,z")
  assert_eq(parse_comma_list2(multiple, starts_test_word, parse_test_word), [
    b"x", b"y", b"z",
  ])
  multiple.expect_eof()
  ignore(
    captured_syntax_failure(() => {
      ignore(
        parse_comma_list2(Parser::new(b"x"), starts_test_word, parse_test_word),
      )
    }),
  )
  ignore(
    captured_syntax_failure(() => {
      ignore(
        parse_comma_list1(Parser::new(b"x,"), starts_test_word, parse_test_word),
      )
    }),
  )
}

///|
test "list helpers: semicolon, bar, with, and mapping/default shapes" {
  ignore(
    captured_syntax_failure(() => {
      ignore(
        parse_semicolon_list1(
          Parser::new(b""),
          starts_test_word,
          parse_test_word,
        ),
      )
    }),
  )
  let semicolon_single = Parser::new(b"x;")
  assert_eq(
    parse_semicolon_list1(semicolon_single, starts_test_word, parse_test_word),
    [b"x"],
  )
  semicolon_single.expect_eof()
  let semicolons = Parser::new(b"x;y;")
  assert_eq(
    parse_semicolon_list1(semicolons, starts_test_word, parse_test_word),
    [b"x", b"y"],
  )
  semicolons.expect_eof()
  ignore(
    captured_syntax_failure(() => {
      ignore(
        parse_bar_list1(Parser::new(b""), starts_test_word, parse_test_word),
      )
    }),
  )
  let bar_single = Parser::new(b"|x")
  assert_eq(parse_bar_list1(bar_single, starts_test_word, parse_test_word), [
    b"x",
  ])
  bar_single.expect_eof()
  let bars = Parser::new(b"|x|y")
  assert_eq(parse_bar_list1(bars, starts_test_word, parse_test_word), [
    b"x", b"y",
  ])
  bars.expect_eof()
  ignore(
    captured_syntax_failure(() => {
      ignore(
        parse_bar_list1(Parser::new(b"x|"), starts_test_word, parse_test_word),
      )
    }),
  )
  ignore(
    captured_syntax_failure(() => {
      ignore(
        parse_with_list1(Parser::new(b""), starts_test_word, parse_test_word),
      )
    }),
  )
  let with_single = Parser::new(b"x")
  assert_eq(parse_with_list1(with_single, starts_test_word, parse_test_word), [
    b"x",
  ])
  with_single.expect_eof()
  let withs = Parser::new(b"x with y")
  assert_eq(parse_with_list1(withs, starts_test_word, parse_test_word), [
    b"x", b"y",
  ])
  withs.expect_eof()
  ignore(
    captured_syntax_failure(() => {
      ignore(
        parse_with_list1(
          Parser::new(b"x with"),
          starts_test_word,
          parse_test_word,
        ),
      )
    }),
  )
  ignore(
    captured_syntax_failure(() => {
      ignore(
        parse_mapping_list_with_default(
          Parser::new(b""),
          starts_test_word,
          parse_test_word,
        ),
      )
    }),
  )
  let mapping_single = Parser::new(b"x=>y;")
  assert_eq(
    parse_mapping_list_with_default(
      mapping_single, starts_test_word, parse_test_word,
    ),
    ([(b"x", b"y")], None),
  )
  mapping_single.expect_eof()
  let default_only = Parser::new(b"_=>d;")
  assert_eq(
    parse_mapping_list_with_default(
      default_only, starts_test_word, parse_test_word,
    ),
    ([], Some(b"d")),
  )
  default_only.expect_eof()
  let mappings = Parser::new(b"x=>y;z=>w;_=>d;")
  let (pairs, default) = parse_mapping_list_with_default(
    mappings, starts_test_word, parse_test_word,
  )
  assert_eq(pairs, [(b"x", b"y"), (b"z", b"w")])
  assert_eq(default, Some(b"d"))
  mappings.expect_eof()
}

///|
test "binding powers: table order, associativity, and prefix separation are fixed" {
  assert_true(pratt_binding(Symbol(Semicolon), true) is Some((10, PrattLeft)))
  assert_true(pratt_binding(Symbol(LArrow), true) is Some((20, PrattNonassoc)))
  assert_true(pratt_binding(Symbol(Arrow), false) is Some((50, PrattRight)))
  assert_true(pratt_binding(Keyword(At), false) is Some((100, PrattNonassoc)))
  assert_true(pratt_binding(Op2(b"+"), false) is Some((110, PrattLeft)))
  assert_true(negation_binding_power() < 90)
  assert_true(ordinary_prefix_binding_power() < signed_numeral_binding_power())
  assert_true(signed_numeral_binding_power() < postfix_binding_power())
  assert_true(postfix_binding_power() < tight_prefix_binding_power())
}

///|
test "operator grammar: prefix and infix helper families encode every token class" {
  for
    item in [
      (b"~", b"prefix ~"),
      (b"+", b"prefix +"),
      (b"*", b"prefix *"),
      (b"$", b"prefix $"),
      (b"<", b"prefix <"),
      (b">", b"prefix >"),
      (b"-", b"prefix -"),
    ] {
    let (source, expected) = item
    let parser = Parser::new(source)
    assert_eq(
      finish_internal_entry(parser, parser => parser.parse_prefix_op()).name,
      expected,
    )
  }
  let parser = Parser::new(b"!!")
  assert_eq(
    finish_internal_entry(parser, parser => parser.parse_oppref()).name,
    b"prefix !!",
  )
  for
    item in [
      (b"~", b"infix ~"),
      (b"=", b"infix ="),
      (b"<>", b"infix <>"),
      (b"<", b"infix <"),
      (b">", b"infix >"),
    ] {
    let (source, expected) = item
    let parser = Parser::new(source)
    assert_eq(
      finish_internal_entry(parser, parser => parser.parse_infix_op_1()).name,
      expected,
    )
  }
  for
    item in [
      (b"+", b"infix +"),
      (b"*", b"infix *"),
      (b"$", b"infix $"),
      (b"-", b"infix -"),
    ] {
    let (source, expected) = item
    let parser = Parser::new(source)
    assert_eq(
      finish_internal_entry(parser, parser => parser.parse_infix_op_234()).name,
      expected,
    )
  }
}

///|
test "operator notation: every internal encoding is exact" {
  assert_eq(op_infix(b"+"), b"infix +")
  assert_eq(op_prefix(b"-"), b"prefix -")
  assert_eq(op_get(b"''"), b"mixfix []''")
  assert_eq(op_set(b""), b"mixfix []<-")
  assert_eq(op_update(b"'"), b"mixfix [<-]'")
  assert_eq(op_cut(b""), b"mixfix [..]")
  assert_eq(op_lcut(b""), b"mixfix [.._]")
  assert_eq(op_rcut(b""), b"mixfix [_..]")
}

///|
test "operator notation: decoder distinguishes all forms and appended suffixes" {
  assert_true(notation_decode(b"plain") is SNword(b"plain"))
  assert_true(notation_decode(op_infix(b"+")) is SNinfix(b"+"))
  assert_true(notation_decode(op_prefix(b"!")) is SNtight(b"!"))
  assert_true(notation_decode(op_prefix(b"!+")) is SNprefix(b"!+"))
  assert_true(notation_decode(op_get(b"''")) is SNget(b"''"))
  assert_true(notation_decode(op_set(b"")) is SNset(b""))
  assert_true(notation_decode(op_update(b"")) is SNupdate(b""))
  assert_true(notation_decode(op_cut(b"")) is SNcut(b""))
  assert_true(notation_decode(op_lcut(b"")) is SNlcut(b""))
  assert_true(notation_decode(op_rcut(b"")) is SNrcut(b""))
  assert_true(notation_decode(b"infix +_suffix") is SNword(b"(+)_suffix"))
}

///|
test "identifiers: contextual words, ref, core references, and nq restrictions" {
  let idents = parse_ident_list_entry(b"range,float,ref,X,X'a,x'a")
  assert_eq(idents.map(ident => ident.name), [
    b"range", b"float", b"ref", b"X", b"X'a", b"x'a",
  ])
  assert_eq(qualid_segments(parse_qualid_entry(b"x'a")), [b"x'a"])
  let parser = Parser::new(b"x'a")
  try finish_internal_entry(parser, parser => parser.parse_ident_nq()) catch {
    ParseError(diagnostic) => {
      assert_true(diagnostic.kind is ReservedCoreIdentifier)
      assert_eq(diagnostic.span.start.byte_offset, 0)
    }
  } noraise {
    _ => fail("expected core identifier definition error")
  }
  let parser = Parser::new(b"X'a")
  try finish_internal_entry(parser, parser => parser.parse_ident_nq()) catch {
    ParseError(diagnostic) =>
      assert_true(diagnostic.kind is ReservedCoreIdentifier)
  } noraise {
    _ => fail("expected uppercase core identifier definition error")
  }
  let parser = Parser::new(b"ref")
  try finish_internal_entry(parser, parser => parser.parse_ident_nq()) catch {
    ParseError(diagnostic) => assert_true(diagnostic.kind is UnexpectedToken)
  } noraise {
    _ => fail("expected ref definition restriction")
  }
}

///|
test "symbolic identifiers: infix, prefix, mixfix, and suffix names match Why3" {
  let idents = parse_ident_list_entry(
    b"(+),(+_),([]),([]<-),([<-]),([..]),([.._]),([_..]),([]''),(+)_suffix,(+)'suffix",
  )
  assert_eq(idents.map(ident => ident.name), [
    b"infix +", b"prefix +", b"mixfix []", b"mixfix []<-", b"mixfix [<-]", b"mixfix [..]",
    b"mixfix [.._]", b"mixfix [_..]", b"mixfix []''", b"infix +_suffix", b"infix +'suffix",
  ])
  let classes = parse_ident_list_entry(
    b"(~),(*),($),(<),(>),(=),(-),(-_),(!!),(!!_)",
  )
  assert_eq(classes.map(ident => ident.name), [
    b"infix ~", b"infix *", b"infix $", b"infix <", b"infix >", b"infix =", b"infix -",
    b"prefix -", b"prefix !!", b"prefix !!",
  ])
  let parser = Parser::new(b"(+)'suffix")
  try finish_internal_entry(parser, parser => parser.parse_ident_nq()) catch {
    ParseError(diagnostic) =>
      assert_true(diagnostic.kind is ReservedCoreIdentifier)
  } noraise {
    _ => fail("expected quoted symbolic definition error")
  }
  let symbolic_error_span = diagnostic_span_of_symbolic_definition_error()
  assert_eq(
    (symbolic_error_span.start.byte_offset, symbolic_error_span.end.byte_offset),
    (0, 10),
  )
}

///|
fn diagnostic_span_of_symbolic_definition_error() -> Span {
  let parser = Parser::new(b"(+)'suffix")
  try finish_internal_entry(parser, parser => parser.parse_ident_nq()) catch {
    ParseError(diagnostic) => diagnostic.span
  } noraise {
    _ => abort("expected symbolic definition error")
  }
}

///|
test "qualified identifiers: each family preserves its segment restrictions" {
  assert_eq(qualid_segments(parse_qualid_entry(b"M.N.x")), [b"M", b"N", b"x"])
  assert_eq(qualid_segments(parse_qualid_entry(b"M.N")), [b"M", b"N"])
  let parser = Parser::new(b"M.N")
  assert_eq(
    qualid_segments(
      finish_internal_entry(parser, parser => parser.parse_uqualid()),
    ),
    [b"M", b"N"],
  )
  let parser = Parser::new(b"M.N.x")
  assert_eq(
    qualid_segments(
      finish_internal_entry(parser, parser => parser.parse_lqualid()),
    ),
    [b"M", b"N", b"x"],
  )
  let parser = Parser::new(b"M.(+)")
  assert_eq(
    qualid_segments(
      finish_internal_entry(parser, parser => parser.parse_lqualid_rich()),
    ),
    [b"M", b"infix +"],
  )
  let parser = Parser::new(b"foo.\"bar\".M")
  assert_eq(
    qualid_segments(
      finish_internal_entry(parser, parser => parser.parse_tqualid()),
    ),
    [b"foo", b"bar", b"M"],
  )
  let parser = Parser::new(b"foo.\"bar\".M")
  assert_eq(
    qualid_segments(
      finish_internal_entry(parser, parser => parser.parse_squalid()).0,
    ),
    [b"foo", b"bar", b"M"],
  )
  assert_eq(parse_qualid_list_entry(b"x,M.y,(+)").map(qualid_segments), [
    [b"x"],
    [b"M", b"y"],
    [b"infix +"],
  ])
  assert_true(qualid_error(b"M.x.y").kind is UnexpectedToken)
}

///|
test "attributes: text and position attributes attach in source order" {
  let parser = Parser::new(b"x [@first] [# \"f\" 1 0 1 0] [@last]")
  let ident = finish_internal_entry(parser, parser => {
    parse_attrs_ident(parser, parser => parser.parse_lident(true, false))
  })
  assert_true(ident.attributes[0] is Text(b"first"))
  assert_true(ident.attributes[1] is Position(_))
  assert_true(ident.attributes[2] is Text(b"last"))
  assert_eq((ident.span.start.byte_offset, ident.span.end.byte_offset), (0, 1))
}

///|
test "identifier entries: EOF is mandatory and reports the trailing token" {
  let diagnostic = qualid_error(b"x y")
  assert_true(diagnostic.kind is UnexpectedToken)
  assert_eq(diagnostic.span.start.byte_offset, 2)
  assert_eq(diagnostic.actual, Some("lowercase identifier `y`"))
}
