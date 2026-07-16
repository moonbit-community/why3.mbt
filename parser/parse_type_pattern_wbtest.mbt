///|
fn ast_test_span(offset : Int) -> Span {
  let at = SourcePos::{
    filename: b"ast.mlw",
    byte_offset: offset,
    line: 1L,
    column: offset.to_int64(),
  }
  Span::empty(at)
}

///|
fn ast_test_ident(name : Bytes, offset : Int) -> Ident {
  { name, attributes: [], span: ast_test_span(offset) }
}

///|
test "AST identifiers: arbitrary attribute bytes and segment spans are preserved" {
  let left = ast_test_ident(b"M", 0)
  let right = Ident::{
    name: b"x",
    attributes: [Text(b"\xff"), Position(ast_test_span(2))],
    span: ast_test_span(3),
  }
  let qualified = Qdot(Qident(left), right)
  guard qualified is Qdot(Qident(actual_left), actual_right) else {
    fail("expected qualified identifier")
  }
  assert_eq(actual_left.span, ast_test_span(0))
  assert_eq(actual_right.span, ast_test_span(3))
  assert_true(actual_right.attributes[0] is Text(bytes) && bytes == b"\xff")
}

///|
test "AST types: tuple, paren, pure, ref, arrow, and scope stay explicit" {
  let ident = ast_test_ident(b"t", 0)
  let variable = PTtyvar(ident)
  let path = Qident(ast_test_ident(b"M", 1))
  let ty = PTarrow(
    PTref([PTparen(variable)]),
    PTscope(path, PTpure(PTtuple([]))),
  )
  assert_true(
    ty is PTarrow(PTref([PTparen(PTtyvar(_))]), PTscope(_, PTpure(PTtuple([])))),
  )
}

///|
test "AST patterns: wrapper span and descriptor are separate" {
  let inner = Pattern::{ desc: Pwild, span: ast_test_span(1) }
  let parenthesized = Pattern::{ desc: Pparen(inner), span: ast_test_span(3) }
  let outer = Pattern::{ desc: Pghost(parenthesized), span: ast_test_span(4) }
  assert_eq(outer.span, ast_test_span(4))
  guard outer.desc is Pghost(actual_parenthesized) &&
    actual_parenthesized.desc is Pparen(actual_inner) else {
    fail("expected ghost parenthesized pattern")
  }
  assert_true(actual_inner.desc is Pwild)
}

///|
test "AST binders: anonymous untyped Ptree binders remain representable" {
  let span = ast_test_span(0)
  let anonymous = make_binder(span, None, false, None)
  assert_true(anonymous.ident is None)
  assert_true(anonymous.binder_type is None)
  let named = make_binder(span, Some(ast_test_ident(b"x", 0)), false, None)
  guard named.ident is Some(identifier) else { fail("expected named binder") }
  assert_eq(identifier.name, b"x")
  let param = Param::{ span, ident: None, ghost: true, param_type: PTtuple([]) }
  assert_true(param.param_type is PTtuple([]))
}

///|
fn type_error(input : BytesView) -> ParseDiagnostic {
  try parse_type_entry(input) catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected type parser error")
  }
}

///|
fn binder_error(input : BytesView) -> ParseDiagnostic {
  try parse_binders_entry(input) catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected binder parser error")
  }
}

///|
fn param_error(input : BytesView) -> ParseDiagnostic {
  try parse_params_entry(input) catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected parameter parser error")
  }
}

///|
fn pattern_error(
  input : BytesView,
  let_pattern? : Bool = false,
) -> ParseDiagnostic {
  try {
    if let_pattern {
      ignore(parse_let_pattern_entry(input))
    } else {
      ignore(parse_pattern_entry(input))
    }
    abort("expected pattern parser error")
  } catch {
    ParseError(diagnostic) => diagnostic
  }
}

///|
test "type parser: unit, tuple, paren, pure, and every scoped block stay explicit" {
  assert_true(parse_type_entry(b"()") is PTtuple([]))
  assert_true(
    parse_type_entry(b"(a,b,'c)")
    is PTtuple(
      [
        PTtyapp(Qident({ name: b"a", .. }), []),
        PTtyapp(Qident({ name: b"b", .. }), []),
        PTtyvar({ name: b"c", .. }),
      ]
    ),
  )
  assert_true(
    parse_type_entry(b"(a)") is PTparen(PTtyapp(Qident({ name: b"a", .. }), [])),
  )
  assert_true(
    parse_type_entry(b"{a}") is PTpure(PTtyapp(Qident({ name: b"a", .. }), [])),
  )
  assert_true(parse_type_entry(b"M.()") is PTscope(_, PTtuple([])))
  assert_true(parse_type_entry(b"M.(a)") is PTscope(_, PTparen(_)))
  assert_true(parse_type_entry(b"M.(a,b)") is PTscope(_, PTtuple([_, _])))
  assert_true(parse_type_entry(b"M.{a}") is PTscope(_, PTpure(_)))
}

///|
test "type parser: application is greedy and arrows associate to the right" {
  let ty = parse_type_entry(b"a b c -> d -> e")
  guard ty
    is PTarrow(
      PTtyapp(Qident(head), [arg_b, arg_c]),
      PTarrow(PTtyapp(Qident(d), []), PTtyapp(Qident(e), []))
    ) else {
    fail("expected application followed by right-associated arrows")
  }
  assert_eq(head.name, b"a")
  assert_true(arg_b is PTtyapp(Qident({ name: b"b", .. }), []))
  assert_true(arg_c is PTtyapp(Qident({ name: b"c", .. }), []))
  assert_eq((d.name, e.name), (b"d", b"e"))
  assert_true(
    parse_type_entry(b"M.N.t 'a")
    is PTtyapp(
      Qdot(
        Qdot(Qident({ name: b"M", .. }), { name: b"N", .. }),
        { name: b"t", .. }
      ),
      [PTtyvar({ name: b"a", .. })]
    ),
  )
}

///|
test "type parser: malformed blocks and trailing input are structured syntax errors" {
  assert_true(type_error(b"(a,)").kind is UnexpectedToken)
  assert_true(type_error(b"M.").kind is UnexpectedEof)
  let trailing = type_error(b"a b : c")
  assert_true(trailing.kind is UnexpectedToken)
  assert_eq(trailing.span.start.byte_offset, 4)
  let parser = Parser::new(b"(())", max_nesting=1)
  try finish_internal_entry(parser, parser => parser.parse_ty()) catch {
    ParseError(diagnostic) => assert_true(diagnostic.kind is NestingTooDeep)
  } noraise {
    _ => fail("expected parser nesting limit")
  }
}

///|
fn make_nested_source(
  prefix : String,
  atom : String,
  suffix : String,
  depth : Int,
) -> Bytes {
  let builder = StringBuilder(
    size_hint=(prefix.length() + suffix.length()) * depth + atom.length(),
  )
  for index = 0; index < depth; index = index + 1 {
    builder.write_string(prefix)
  }
  builder.write_string(atom)
  for index = 0; index < depth; index = index + 1 {
    builder.write_string(suffix)
  }
  @utf8.encode(builder.to_string())
}

///|
fn assert_explicit_nesting_limit(
  prefix : String,
  atom : String,
  suffix : String,
  parse : (Parser) -> Unit raise,
) -> Unit raise {
  let limit = 8
  for depth in [limit - 1, limit] {
    let parser = Parser::new(
      make_nested_source(prefix, atom, suffix, depth),
      max_nesting=limit,
    )
    finish_internal_entry(parser, parse)
    assert_eq(parser.nesting_depth, 0)
  }
  let parser = Parser::new(
    make_nested_source(prefix, atom, suffix, limit + 1),
    max_nesting=limit,
  )
  try finish_internal_entry(parser, parse) catch {
    ParseError(diagnostic) => assert_true(diagnostic.kind is NestingTooDeep)
  } noraise {
    _ => fail("expected explicit nesting-budget failure")
  }
  assert_eq(parser.nesting_depth, 0)
}

///|
test "nesting budget covers type, pattern, term, expression, scope, and control recursion" {
  assert_explicit_nesting_limit("(", "t", ")", parser => {
    ignore(parser.parse_ty())
  })
  assert_explicit_nesting_limit("(", "x", ")", parser => {
    ignore(parser.parse_pattern())
  })
  assert_explicit_nesting_limit("(", "true", ")", parser => {
    ignore(parser.parse_term())
  })
  assert_explicit_nesting_limit("(", "true", ")", parser => {
    ignore(parser.parse_expr())
  })
  assert_explicit_nesting_limit("scope S ", "", "end ", parser => {
    ignore(parser.parse_mlw_file())
  })
  assert_explicit_nesting_limit("if true then ", "true", "", parser => {
    ignore(parser.parse_expr())
  })

  let default_limited = Parser::new(
    make_nested_source("(", "t", ")", DEFAULT_MAX_NESTING + 1),
  )
  try
    finish_internal_entry(default_limited, parser => ignore(parser.parse_ty()))
  catch {
    ParseError(diagnostic) => assert_true(diagnostic.kind is NestingTooDeep)
  } noraise {
    _ => fail("expected default nesting-budget failure")
  }
  assert_eq(default_limited.nesting_depth, 0)
}

///|
test "ten thousand nested comments use the iterative lexer depth counter" {
  let source = make_nested_source("(*", "", "*)", 10000) + b"true"
  let parser = Parser::new(source)
  let term = finish_internal_entry(parser, parser => parser.parse_term())
  assert_true(term.desc is Ttrue)
  assert_eq(parser.nesting_depth, 0)
  assert_eq(parser.lexer.cursor.comment_depth, 0)
  assert_eq(parser.lexer.cursor.byte_advance_count, source.length())
}

///|
test "binder and param: bare type/name token shapes have distinct interpretations" {
  let params = parse_params_entry(b"x")
  assert_eq(params.length(), 1)
  assert_true(params[0].ident is None)
  assert_true(params[0].param_type is PTtyapp(Qident({ name: b"x", .. }), []))
  let binders = parse_binders_entry(b"x")
  assert_eq(binders.length(), 1)
  assert_true(binders[0].ident is Some({ name: b"x", .. }))
  assert_true(binders[0].binder_type is None)
  assert_true(
    parse_params_entry(b"(x)")[0].param_type
    is PTparen(PTtyapp(Qident({ name: b"x", .. }), [])),
  )
  assert_true(parse_binders_entry(b"(x)")[0].ident is Some({ name: b"x", .. }))
  assert_true(
    parse_binders_entry(b"x'a")[0].ident is Some({ name: b"x'a", .. }),
  )
}

///|
test "binder and param: special and attributed names diverge exactly at semantics" {
  assert_true(param_error(b"_").kind is UndeterminedParameterType)
  let anonymous = parse_binders_entry(b"_")
  assert_eq(anonymous.length(), 1)
  assert_true(anonymous[0].ident is None)
  assert_true(anonymous[0].binder_type is None)
  assert_true(param_error(b"&x").kind is UndeterminedParameterType)
  let referenced = parse_binders_entry(b"&x")[0]
  guard referenced.ident is Some(ident) else {
    fail("expected reference binder")
  }
  assert_true(is_reference_ident(ident))
  assert_true(param_error(b"x [@a]").kind is UndeterminedParameterType)
  let attributed = parse_binders_entry(b"x [@a]")[0]
  assert_true(attributed.ident is Some({ attributes: [Text(b"a")], .. }))
}

///|
test "binder and param: typed, ghost, and ref groups share their token grammar" {
  let binders = parse_binders_entry(b"(x y : t)")
  assert_eq(binders.length(), 2)
  assert_true(binders[0].ident is Some({ name: b"x", .. }))
  assert_true(binders[1].ident is Some({ name: b"y", .. }))
  assert_true(
    binders[0].binder_type is Some(PTtyapp(Qident({ name: b"t", .. }), [])),
  )
  let params = parse_params_entry(b"(ghost x y : t)")
  assert_eq(params.length(), 2)
  assert_true(params[0].ghost && params[1].ghost)
  let referenced = parse_binders_entry(b"(ref x y : t)")
  assert_true(referenced[0].binder_type is Some(PTref([_])))
  guard referenced[0].ident is Some(first) &&
    referenced[1].ident is Some(second) else {
    fail("expected named reference binders")
  }
  assert_true(is_reference_ident(first) && is_reference_ident(second))
  let inferred_ref = parse_binders_entry(b"(ref x)")
  assert_true(inferred_ref[0].binder_type is None)
  assert_true(inferred_ref[0].ident is Some(ident) && is_reference_ident(ident))
  let ghost_type = parse_params_entry(b"(ghost t)")
  assert_true(ghost_type[0].ghost && ghost_type[0].ident is None)
  assert_true(
    ghost_type[0].param_type is PTtyapp(Qident({ name: b"t", .. }), []),
  )
  let ghost_binder = parse_binders_entry(b"(ghost t)")
  assert_true(ghost_binder[0].ghost)
  assert_true(ghost_binder[0].ident is Some({ name: b"t", .. }))
  assert_true(param_error(b"(&x)").kind is UndeterminedParameterType)
  assert_true(param_error(b"(ghost &x)").kind is UndeterminedParameterType)
  let typed_params = parse_params_entry(b"(x y : t)")
  assert_eq(typed_params.length(), 2)
  let attributed_group = parse_binders_entry(b"(x [@a] y : t)")
  assert_true(
    attributed_group[0].ident is Some({ attributes: [Text(b"a")], .. }),
  )
  let special_group = parse_binders_entry(b"(_ x : t)")
  assert_eq(special_group.length(), 2)
  assert_true(special_group[0].ident is None)
  assert_true(special_group[0].binder_type is Some(_))
  let core_head = parse_binders_entry(b"(x'a y : t)")
  assert_true(core_head[0].ident is Some({ name: b"x'a", .. }))
  assert_true(binder_error(b"(_ x'a : t)").kind is ReservedCoreIdentifier)
}

///|
test "binder constraints: anonymous/double ref, ref name, and untyped groups fail" {
  assert_true(binder_error(b"(ref _ : t)").kind is AnonymousReference)
  assert_true(binder_error(b"(ref &x : t)").kind is DoubleReference)
  assert_true(binder_error(b"ref").kind is UnexpectedToken)
  assert_true(binder_error(b"(x [@a] y)").kind is UnexpectedEof)
}

///|
test "one-variable binders: sym, var, and ref forms keep their distinct rules" {
  let parser = Parser::new(b"(+) [@a]")
  let symbolic = finish_internal_entry(parser, parser => {
    parser.parse_sym_binder()
  })
  assert_eq(symbolic.name, b"infix +")
  assert_true(symbolic.attributes is [Text(b"a")])
  let parser = Parser::new(b"&x")
  let variable = finish_internal_entry(parser, parser => {
    parser.parse_var_binder_ident()
  })
  assert_true(is_reference_ident(variable))
  let parser = Parser::new(b"x")
  let reference = finish_internal_entry(parser, parser => {
    parser.parse_ref_binder()
  })
  assert_true(is_reference_ident(reference))
  let parser = Parser::new(b"&x")
  try finish_internal_entry(parser, parser => parser.parse_ref_binder()) catch {
    ParseError(diagnostic) => assert_true(diagnostic.kind is DoubleReference)
  } noraise {
    _ => fail("expected explicit double reference")
  }
  let ghost_special = parse_binders_entry(b"(ghost &x)")
  assert_true(ghost_special[0].ghost)
  assert_true(
    ghost_special[0].ident is Some(ident) && is_reference_ident(ident),
  )
}

///|
test "pattern parser: atoms, constructors, scope, records, and parentheses" {
  assert_true(parse_pattern_entry(b"_").desc is Pwild)
  assert_true(parse_pattern_entry(b"()").desc is Ptuple([]))
  assert_true(parse_pattern_entry(b"x").desc is Pvar({ name: b"x", .. }))
  assert_true(parse_pattern_entry(b"C").desc is Papp(_, []))
  assert_true(parse_pattern_entry(b"C x D").desc is Papp(_, [_, _]))
  assert_true(
    parse_pattern_entry(b"M.(x)").desc is Pscope(_, { desc: Pparen(_), .. }),
  )
  let record = parse_pattern_entry(b"{ f = x; M.g = C; }")
  assert_true(record.desc is Prec([(_, _), (_, _)]))
  let parenthesized = parse_pattern_entry(b"(x)")
  assert_true(parenthesized.desc is Pparen({ desc: Pvar(_), .. }))
  assert_eq(
    (parenthesized.span.start.byte_offset, parenthesized.span.end.byte_offset),
    (0, 3),
  )
}

///|
test "pattern precedence: cast binds above ghost, which binds above as" {
  let first = parse_pattern_entry(b"ghost p : t as x")
  assert_true(
    first.desc
    is Pas(
      { desc: Pghost({ desc: Pcast({ desc: Pvar(_), .. }, _), .. }), .. },
      { name: b"x", .. },
      false
    ),
  )
  let second = parse_pattern_entry(b"p as ghost x : t | q")
  assert_true(
    second.desc
    is Por(
      {
        desc: Pcast(
          { desc: Pas({ desc: Pvar(_), .. }, { name: b"x", .. }, true), .. },
          _
        ),
        ..,
      },
      { desc: Pvar({ name: b"q", .. }), .. }
    ),
  )
  assert_true(
    parse_pattern_entry(b"x,y|z").desc is Por({ desc: Ptuple([_, _]), .. }, _),
  )
}

///|
test "pattern parser: let-pattern initial ghost restriction and nq errors" {
  assert_true(parse_pattern_entry(b"ghost x").desc is Pghost(_))
  assert_true(
    pattern_error(b"ghost x", let_pattern=true).kind is UnexpectedToken,
  )
  assert_true(
    parse_let_pattern_entry(b"x, ghost y | ghost z").desc
    is Por(
      { desc: Ptuple([_, { desc: Pghost(_), .. }]), .. },
      { desc: Pghost(_), .. }
    ),
  )
  assert_true(
    parse_let_pattern_entry(b"C x as y : t").desc
    is Pcast({ desc: Pas({ desc: Papp(_, [_]), .. }, _, false), .. }, _),
  )
  assert_true(pattern_error(b"x'a").kind is ReservedCoreIdentifier)
  assert_true(pattern_error(b"&x [@mlw:reference_var]").kind is DoubleReference)
}

///|
test "pattern parser: repeated nonassociative wrappers and trailing tokens fail" {
  assert_true(pattern_error(b"x as y as z").kind is UnexpectedToken)
  assert_true(pattern_error(b"x : t : u").kind is UnexpectedToken)
  let trailing = pattern_error(b"x y")
  assert_true(trailing.kind is UnexpectedToken)
  assert_eq(trailing.span.start.byte_offset, 2)
}

///|
fn parse_type_entry(
  input : BytesView,
  filename? : BytesView = b"<type-test>",
) -> Pty raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => parser.parse_ty())
}

///|
fn parse_binders_entry(
  input : BytesView,
  filename? : BytesView = b"<binder-test>",
) -> Array[Binder] raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => parser.parse_binders())
}

///|
fn parse_params_entry(
  input : BytesView,
  filename? : BytesView = b"<param-test>",
) -> Array[Param] raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => parser.parse_params(true))
}

///|
fn parse_pattern_entry(
  input : BytesView,
  filename? : BytesView = b"<pattern-test>",
) -> Pattern raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => parser.parse_pattern())
}

///|
fn parse_let_pattern_entry(
  input : BytesView,
  filename? : BytesView = b"<let-pattern-test>",
) -> Pattern raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => parser.parse_let_pattern())
}
