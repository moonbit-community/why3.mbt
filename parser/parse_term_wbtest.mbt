// White-box tests for term parsing.

///|
fn term_test_error(input : BytesView) -> ParseDiagnostic {
  try parse_term_entry(input) catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected term parser error")
  }
}

///|
fn term_test_last_name(path : QualId) -> Bytes {
  path.last_ident().name
}

///|
fn term_test_ident_name(term : Term) -> Bytes {
  guard term.desc is Tident(path) else { abort("expected identifier term") }
  term_test_last_name(path)
}

///|
fn term_test_call(term : Term) -> (Bytes, Array[Term]) {
  guard term.desc is Tidapp(path, arguments) else {
    abort("expected direct identifier application")
  }
  (term_test_last_name(path), arguments)
}

///|
test "term atoms and blocks preserve descriptors while delimiters widen spans" {
  assert_true(parse_term_entry(b"true").desc is Ttrue)
  assert_true(parse_term_entry(b"false").desc is Tfalse)
  assert_true(
    parse_term_entry(b"42").desc is Tconst(ConstInt({ value, .. })) &&
    value.compare_int(42) == 0,
  )
  assert_true(parse_term_entry(b"1.5").desc is Tconst(ConstReal(_)))
  assert_true(parse_term_entry(b"\"x\"").desc is Tconst(ConstStr(b"x")))
  assert_true(
    parse_term_entry(b"&x").desc is Tasref(Qident({ name: b"x", .. })),
  )
  assert_true(parse_term_entry(b"()").desc is Ttuple([]))
  assert_true(parse_term_entry(b"begin end").desc is Ttuple([]))
  let parenthesized = parse_term_entry(b"(x)")
  assert_true(parenthesized.desc is Tident(Qident({ name: b"x", .. })))
  assert_eq(parenthesized.span.start.byte_offset, 0)
  assert_eq(parenthesized.span.end.byte_offset, 3)
  let begun = parse_term_entry(b"begin x end")
  assert_true(begun.desc is Tident(Qident({ name: b"x", .. })))
  assert_eq(begun.span.end.byte_offset, 11)
}

///|
test "term record, update, scope, and field application retain distinct AST nodes" {
  let record = parse_term_entry(b"{ f = x; M.g = y; }")
  guard record.desc is Trecord(fields) else { fail("expected term record") }
  assert_eq(fields.length(), 2)
  assert_eq(term_test_last_name(fields[1].0), b"g")
  let update = parse_term_entry(b"{ x with f = y; }")
  guard update.desc is Tupdate(base, fields) else {
    fail("expected term record update")
  }
  assert_eq(term_test_ident_name(base), b"x")
  assert_eq(fields.length(), 1)
  let scoped = parse_term_entry(b"M.(x)")
  guard scoped.desc is Tscope(path, inner) else { fail("expected term scope") }
  assert_eq(term_test_last_name(path), b"M")
  assert_eq(term_test_ident_name(inner), b"x")
  let field = parse_term_entry(b"x.f")
  let (name, arguments) = term_test_call(field)
  assert_eq(name, b"f")
  assert_eq(arguments.length(), 1)
  assert_eq(term_test_ident_name(arguments[0]), b"x")
}

///|
test "term postfix get/update/cut encodings, suffixes, and operator spans are exact" {
  let get = parse_term_entry(b"x[0]''")
  let (name, arguments) = term_test_call(get)
  assert_eq(name, b"mixfix []''")
  assert_eq(arguments.length(), 2)
  guard get.desc is Tidapp(Qident(operator), _) else { fail("expected get") }
  assert_eq(operator.span.start.byte_offset, 1)
  assert_eq(operator.span.end.byte_offset, 2)
  assert_eq(get.span.end.byte_offset, 6)
  let cases : Array[(Bytes, Bytes, Int)] = [
    (b"a[i <- v]", b"mixfix [<-]", 3),
    (b"a[i..j]", b"mixfix [..]", 3),
    (b"a[i..]", b"mixfix [_..]", 2),
    (b"a[..j]", b"mixfix [.._]", 2),
  ]
  for case in cases {
    let (actual_name, actual_arguments) = term_test_call(
      parse_term_entry(case.0),
    )
    assert_eq(actual_name, case.1)
    assert_eq(actual_arguments.length(), case.2)
  }
  assert_true(term_test_error(b"true.f").kind is UnexpectedToken)
  assert_true(parse_term_entry(b"(1).f").desc is Tidapp(_))
}

///|
test "application differs from field sugar and tight prefix binds only one term_arg" {
  let application = parse_term_entry(b"f a b")
  guard application.desc
    is Tapply({ desc: Tapply(function, first), .. }, second) else {
    fail("expected left-associated application")
  }
  assert_eq(term_test_ident_name(function), b"f")
  assert_eq(term_test_ident_name(first), b"a")
  assert_eq(term_test_ident_name(second), b"b")
  let tight = parse_term_entry(b"!f x")
  guard tight.desc is Tapply(prefix_call, tight_second) else {
    fail("expected application outside tight prefix")
  }
  let (tight_name, tight_arguments) = term_test_call(prefix_call)
  assert_eq(tight_name, b"prefix !")
  assert_eq(tight_arguments.length(), 1)
  assert_eq(term_test_ident_name(tight_arguments[0]), b"f")
  assert_eq(term_test_ident_name(tight_second), b"x")
  let indexed = parse_term_entry(b"!x[0]")
  let (indexed_name, indexed_arguments) = term_test_call(indexed)
  assert_eq(indexed_name, b"mixfix []")
  assert_eq(term_test_call(indexed_arguments[0]).0, b"prefix !")
  let ordinary = parse_term_entry(b"- f x")
  let (ordinary_name, ordinary_arguments) = term_test_call(ordinary)
  assert_eq(ordinary_name, b"prefix -")
  assert_eq(ordinary_arguments.length(), 1)
  assert_true(ordinary_arguments[0].desc is Tapply(_))
  assert_true(
    parse_term_entry(b"-42").desc is Tconst(ConstInt({ value, .. })) &&
    value.compare_int(-42) == 0,
  )
}

///|
test "term Pratt precedence, associativity, and relation-chain breaks match Menhir" {
  let arithmetic = parse_term_entry(b"a + b * c")
  let (plus, plus_arguments) = term_test_call(arithmetic)
  assert_eq(plus, b"infix +")
  assert_eq(plus_arguments.length(), 2)
  let (times, _) = term_test_call(plus_arguments[1])
  assert_eq(times, b"infix *")
  let implication = parse_term_entry(b"a -> b -> c")
  assert_true(
    implication.desc
    is Tbinop(_, DTimplies, { desc: Tbinop(_, DTimplies, _), .. }),
  )
  let relation = parse_term_entry(b"a < b < c")
  assert_true(relation.desc is Tinfix(_, _, { desc: Tinfix(_, _, _), .. }))
  assert_true(parse_term_entry(b"(a < b)").desc is Tinnfix(_))
  assert_true(parse_term_entry(b"(p /\\ q)").desc is Tbinnop(_, DTand, _))
  let nested = parse_term_entry(b"(a < b) < c")
  assert_true(nested.desc is Tinfix({ desc: Tinnfix(_), .. }, _, _))
  let negated = parse_term_entry(b"not a = b /\\ c")
  assert_true(
    negated.desc
    is Tbinop({ desc: Tnot({ desc: Tinfix(_, _, _), .. }), .. }, DTand, _),
  )
}

///|
test "term if, pattern let, logic-function let, and match build exact control nodes" {
  let conditional = parse_term_entry(b"if p then a else b")
  assert_true(conditional.desc is Tif(_, _, _))
  let variable_let = parse_term_entry(b"let x = v in b")
  guard variable_let.desc is Tlet(ident, value, body) else {
    fail("expected variable term let")
  }
  assert_eq(ident.name, b"x")
  assert_eq(term_test_ident_name(value), b"v")
  assert_eq(term_test_ident_name(body), b"b")
  let wildcard_let = parse_term_entry(b"let _ = v in b")
  guard wildcard_let.desc is Tlet(wildcard, _, _) else {
    fail("expected wildcard term let")
  }
  assert_eq(wildcard.name, b"_")
  assert_eq(wildcard.span.start.byte_offset, 4)
  let cast_let = parse_term_entry(b"let (x : t) = v in b")
  assert_true(
    cast_let.desc
    is Tlet(
      { name: b"x", .. },
      { desc: Tcast({ desc: Tident(Qident({ name: b"v", .. })), .. }, _), .. },
      _
    ),
  )
  let complex_let = parse_term_entry(b"let (Some x : t) = v in b")
  guard complex_let.desc is Tcase(scrutinee, [(branch_pattern, _)]) else {
    fail("expected complex pattern term case")
  }
  assert_true(scrutinee.desc is Tcast(_, _))
  assert_eq(scrutinee.span.start.byte_offset, 19)
  assert_true(branch_pattern.desc is Pparen({ desc: Pcast(_, _), .. }))
  let function_let = parse_term_entry(b"let f x = x in f")
  assert_true(
    function_let.desc
    is Tlet({ name: b"f", .. }, { desc: Tquant(DTlambda, [_], [], _), .. }, _),
  )
  let matched = parse_term_entry(b"match x with | A -> a | B y -> b end")
  guard matched.desc is Tcase(_, cases) else { fail("expected term match") }
  assert_eq(cases.length(), 2)
  assert_true(cases[0].0.desc is Papp(Qident({ name: b"A", .. }), []))
  assert_true(cases[1].0.desc is Papp(Qident({ name: b"B", .. }), [_]))
}

///|
test "term quantifiers use shared casts and nonempty two-dimensional triggers" {
  let quantified = parse_term_entry(b"forall x y: t, z [f x, g y | h z]. p")
  guard quantified.desc is Tquant(DTforall, binders, triggers, body) else {
    fail("expected quantified term")
  }
  assert_eq(binders.length(), 3)
  assert_true(binders[0].binder_type is Some(PTtyapp(_)))
  assert_true(binders[1].binder_type is Some(PTtyapp(_)))
  assert_true(binders[2].binder_type is None)
  assert_eq(triggers.length(), 2)
  assert_eq(triggers[0].length(), 2)
  assert_eq(triggers[1].length(), 1)
  assert_eq(term_test_ident_name(body), b"p")
  let existential = parse_term_entry(b"exists _: t. true")
  assert_true(
    existential.desc is Tquant(DTexists, [_], [], { desc: Ttrue, .. }),
  )
  let lambda = parse_term_entry(b"fun (x: t) -> x")
  assert_true(lambda.desc is Tquant(DTlambda, [_], [], _))
  let anonymous_lambda = parse_term_entry(b"fun _ -> x")
  assert_true(
    anonymous_lambda.desc
    is Tquant(DTlambda, [{ ident: None, binder_type: None, .. }], [], _),
  )
  assert_true(term_test_error(b"forall x []. p").kind is UnexpectedToken)
  assert_true(term_test_error(b"forall x [| p]. q").kind is UnexpectedToken)
}

///|
test "old, labels, attributes, casts, tuples, and internal list entry stay distinct" {
  let old = parse_term_entry(b"old x")
  guard old.desc is Tat(_, label) else { fail("expected old label") }
  assert_eq(label.name, old_label)
  assert_eq(label.span.start.byte_offset, 0)
  assert_eq(label.span.end.byte_offset, 3)
  let at = parse_term_entry(b"x at L")
  assert_true(at.desc is Tat(_, { name: b"L", .. }))
  assert_true(term_test_error(b"old x at L").kind is UnexpectedToken)
  assert_true(parse_term_entry(b"(old x) at L").desc is Tat(_))
  let attributed = parse_term_entry(b"[@a] x : t")
  assert_true(attributed.desc is Tattr(Text(b"a"), { desc: Tcast(_, _), .. }))
  let tuple = parse_term_entry(b"a, b, c")
  assert_true(tuple.desc is Ttuple([_, _, _]))
  let list = parse_term_list_entry(b"a, b, c")
  assert_eq(list.length(), 3)
  assert_true(list[0].desc is Tident(_))
  assert_true(term_test_error(b"a, b ; c").kind is UnexpectedToken)
}

///|
test "term function literals preserve the final redundant comparison and sequence indices" {
  let one = parse_term_entry(b"[| k => v |]")
  guard one.desc
    is Tattr(
      Text(attribute),
      { desc: Tquant(DTlambda, [binder], [], branch), .. }
    ) else {
    fail("expected attributed term function literal")
  }
  assert_eq(attribute, function_literal_attribute)
  guard binder.ident is Some(identifier) else {
    fail("expected literal binder")
  }
  assert_eq(identifier.name, b"x'x")
  guard branch.desc is Tif(_, consequent, alternative) else {
    fail("expected final redundant function-literal branch")
  }
  assert_eq(consequent, alternative)
  let default_only = parse_term_entry(b"[| _ => d |]")
  guard default_only.desc
    is Tattr(
      _,
      { desc: Tquant(DTlambda, [default_binder], [], default_body), .. }
    ) else {
    fail("expected default-only function literal")
  }
  guard default_binder.ident is Some(default_ident) else {
    fail("expected default binder")
  }
  assert_eq(default_ident.name, b"_")
  assert_eq(term_test_ident_name(default_body), b"d")
  let sequence = parse_term_entry(b"[| a; b |]")
  guard sequence.desc
    is Tattr(
      _,
      { desc: Tquant(_, _, _, { desc: Tif(condition, _, _), .. }), .. }
    ) else {
    fail("expected sequence function literal")
  }
  guard condition.desc is Tinfix(_, _, { desc: Tconst(ConstInt(index)), .. }) else {
    fail("expected synthesized decimal index")
  }
  assert_true(index.kind is ILitDec)
  assert_eq(index.value.compare_int(0), 0)
  let mapped = parse_term_entry(b"[| k => v; _ => d |]")
  assert_true(
    mapped.desc
    is Tattr(_, { desc: Tquant(_, _, _, { desc: Tif(_, _, _), .. }), .. }),
  )
}

///|
test "unsupported epsilon and non-associative postfixes report structured errors" {
  let epsilon = term_test_error(b"epsilon")
  assert_true(epsilon.kind is UnsupportedEpsilon)
  assert_eq(epsilon.span.start.byte_offset, 0)
  assert_eq(epsilon.span.end.byte_offset, 7)
  assert_true(term_test_error(b"x : t : u").kind is UnexpectedToken)
  assert_true(term_test_error(b"x at L at M").kind is UnexpectedToken)
  assert_true(
    parse_term_entry(b"x at L + x at M").desc
    is Tat(
      {
        desc: Tidapp(
          Qident({ name: b"infix +", .. }),
          [{ desc: Tat(_, { name: b"L", .. }), .. }, _]
        ),
        ..,
      },
      { name: b"M", .. }
    ),
  )
}

///|
test "every logical operator maps to its exact BinaryLogicOp constructor" {
  let cases : Array[(Bytes, BinaryLogicOp)] = [
    (b"a -> b", DTimplies),
    (b"a <-> b", DTiff),
    (b"a \\/ b", DTor),
    (b"a || b", DTorAsym),
    (b"a /\\ b", DTand),
    (b"a && b", DTandAsym),
    (b"a by b", DTby),
    (b"a so b", DTso),
  ]
  for case in cases {
    guard parse_term_entry(case.0).desc is Tbinop(_, actual, _) else {
      fail("expected logical binary term")
    }
    assert_eq(actual, case.1)
  }
  assert_true(
    parse_term_entry(b"a \\/ b \\/ c").desc
    is Tbinop(_, DTor, { desc: Tbinop(_, DTor, _), .. }),
  )
  assert_true(
    parse_term_entry(b"a by b so c").desc
    is Tbinop(_, DTby, { desc: Tbinop(_, DTso, _), .. }),
  )
}

///|
test "relation and OP2-OP4 layers map names and preserve right/left association" {
  let relations : Array[(Bytes, Bytes)] = [
    (b"a = b", b"infix ="),
    (b"a <> b", b"infix <>"),
    (b"a < b", b"infix <"),
    (b"a > b", b"infix >"),
    (b"a ~= b", b"infix ~="),
  ]
  for case in relations {
    guard parse_term_entry(case.0).desc is Tinfix(_, operator, _) else {
      fail("expected relation term")
    }
    assert_eq(operator.name, case.1)
  }
  let arithmetic : Array[(Bytes, Bytes)] = [
    (b"a - b", b"infix -"),
    (b"a + b", b"infix +"),
    (b"a * b", b"infix *"),
    (b"a ^ b", b"infix ^"),
  ]
  for case in arithmetic {
    let (operator, _) = term_test_call(parse_term_entry(case.0))
    assert_eq(operator, case.1)
  }
  let left = parse_term_entry(b"a + b + c")
  guard left.desc is Tidapp(_, [left_operand, _]) else {
    fail("expected left-associated OP2 term")
  }
  assert_true(left_operand.desc is Tidapp(_))
  let old_arithmetic = parse_term_entry(b"old a + b = c")
  assert_true(
    old_arithmetic.desc
    is Tinfix({ desc: Tat({ desc: Tidapp(_, [_, _]), .. }, _), .. }, _, _),
  )
}

///|
test "all scoped blocks and mixed postfix chains remain grammar-constrained" {
  assert_true(
    parse_term_entry(b"M.()").desc is Tscope(_, { desc: Ttuple([]), .. }),
  )
  assert_true(
    parse_term_entry(b"M.(x, y)").desc
    is Tscope(_, { desc: Ttuple([_, _]), .. }),
  )
  assert_true(
    parse_term_entry(b"M.{ f = x }").desc is Tscope(_, { desc: Trecord(_), .. }),
  )
  assert_true(
    parse_term_entry(b"M.begin x end").desc
    is Tscope(_, { desc: Tident(_), .. }),
  )
  assert_true(
    parse_term_entry(b"(+)").desc is Tident(Qident({ name: b"infix +", .. })),
  )
  let chain = parse_term_entry(b"x.f[0].g[..n]")
  let (outer_name, outer_arguments) = term_test_call(chain)
  assert_eq(outer_name, b"mixfix [.._]")
  assert_eq(outer_arguments.length(), 2)
  let (field_name, _) = term_test_call(outer_arguments[0])
  assert_eq(field_name, b"g")
  assert_true(parse_term_entry(b"true[0]").desc is Tidapp(_))
  assert_true(term_test_error(b"&x.f").kind is UnexpectedToken)
  assert_true(term_test_error(b"[|x|].f").kind is UnexpectedToken)
}

///|
test "trigger syntax rejects empty and leading-bar forms without flattening commas" {
  assert_true(term_test_error(b"forall x []. p").kind is UnexpectedToken)
  assert_true(term_test_error(b"forall x [ | p ]. q").kind is UnexpectedToken)
  let trigger = parse_term_entry(b"forall x [f x, g x | h x]. p")
  guard trigger.desc is Tquant(_, _, groups, _) else {
    fail("expected quantified trigger")
  }
  assert_eq(groups.length(), 2)
  assert_eq(groups[0].length(), 2)
  assert_true(groups[0][0].desc is Tapply(_))
  assert_true(groups[0][1].desc is Tapply(_))
}
