// White-box tests for specification and expression parsing.

///|
fn spec_test_error(input : BytesView) -> ParseDiagnostic {
  try parse_spec_entry(input) catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected specification parser error")
  }
}

///|
fn spec_test_hypothesis_name(term : Term) -> Bytes {
  guard term.desc is Tattr(Text(name), _) else {
    abort("expected named specification term")
  }
  name
}

///|
fn spec_test_ident_name(term : Term) -> Bytes {
  guard term.desc is Tident(Qident(ident)) else {
    abort("expected unqualified identifier term")
  }
  ident.name
}

///|
fn spec_test_return_opt(input : BytesView) -> (Pattern, Pty?, Mask) raise {
  let parser = Parser::new(input, filename=b"<return-opt-test>")
  finish_internal_entry(parser, parser => parser.parse_return_opt())
}

///|
test "specification union preserves clause order, booleans, and check-rw state" {
  let spec = parse_spec_entry(
    b"requires first {p} requires {q} ensures named {r} returns { | x -> s | _ -> t } reads {x,M.y} writes {w,f z} alias {a with b} diverges variant {v with rel,u}",
  )
  assert_eq(spec.preconditions.length(), 2)
  assert_eq(spec_test_hypothesis_name(spec.preconditions[0]), b"hyp_name:first")
  assert_eq(
    spec_test_hypothesis_name(spec.preconditions[1]),
    b"hyp_name:Requires",
  )
  assert_eq(spec.postconditions.length(), 2)
  assert_eq(
    spec_test_hypothesis_name(spec.postconditions[0].branches[0].1),
    b"hyp_name:named",
  )
  assert_eq(spec.postconditions[1].branches.length(), 2)
  assert_eq(spec.reads.length(), 2)
  assert_eq(spec.writes.length(), 2)
  assert_eq(spec.aliases.length(), 1)
  assert_eq(spec.variant.items.length(), 2)
  assert_eq(
    spec_test_hypothesis_name(spec.variant.items[0].0),
    b"hyp_name:Variant",
  )
  assert_true(spec.variant.items[0].1 is Some(Qident({ name: b"rel", .. })))
  assert_true(spec.check_reads_writes)
  assert_true(spec.diverges)
  assert_false(spec.partial)
}

///|
test "duplicate variants report the first term of the second clause" {
  let diagnostic = spec_test_error(b"variant {a} variant {b,c}")
  assert_true(diagnostic.kind is DuplicateVariant)
  assert_eq(diagnostic.span.start.byte_offset, 21)
  assert_eq(diagnostic.span.end.byte_offset, 22)
}

///|
test "ensures, returns, and both raises forms retain their exact branch shapes" {
  let spec = parse_spec_entry(
    b"ensures {ok} returns { | x -> px | _ -> pw } raises { E -> pe | F x -> pf } raises { G,H }",
  )
  assert_eq(spec.postconditions.length(), 2)
  let ensures = spec.postconditions[0]
  guard ensures.branches is [({ desc: Pvar(result), .. }, ensures_term)] else {
    fail("expected synthesized ensures result branch")
  }
  assert_eq(result.name, b"result")
  assert_eq(ensures.span, result.span)
  assert_eq(spec_test_hypothesis_name(ensures_term), b"hyp_name:Ensures")
  let returns = spec.postconditions[1]
  assert_eq(returns.branches.length(), 2)
  assert_true(returns.branches[0].0.desc is Pvar({ name: b"x", .. }))
  assert_true(returns.branches[1].0.desc is Pwild)
  assert_eq(spec.exceptional_postconditions.length(), 2)
  let with_terms = spec.exceptional_postconditions[0]
  guard with_terms.branches
    is [
      (Qident({ name: b"E", .. }), Some((unit_pattern, e_term))),
      (Qident({ name: b"F", .. }), Some((argument_pattern, f_term))),
    ] else {
    fail("expected patterned exception postconditions")
  }
  assert_true(unit_pattern.desc is Ptuple([]))
  assert_true(argument_pattern.desc is Pvar({ name: b"x", .. }))
  assert_eq(spec_test_ident_name(e_term), b"pe")
  assert_eq(spec_test_ident_name(f_term), b"pf")
  let symbols = spec.exceptional_postconditions[1]
  assert_true(
    symbols.branches
    is [(Qident({ name: b"G", .. }), None), (Qident({ name: b"H", .. }), None)],
  )
  let leading_bars = parse_spec_entry(
    b"returns { | x -> p } raises { | E -> q }",
  )
  assert_eq(leading_bars.postconditions[0].span.start.byte_offset, 10)
  assert_eq(leading_bars.postconditions[0].span.end.byte_offset, 18)
  assert_eq(
    leading_bars.exceptional_postconditions[0].span.start.byte_offset,
    30,
  )
  assert_eq(leading_bars.exceptional_postconditions[0].span.end.byte_offset, 38)
}

///|
test "loop and type invariants use distinct defaults and explicit names override them" {
  let loop_parser = Parser::new(b"invariant {p}")
  let loop_invariant = finish_internal_entry(loop_parser, parser => {
    parser.parse_loop_invariant()
  })
  assert_eq(
    spec_test_hypothesis_name(loop_invariant),
    b"hyp_name:LoopInvariant",
  )
  let type_parser = Parser::new(b"invariant {q}")
  let type_invariant = finish_internal_entry(type_parser, parser => {
    parser.parse_type_invariant()
  })
  assert_eq(
    spec_test_hypothesis_name(type_invariant),
    b"hyp_name:TypeInvariant",
  )
  let named_parser = Parser::new(b"invariant stable {r}")
  let named = finish_internal_entry(named_parser, parser => {
    parser.parse_loop_invariant()
  })
  assert_eq(spec_test_hypothesis_name(named), b"hyp_name:stable")
}

///|
test "return grammar distinguishes wildcard, named, tuple-type, and mixed masks" {
  let (omitted_pattern, omitted_type, omitted_mask) = spec_test_return_opt(b"")
  assert_true(omitted_pattern.desc is Pwild)
  assert_true(omitted_type is None)
  assert_true(omitted_mask is MaskVisible)
  let (bare_pattern, bare_type, bare_mask) = parse_return_named_entry(b"t")
  assert_true(bare_pattern.desc is Pwild)
  assert_true(bare_type is PTtyapp(Qident({ name: b"t", .. }), []))
  assert_true(bare_mask is MaskVisible)
  let (ghost_pattern, ghost_type, ghost_mask) = parse_return_named_entry(
    b"(ghost t)",
  )
  assert_true(ghost_pattern.desc is Pwild)
  assert_true(ghost_type is PTtyapp(Qident({ name: b"t", .. }), []))
  assert_true(ghost_mask is MaskGhost)
  let (tuple_pattern, tuple_type, tuple_mask) = parse_return_named_entry(
    b"(t,u)",
  )
  assert_true(tuple_pattern.desc is Pwild)
  assert_true(tuple_type is PTtuple([_, _]))
  assert_true(tuple_mask is MaskVisible)
  let (mixed_pattern, mixed_type, mixed_mask) = parse_return_named_entry(
    b"(t,ghost u)",
  )
  assert_true(mixed_pattern.desc is Pwild)
  assert_true(mixed_type is PTtuple([_, _]))
  assert_true(mixed_mask is MaskTuple([MaskVisible, MaskGhost]))
}

///|
test "named return slots preserve explicit underscore and unused-variable attributes" {
  let (named_pattern, named_type, named_mask) = parse_return_named_entry(
    b"(x:t)",
  )
  guard named_pattern.desc is Pvar(named_ident) else {
    fail("expected named return pattern")
  }
  assert_eq(named_ident.name, b"x")
  assert_true(
    named_ident.attributes is [Text(attribute)] &&
    attribute == unused_variable_attribute,
  )
  assert_true(named_type is PTtyapp(Qident({ name: b"t", .. }), []))
  assert_true(named_mask is MaskVisible)
  let (underscore_pattern, _, _) = parse_return_named_entry(b"(_:t)")
  guard underscore_pattern.desc is Pvar(underscore) else {
    fail("expected explicit underscore return pattern")
  }
  assert_eq(underscore.name, b"_")
  assert_eq(underscore.attributes, [])
  let (tuple_pattern, tuple_type, tuple_mask) = parse_return_named_entry(
    b"(ghost x:t,y:u)",
  )
  assert_true(tuple_pattern.desc is Ptuple([_, _]))
  assert_true(tuple_type is PTtuple([_, _]))
  assert_true(tuple_mask is MaskTuple([MaskGhost, MaskVisible]))
}

///|
test "apply_return rewrites only canonical synthesized ensures branches" {
  let (explicit, _, _) = parse_return_named_entry(b"(x:t)")
  let canonical = parse_spec_entry(b"ensures {ok}")
  let rewritten = apply_return(explicit, canonical)
  assert_eq(rewritten.postconditions[0].branches[0].0, explicit)
  let (wildcard, _, _) = parse_return_named_entry(b"t")
  assert_eq(apply_return(wildcard, canonical), canonical)
  let multiple = parse_spec_entry(b"returns { | x -> p | y -> q }")
  assert_eq(apply_return(explicit, multiple), multiple)
  let noncanonical = parse_spec_entry(b"returns { result -> p }")
  assert_eq(apply_return(explicit, noncanonical), noncanonical)
  let original_post = canonical.postconditions[0]
  let mismatched = {
    ..canonical,
    postconditions: [
      { ..original_post, span: Span::empty(original_post.span.start) },
    ],
  }
  assert_eq(apply_return(explicit, mismatched), mismatched)
}

///|
fn expr_test_error(input : BytesView) -> ParseDiagnostic {
  try parse_expr_entry(input) catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected program-expression parser error")
  }
}

///|
fn expr_test_last_name(path : QualId) -> Bytes {
  path.last_ident().name
}

///|
fn expr_test_ident_name(expression : Expr) -> Bytes {
  guard expression.desc is Eident(path) else {
    abort("expected identifier expression")
  }
  expr_test_last_name(path)
}

///|
fn expr_test_direct_call(expression : Expr) -> (Bytes, Array[Expr]) {
  guard expression.desc is Eidapp(path, arguments) else {
    abort("expected direct identifier application")
  }
  (expr_test_last_name(path), arguments)
}

///|
test "expression atoms, blocks, records, scopes, and pure symbols remain distinct" {
  assert_true(parse_expr_entry(b"true").desc is Etrue)
  assert_true(parse_expr_entry(b"false").desc is Efalse)
  assert_true(parse_expr_entry(b"42").desc is Econst(ConstInt(_)))
  assert_true(parse_expr_entry(b"1.5").desc is Econst(ConstReal(_)))
  assert_true(parse_expr_entry(b"\"x\"").desc is Econst(ConstStr(b"x")))
  assert_true(
    parse_expr_entry(b"&x").desc is Easref(Qident({ name: b"x", .. })),
  )
  assert_true(parse_expr_entry(b"()").desc is Etuple([]))
  let parenthesized = parse_expr_entry(b"(x)")
  assert_true(parenthesized.desc is Eident(_))
  assert_eq(parenthesized.span.end.byte_offset, 3)
  assert_true(parse_expr_entry(b"begin end").desc is Etuple([]))
  let record = parse_expr_entry(b"{ f = x; M.g = y; }")
  assert_true(record.desc is Erecord([_, _]))
  let update = parse_expr_entry(b"{ x with f = y; }")
  assert_true(update.desc is Eupdate({ desc: Eident(_), .. }, [_]))
  assert_true(parse_expr_entry(b"M.(x)").desc is Escope(_, _))
  assert_true(parse_expr_entry(b"x.f").desc is Eidapp(_, [_]))
  assert_true(
    parse_expr_entry(b"{f}").desc is Eidpur(Qident({ name: b"f", .. })),
  )
  assert_true(
    parse_expr_entry(b"M.{f}").desc
    is Eidpur(Qdot(Qident({ name: b"M", .. }), { name: b"f", .. })),
  )
  assert_true(
    parse_expr_entry(b"x.{f}").desc
    is Eapply({ desc: Eidpur(Qident({ name: b"f", .. })), .. }, _),
  )
  assert_true(
    parse_expr_entry(b"pure {p}").desc is Epure({ desc: Tident(_), .. }),
  )
}

///|
test "expression postfix operators preserve every mixfix spelling and suffix" {
  let get = parse_expr_entry(b"a[i]''")
  let (get_name, get_arguments) = expr_test_direct_call(get)
  assert_eq(get_name, b"mixfix []''")
  assert_eq(get_arguments.length(), 2)
  let cases : Array[(Bytes, Bytes, Int)] = [
    (b"a[i <- v]", b"mixfix [<-]", 3),
    (b"a[i..j]", b"mixfix [..]", 3),
    (b"a[i..]", b"mixfix [_..]", 2),
    (b"a[..j]", b"mixfix [.._]", 2),
  ]
  for case in cases {
    let (name, arguments) = expr_test_direct_call(parse_expr_entry(case.0))
    assert_eq(name, case.1)
    assert_eq(arguments.length(), case.2)
  }
  assert_true(expr_test_error(b"true.f").kind is UnexpectedToken)
  assert_true(parse_expr_entry(b"(1).f").desc is Eidapp(_))
}

///|
test "expression application and Pratt precedence match program operators" {
  let application = parse_expr_entry(b"f a b")
  assert_true(
    application.desc
    is Eapply({ desc: Eapply({ desc: Eident(_), .. }, _), .. }, _),
  )
  let tight = parse_expr_entry(b"!f x")
  guard tight.desc is Eapply(prefix, second) else {
    fail("expected application outside tight prefix")
  }
  assert_eq(expr_test_direct_call(prefix).0, b"prefix !")
  assert_eq(expr_test_ident_name(second), b"x")
  let indexed = parse_expr_entry(b"!x[0]")
  let (indexed_name, indexed_arguments) = expr_test_direct_call(indexed)
  assert_eq(indexed_name, b"mixfix []")
  assert_eq(expr_test_direct_call(indexed_arguments[0]).0, b"prefix !")
  let ordinary = parse_expr_entry(b"- f x")
  assert_eq(expr_test_direct_call(ordinary).0, b"prefix -")
  assert_true(expr_test_direct_call(ordinary).1[0].desc is Eapply(_))
  assert_true(parse_expr_entry(b"-42").desc is Econst(ConstInt(_)))
  let logic = parse_expr_entry(b"not a = b && c || d")
  assert_true(
    logic.desc
    is Eor(
      { desc: Eand({ desc: Enot({ desc: Einfix(_, _, _), .. }), .. }, _), .. },
      _
    ),
  )
  let arithmetic = parse_expr_entry(b"a + b * c")
  assert_eq(expr_test_direct_call(arithmetic).0, b"infix +")
  assert_eq(
    expr_test_direct_call(expr_test_direct_call(arithmetic).1[1]).0,
    b"infix *",
  )
  assert_true(
    parse_expr_entry(b"a < b < c").desc
    is Einfix(_, _, { desc: Einfix(_, _, _), .. }),
  )
  assert_true(parse_expr_entry(b"(a < b)").desc is Einnfix(_))
  assert_true(parse_expr_entry(b"x : t").desc is Ecast(_, _))
}

///|
test "tuples, right-associated sequences, and the two contract wrappers differ" {
  assert_true(parse_expr_entry(b"a,b,c").desc is Etuple([_, _, _]))
  let sequence = parse_expr_entry(b"a;b;c")
  assert_true(sequence.desc is Esequence(_, { desc: Esequence(_, _), .. }))
  assert_eq(parse_expr_entry(b"a;"), parse_expr_entry(b"a"))
  let trailing = parse_expr_entry(b"x requires {p} ensures {q}")
  guard trailing.desc
    is Eattr(Text(attribute), { desc: Efun([], _, _, _, spec, body), .. }) else {
    fail("expected white-box trailing contract")
  }
  assert_eq(attribute, white_box_attribute)
  assert_eq(spec.preconditions.length(), 1)
  assert_eq(spec.postconditions.length(), 1)
  assert_eq(expr_test_ident_name(body), b"x")
  let block = parse_expr_entry(b"begin requires {p} x end")
  guard block.desc is Efun([], _, _, _, block_spec, block_body) else {
    fail("expected begin contract function")
  }
  assert_eq(block_spec.preconditions.length(), 1)
  assert_eq(expr_test_ident_name(block_body), b"x")
  let empty_block = parse_expr_entry(b"begin ensures {p} end")
  guard empty_block.desc
    is Efun([], _, _, _, _, { desc: Etuple([]), span: unit_span }) else {
    fail("expected empty contract block body")
  }
  assert_eq(unit_span, empty_block.span)
}

///|
test "ordinary and parallel assignments lower all valid lvalue shapes" {
  let reference = parse_expr_entry(b"x <- v")
  assert_true(
    reference.desc
    is Eassign(
      [
        {
          target: { desc: Easref(Qident({ name: b"x", .. })), .. },
          field: None,
          ..,
        },
      ]
    ),
  )
  let field = parse_expr_entry(b"x.f <- v")
  assert_true(
    field.desc
    is Eassign(
      [
        {
          target: { desc: Eident(Qident({ name: b"x", .. })), .. },
          field: Some(Qident({ name: b"f", .. })),
          ..,
        },
      ]
    ),
  )
  let prefix = parse_expr_entry(b"!x <- v")
  assert_true(
    prefix.desc
    is Eassign([{ field: Some(Qident({ name: b"prefix !", .. })), .. }]),
  )
  let array = parse_expr_entry(b"a[i] <- v")
  assert_true(
    array.desc is Eidapp(Qident({ name: b"mixfix []<-", .. }), [_, _, _]),
  )
  let parallel = parse_expr_entry(b"[@a] x, [@b] y <- u,v")
  guard parallel.desc
    is Eattr(
      Text(b"a"),
      { desc: Eattr(Text(b"b"), { desc: Eassign(items), .. }), .. }
    ) else {
    fail("expected hoisted parallel-assignment attrs")
  }
  assert_eq(items.length(), 2)
  assert_true(items[0].target.desc is Easref(_))
  assert_true(items[1].target.desc is Easref(_))
  assert_true(
    parse_expr_entry(b"x <- (u,v)").desc
    is Eassign([{ value: { desc: Etuple([_, _]), .. }, .. }]),
  )
}

///|
test "assignment errors distinguish invalid targets from invalid parallel structure" {
  assert_true(expr_test_error(b"true <- v").kind is InvalidAssignment)
  assert_true(expr_test_error(b"x,y <- v").kind is InvalidParallelAssignment)
  assert_true(
    expr_test_error(b"x,y <- u,v,w").kind is InvalidParallelAssignment,
  )
  assert_true(
    expr_test_error(b"a[i],x <- u,v").kind is InvalidParallelAssignment,
  )
}

///|
test "let modifiers, pattern lowering, partiality, and kind errors are exact" {
  let variable = parse_expr_entry(b"let x = v in b")
  assert_true(variable.desc is Elet({ name: b"x", .. }, false, RKnone, _, _))
  let ghost = parse_expr_entry(b"let ghost x = v in b")
  assert_true(ghost.desc is Elet({ name: b"x", .. }, true, RKnone, _, _))
  let complex = parse_expr_entry(b"let C x = v in b")
  assert_true(
    complex.desc is Ematch(_, [{ pattern: { desc: Papp(_, [_]), .. }, .. }], []),
  )
  let partial = parse_expr_entry(b"let partial f x = x in f")
  assert_true(
    partial.desc
    is Elet(
      _,
      false,
      RKnone,
      { desc: Efun(_, _, _, _, { partial: true, .. }, _), .. },
      _
    ),
  )
  assert_true(
    expr_test_error(b"let ghost partial x = v in b").kind
    is GhostPartialConflict,
  )
  assert_true(
    expr_test_error(b"let partial ghost x = v in b").kind
    is GhostPartialConflict,
  )
  assert_true(
    expr_test_error(b"let partial (+) = v in b").kind
    is InvalidPartialDeclaration,
  )
  assert_true(
    expr_test_error(b"let function C x = v in b").kind is IllegalKindQualifier,
  )
}

///|
test "local named, ref, recursive, anonymous, and val forms retain exact nodes" {
  let function = parse_expr_entry(b"let f x : ghost t ensures {p} = x in f")
  guard function.desc
    is Elet(
      { name: b"f", .. },
      false,
      RKnone,
      {
        desc: Efun(
          [_],
          Some(_),
          { desc: Pwild, .. },
          MaskGhost,
          { postconditions: [_], .. },
          { desc: Eoptexn(return_ident, MaskGhost, _), .. }
        ),
        ..,
      },
      _
    ) else {
    fail("expected named local function")
  }
  assert_eq(return_ident.name, return_label)
  let symbolic = parse_expr_entry(b"let (+) = x in y")
  assert_true(symbolic.desc is Elet({ name: b"infix +", .. }, _, _, _, _))
  let reference = parse_expr_entry(b"let ref x = v in x")
  assert_true(
    reference.desc
    is Elet(
      { attributes: [Text(name)], .. },
      _,
      _,
      { desc: Eapply({ desc: Eref, .. }, _), .. },
      _
    ) &&
    name == reference_attribute,
  )
  let recursive = parse_expr_entry(b"let rec f x = x with g y = y in f")
  assert_true(recursive.desc is Erec([_, _], _))
  let anonymous = parse_expr_entry(b"fun x -> return x")
  assert_true(
    anonymous.desc
    is Efun(
      [_],
      None,
      { desc: Pwild, .. },
      MaskVisible,
      _,
      { desc: Eoptexn({ name: b"'Return", .. }, MaskVisible, _), .. }
    ),
  )
  let declared = parse_expr_entry(b"val f (x:t) : u ensures {p} in f")
  assert_true(
    declared.desc is Elet(_, _, _, { desc: Eany([_], _, _, _, _, _), .. }, _),
  )
  let constant = parse_expr_entry(b"val x : t in x")
  assert_true(
    constant.desc
    is Elet(_, _, _, { desc: Eany([], _, Some(_), _, _, _), .. }, _),
  )
  let val_ref = parse_expr_entry(b"val ref x : t in x")
  assert_true(
    val_ref.desc
    is Elet(_, _, _, { desc: Eapply({ desc: Eref, .. }, _), .. }, _),
  )
  let amp_val = parse_expr_entry(b"val &x : t in x")
  assert_true(
    amp_val.desc
    is Elet(
      { attributes: [Text(name)], .. },
      _,
      _,
      { desc: Eany([], _, _, _, _, _), .. },
      _
    ) &&
    name == reference_attribute,
  )
}

///|
test "any applies explicit returns, appends witnesses, and rejects restricted clauses" {
  let expression = parse_expr_entry(b"any (x:t) ensures {p} reads {r}")
  guard expression.desc
    is Eany(
      [],
      RKnone,
      Some(_),
      { desc: Pwild, .. },
      MaskVisible,
      specification
    ) else {
    fail("expected any expression")
  }
  assert_eq(specification.reads.length(), 1)
  assert_eq(specification.preconditions.length(), 1)
  assert_true(
    specification.preconditions[0].desc
    is Tattr(Text(name), { desc: Tquant(DTexists, [_], [], _), .. }) &&
    name == witness_existence_attribute,
  )
  assert_true(
    specification.postconditions[0].branches[0].0.desc
    is Pvar({ name: b"x", .. }),
  )
  let restricted : Array[Bytes] = [
    b"any t writes {x}", b"any t raises { E }", b"any t alias {x with y}", b"any t diverges",
  ]
  for source in restricted {
    assert_true(expr_test_error(source).kind is RestrictedAnySpec)
  }
  let defensive = try
    restricted_any_spec({ ..Spec::empty(), partial: true }, expression.span)
  catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected defensive partial check")
  }
  assert_true(defensive.kind is RestrictedAnySpec)
  assert_true(expr_test_error(b"any t partial").kind is UnexpectedToken)
}

///|
test "match, try, and local exceptions keep regular and exception branches separate" {
  let mixed = parse_expr_entry(
    b"match x with | A -> a | exception E y -> b end",
  )
  assert_true(
    mixed.desc
    is Ematch(
      _,
      [{ pattern: { desc: Papp(_, []), .. }, .. }],
      [{ pattern: Some({ desc: Pvar({ name: b"y", .. }), .. }), .. }]
    ),
  )
  let exception_only = parse_expr_entry(b"match x with exception E -> b end")
  assert_true(
    exception_only.desc
    is Ematch(
      _,
      [{ pattern: { desc: Pwild, .. }, body: { desc: Eabsurd, .. } }],
      [_]
    ),
  )
  let tried = parse_expr_entry(b"try x with | E -> a | F y -> b end")
  assert_true(tried.desc is Ematch(_, [], [_, _]))
  let unit_exception = parse_expr_entry(b"exception E in x")
  assert_true(unit_exception.desc is Eexn(_, PTtuple([]), MaskVisible, _))
  let typed_exception = parse_expr_entry(b"exception E (t,ghost u) in x")
  assert_true(
    typed_exception.desc
    is Eexn(_, PTtuple([_, _]), MaskTuple([MaskVisible, MaskGhost]), _),
  )
}

///|
test "while and counted for inject break/continue optional exceptions" {
  let while_loop = parse_expr_entry(
    b"while p do invariant loop_inv {i} variant {v} x done",
  )
  guard while_loop.desc
    is Eoptexn(
      break_ident,
      MaskVisible,
      {
        desc: Ewhile(
          _,
          { terms: [invariant] },
          { items: [_] },
          { desc: Eoptexn(continue_ident, MaskVisible, _), .. }
        ),
        ..,
      }
    ) else {
    fail("expected wrapped while")
  }
  assert_eq(
    (break_ident.name, continue_ident.name),
    (break_label, continue_label),
  )
  assert_eq(spec_test_hypothesis_name(invariant), b"hyp_name:loop_inv")
  let empty = parse_expr_entry(b"while p do done")
  assert_true(
    empty.desc
    is Eoptexn(
      _,
      _,
      {
        desc: Ewhile(
          _,
          _,
          _,
          { desc: Eoptexn(_, _, { desc: Etuple([]), .. }), .. }
        ),
        ..,
      }
    ),
  )
  let annotated_empty = parse_expr_entry(b"while p do invariant {i} done")
  guard annotated_empty.desc
    is Eoptexn(
      _,
      _,
      { desc: Ewhile(_, _, _, { desc: Eoptexn(_, _, unit), .. }), .. }
    ) else {
    fail("expected annotated empty while")
  }
  assert_true(unit.desc is Etuple([]))
  assert_eq(unit.span.start.byte_offset, 24)
  assert_eq(unit.span.end.byte_offset, 24)
  let ascending = parse_expr_entry(b"for i = lo to hi do invariant {p} x done")
  assert_true(
    ascending.desc
    is Eoptexn(_, _, { desc: Efor(_, _, To, _, { terms: [_] }, _), .. }),
  )
  let descending = parse_expr_entry(b"for i = hi downto lo do done")
  assert_true(
    descending.desc is Eoptexn(_, _, { desc: Efor(_, _, DownTo, _, _, _), .. }),
  )
  assert_true(
    expr_test_error(b"while p do variant {a} variant {b} done").kind
    is DuplicateVariant,
  )
}

///|
test "iterator for expands create, next, Done, loop annotations, and default iterator" {
  let iterator = parse_expr_entry(
    b"for Some x in xs with Iter do invariant {p} variant {v} body done",
  )
  guard iterator.desc
    is Elet(
      iterator_ident,
      false,
      RKnone,
      { desc: Eidapp(create, [_]), .. },
      {
        desc: Ematch(
          { desc: Eoptexn(_, _, { desc: Ewhile(_, _, _, _), .. }), .. },
          [],
          [
            {
              exception: done_path,
              pattern: None,
              body: { desc: Etuple([]), .. },
            },
          ]
        ),
        ..,
      }
    ) else {
    fail("expected iterator-for expansion")
  }
  assert_eq(iterator_ident.name, b"it")
  assert_eq(expr_test_last_name(create), b"create")
  assert_eq(expr_test_last_name(done_path), b"Done")
  let named = parse_expr_entry(b"for x in xs with Iter as cursor do done")
  assert_true(named.desc is Elet({ name: b"cursor", .. }, _, _, _, _))
}

///|
test "labels, jumps, conditionals, raises, ghost, assertions, attrs, and casts parse" {
  assert_true(
    parse_expr_entry(b"if p then x").desc is Eif(_, _, { desc: Etuple([]), .. }),
  )
  assert_true(parse_expr_entry(b"if p then x else y").desc is Eif(_, _, _))
  assert_true(parse_expr_entry(b"absurd").desc is Eabsurd)
  assert_true(parse_expr_entry(b"raise E x").desc is Eraise(_, Some(_)))
  assert_true(parse_expr_entry(b"raise (E x)").desc is Eraise(_, Some(_)))
  assert_true(
    parse_expr_entry(b"return").desc
    is Eraise(Qident({ name: b"'Return", .. }), None),
  )
  assert_true(parse_expr_entry(b"return x").desc is Eraise(_, Some(_)))
  assert_true(
    parse_expr_entry(b"break").desc
    is Eraise(Qident({ name: b"'Break", .. }), None),
  )
  assert_true(
    parse_expr_entry(b"break L").desc
    is Eraise(Qident({ name: b"L'Break", .. }), None),
  )
  assert_true(
    parse_expr_entry(b"continue L").desc
    is Eraise(Qident({ name: b"L'Continue", .. }), None),
  )
  assert_true(parse_expr_entry(b"ghost x").desc is Eghost(_))
  let assertion = parse_expr_entry(b"assert named {p}")
  assert_true(
    assertion.desc is Eassert(Assert, term) &&
    spec_test_hypothesis_name(term) == b"hyp_name:named",
  )
  assert_true(parse_expr_entry(b"assume {p}").desc is Eassert(Assume, _))
  assert_true(parse_expr_entry(b"check {p}").desc is Eassert(Check, _))
  assert_true(
    parse_expr_entry(b"[@a] x : t").desc
    is Eattr(Text(b"a"), { desc: Ecast(_, _), .. }),
  )
  let labeled = parse_expr_entry(b"label L in while p do x done")
  assert_true(labeled.desc is Elabel({ name: b"L", .. }, _))
}

///|
test "expression function literals keep full proxy trees for mappings and sequences" {
  let mapping = parse_expr_entry(b"[| d0 => r0; d1 => r1; _ => z |]")
  assert_true(
    mapping.desc
    is Eattr(Text(name), { desc: Elet({ name: b"def'e", .. }, _, _, _, _), .. }) &&
    name == function_literal_attribute,
  )
  let sequence = parse_expr_entry(b"[| a; b |]")
  guard sequence.desc is Eattr(_, tree) else {
    fail("expected sequence function literal")
  }
  let mut cursor = tree
  let mut lets = 0
  while cursor.desc is Elet(_, _, _, _, rest) {
    lets = lets + 1
    cursor = rest
  }
  assert_eq(lets, 4)
  assert_true(cursor.desc is Efun(_))
}

///|
fn parse_spec_entry(
  input : BytesView,
  filename? : BytesView = b"<spec-test>",
) -> Spec raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => parser.parse_spec())
}

///|
fn parse_return_named_entry(
  input : BytesView,
  filename? : BytesView = b"<return-test>",
) -> (Pattern, Pty, Mask) raise ParseError {
  let parser = Parser::new(input, filename~)
  finish_internal_entry(parser, parser => {
    let result = parser.parse_return_named()
    (result.pattern, result.return_type, result.mask)
  })
}
