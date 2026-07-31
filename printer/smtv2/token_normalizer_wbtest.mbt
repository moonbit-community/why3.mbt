// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "SMT lexer skips comments and preserves quoted/string token bytes" {
  let tokens = lex_smt_tokens(
    b" ; ignored ( )\n(|x y| \"a\"\"b\" atom) ; tail\n",
  )
  assert_eq(tokens.map(token => token.bytes), [
    b"(", b"|x y|", b"\"a\"\"b\"", b"atom", b")",
  ])
  assert_eq(tokens[1].kind, QuotedSymbol)
  assert_eq(tokens[2].kind, StringLiteral)
}

///|
test "SMT lexer fails closed on malformed delimited tokens" {
  try lex_smt_tokens(b"|unterminated") catch {
    PrinterError(diagnostic) => assert_eq(diagnostic.kind, InvalidSmtToken)
  } noraise {
    _ => fail("expected malformed quoted symbol to fail")
  }
  try lex_smt_tokens(b"\"unterminated") catch {
    PrinterError(diagnostic) => assert_eq(diagnostic.kind, InvalidSmtToken)
  } noraise {
    _ => fail("expected malformed string to fail")
  }
}

///|
test "name allocation ports Why3 sanitizer, reserved words, and collisions" {
  let context = @identity.CompilationContext::new()
  let names = NameAllocator::new()
  assert_eq(names.unique(context.fresh_id(), b"select"), b"select1")
  assert_eq(names.unique(context.fresh_id(), b"select"), b"select2")
  assert_eq(names.unique(context.fresh_id(), b"select1"), b"select11")
  assert_eq(names.unique(context.fresh_id(), b"0 x"), b"zr_x")
  assert_eq(names.unique(context.fresh_id(), b""), b"zilch")
}

///|
test "normalizer alpha-renames only generated identifier occurrences" {
  let context = @identity.CompilationContext::new()
  let first = context.fresh_id()
  let second = context.fresh_id()
  let user = context.fresh_id()
  let generated_origin = @identity.Origin::generated(
    @identity.Guards,
    b"x",
    None,
    [],
  )
  let query : SmtQuery = {
    bytes: b"(x x x x)\n",
    identifiers: [
      {
        start: 1,
        end: 2,
        semantic_id: first,
        identifier_id: first.identifier_id(),
        origin: generated_origin,
      },
      {
        start: 3,
        end: 4,
        semantic_id: first,
        identifier_id: first.identifier_id(),
        origin: generated_origin,
      },
      {
        start: 5,
        end: 6,
        semantic_id: second,
        identifier_id: second.identifier_id(),
        origin: @identity.Origin::generated(@identity.Guards, b"x", None, []),
      },
      {
        start: 7,
        end: 8,
        semantic_id: user,
        identifier_id: user.identifier_id(),
        origin: @identity.Origin::user(b"x", None, []),
      },
    ],
  }
  assert_eq(normalize_smt_query(query).tokens(), [
    b"(", b"$generated[encoding_smt_if_poly:guards][0]", b"$generated[encoding_smt_if_poly:guards][0]",
    b"$generated[encoding_smt_if_poly:guards][1]", b"x", b")",
  ])
}

///|
test "definition binders remain generated through type-preserving guards clones" {
  let context = @identity.CompilationContext::new()
  let user_origin = @identity.Origin::user(b"hl", None, [])
  let type_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"t",
    @identity.Origin::user(b"t", None, []),
    [],
    None,
  )
  let ty = @logic.Ty::app(type_symbol, [], None)
  let raw = @logic.VSymbol::new(context, b"hl", user_origin, ty, None)
  let hidden = raw.clone_identifier(context, None)
  let defined = hidden.clone_identifier_with_origin(
    context,
    @identity.Origin::generated(
      @identity.EliminateDefinitionConditionally,
      b"hl",
      None,
      [],
    ),
    None,
  )
  let task_with_binder = fn(variable : @logic.VSymbol) -> @theory.Task raise {
    let formula = @logic.Term::quantify(
      ForallQuantifier,
      [variable],
      [],
      @logic.Term::true_formula(),
      None,
    )
    let proposition = @logic.PrSymbol::new(
      context,
      b"goal",
      @identity.Origin::user(b"goal", None, []),
    )
    let declaration = @logic.Decl::proposition(
      context,
      proposition.view().origin,
      Pgoal,
      proposition,
      formula,
      None,
    )
    @theory.Task::trusted_new(
      context.fresh_id(),
      [TheoryDecl(declaration)],
      None,
    )
  }
  let provenance = SmtProvenance::new(context)
  provenance.observe_task(task_with_binder(raw), None)
  provenance.observe_task(
    task_with_binder(defined),
    Some(@identity.EliminateAlgebraicIfPoly),
  )
  let guarded = defined.clone_as(
    context,
    b"hl",
    @identity.Origin::generated(@identity.Guards, b"hl", None, []),
    ty,
    None,
  )
  provenance.observe_task(task_with_binder(guarded), Some(@identity.Guards))
  let query : SmtQuery = {
    bytes: b"(hl)\n",
    identifiers: [
      {
        start: 1,
        end: 3,
        semantic_id: guarded.semantic_id(),
        identifier_id: guarded.identifier_id(),
        origin: guarded.view().origin,
      },
    ],
  }
  assert_eq(normalize_smt_query_with_provenance(query, provenance).tokens(), [
    b"(", b"$generated[eliminate_definition_conditionally][0]", b")",
  ])
}

///|
test "normalizer rejects identifier spans that do not align to one atom" {
  let context = @identity.CompilationContext::new()
  let identifier = context.fresh_id()
  let query : SmtQuery = {
    bytes: b"|quoted name|\n",
    identifiers: [
      {
        start: 0,
        end: 13,
        semantic_id: identifier,
        identifier_id: identifier.identifier_id(),
        origin: @identity.Origin::generated(
          @identity.Wp,
          b"quoted name",
          None,
          [],
        ),
      },
    ],
  }
  try normalize_smt_query(query) catch {
    PrinterError(diagnostic) =>
      assert_eq(diagnostic.kind, InvalidIdentifierOccurrence)
  } noraise {
    _ => fail("expected non-atom identifier span to fail")
  }
}

///|
test "discriminate instances inherit completed base syntax maps" {
  let context = @identity.CompilationContext::new()
  let original = @logic.LSymbol::new_predicate(
    context,
    b"polymorphic",
    @identity.Origin::user(b"polymorphic", None, []),
    [],
    None,
  )
  let generated = @logic.LSymbol::new_predicate(
    context,
    b"monomorphic",
    @identity.Origin::generated(
      @identity.DiscriminateIfPoly,
      b"monomorphic",
      None,
      [],
    ),
    [],
    None,
  )
  let proposition = @logic.PrSymbol::new(
    context,
    b"goal",
    @identity.Origin::user(b"goal", None, []),
  )
  let goal = @logic.Decl::proposition(
    context,
    @identity.Origin::user(b"goal", None, []),
    Pgoal,
    proposition,
    @logic.Term::true_formula(),
    None,
  )
  let task = @theory.Task::trusted_new(
    context.fresh_id(),
    [
      TheoryMeta(
        @theory.Meta::new(b"encoding:lsinst", [
          MetaLogicSymbol(original),
          MetaLogicSymbol(generated),
        ]),
      ),
      TheoryMeta(
        @theory.Meta::new(b"syntax_logic", [
          MetaLogicSymbol(original),
          MetaString(b"true"),
          MetaInteger(0L),
        ]),
      ),
      TheoryDecl(goal),
    ],
    None,
  )
  assert_eq(syntax_maps(task).logic_template(generated), Some(b"true"))
}
