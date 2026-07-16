///|
test "desugar constants: internal spellings match Why3 1.7.2" {
  assert_eq(reference_attribute, b"mlw:reference_var")
  assert_eq(break_attribute, b"vc:break_me")
  assert_eq(white_box_attribute, b"vc:white_box")
  assert_eq(unused_variable_attribute, b"W:unused_variable:N")
  assert_eq(proxy_attribute, b"mlw:proxy_symbol")
  assert_eq(user_axiom_attribute, b"useraxiom")
  assert_eq(function_literal_attribute, b"funlit")
  assert_eq(witness_existence_attribute, b"expl:witness existence")
  assert_eq(old_label, b"'Old")
  assert_eq(return_label, b"'Return")
  assert_eq(break_label, b"'Break")
  assert_eq(continue_label, b"'Continue")
}

///|
fn desugar_test_span(offset : Int) -> Span {
  let position = SourcePos::{
    filename: b"desugar.mlw",
    byte_offset: offset,
    line: 1L,
    column: offset.to_int64(),
  }
  Span::empty(position)
}

///|
fn desugar_test_ident(name : Bytes, offset : Int) -> Ident {
  { name, attributes: [], span: desugar_test_span(offset) }
}

///|
fn desugar_test_term(name : Bytes, offset : Int) -> Term {
  {
    desc: Tident(Qident(desugar_test_ident(name, offset))),
    span: desugar_test_span(offset),
  }
}

///|
fn desugar_test_expr(name : Bytes, offset : Int) -> Expr {
  {
    desc: Eident(Qident(desugar_test_ident(name, offset))),
    span: desugar_test_span(offset),
  }
}

///|
fn desugar_test_pattern(name : Bytes, offset : Int) -> Pattern {
  {
    desc: Pvar(desugar_test_ident(name, offset)),
    span: desugar_test_span(offset),
  }
}

///|
fn desugar_test_error(action : () -> Unit raise ParseError) -> ParseDiagnostic {
  try action() catch {
    ParseError(diagnostic) => diagnostic
  } noraise {
    _ => abort("expected parsing-time desugaring error")
  }
}

///|
test "term pattern-let unfolding covers variable, wildcard, wrappers, cast, and unit" {
  let value = desugar_test_term(b"value", 20)
  let body = desugar_test_term(b"body", 30)
  let variable = Pattern::{
    desc: Pvar(desugar_test_ident(b"x", 1)),
    span: desugar_test_span(1),
  }
  assert_true(
    unfold_term_pattern_let(variable, value, body)
    is Tlet({ name: b"x", .. }, _, _),
  )
  let wildcard = Pattern::{ desc: Pwild, span: desugar_test_span(2) }
  guard unfold_term_pattern_let(wildcard, value, body) is Tlet(ident, _, _) else {
    fail("expected wildcard let")
  }
  assert_eq(ident.name, b"_")
  assert_eq(ident.span, wildcard.span)
  let ty = PTtyapp(Qident(desugar_test_ident(b"t", 3)), [])
  let wrapped = Pattern::{
    desc: Pparen({
      desc: Pscope(Qident(desugar_test_ident(b"M", 4)), {
        desc: Pcast(variable, ty),
        span: desugar_test_span(5),
      }),
      span: desugar_test_span(4),
    }),
    span: desugar_test_span(0),
  }
  guard unfold_term_pattern_let(wrapped, value, body) is Tlet(_, cast_value, _) else {
    fail("expected wrapped cast let")
  }
  assert_true(cast_value.desc is Tcast(_, _))
  assert_eq(cast_value.span, value.span)
  let unit = Pattern::{ desc: Ptuple([]), span: desugar_test_span(6) }
  guard unfold_term_pattern_let(unit, value, body)
    is Tlet(unit_ident, unit_value, _) else {
    fail("expected unit wildcard let")
  }
  assert_eq(unit_ident.name, b"_")
  assert_eq(unit_ident.span, unit.span)
  assert_true(unit_value.desc is Tcast(_, PTtuple([])))
}

///|
test "complex term pattern-let keeps the original branch but casts the scrutinee" {
  let value = desugar_test_term(b"value", 20)
  let body = desugar_test_term(b"body", 30)
  let constructor_pattern = Pattern::{
    desc: Papp(Qident(desugar_test_ident(b"Some", 4)), [
      { desc: Pvar(desugar_test_ident(b"x", 9)), span: desugar_test_span(9) },
    ]),
    span: desugar_test_span(4),
  }
  let ty = PTtyapp(Qident(desugar_test_ident(b"t", 12)), [])
  let original = Pattern::{
    desc: Pparen({
      desc: Pcast(constructor_pattern, ty),
      span: desugar_test_span(3),
    }),
    span: desugar_test_span(2),
  }
  guard unfold_term_pattern_let(original, value, body)
    is Tcase(scrutinee, [(branch, branch_body)]) else {
    fail("expected complex pattern case")
  }
  assert_eq(branch, original)
  assert_eq(branch_body, body)
  assert_true(scrutinee.desc is Tcast(_, _))
  assert_eq(scrutinee.span, value.span)
}

///|
test "term function-literal reduction preserves default-only and redundant-last forms" {
  let opening = desugar_test_span(0)
  let closing = desugar_test_span(40)
  let key = desugar_test_term(b"key", 10)
  let value = desugar_test_term(b"value", 20)
  let literal = desugar_term_function_literal(
    opening,
    closing,
    [(key, value)],
    None,
  )
  guard literal.desc
    is Tattr(
      Text(attribute),
      { desc: Tquant(DTlambda, [binder], [], branch), span: lambda_span }
    ) else {
    fail("expected function literal lambda")
  }
  assert_eq(attribute, function_literal_attribute)
  assert_eq(lambda_span, opening.join(closing))
  guard binder.ident is Some(identifier) else { fail("expected named binder") }
  assert_eq(identifier.name, b"x'x")
  guard branch.desc is Tif(condition, consequent, alternative) else {
    fail("expected redundant last comparison")
  }
  assert_eq(consequent, value)
  assert_eq(alternative, value)
  assert_true(
    condition.desc
    is Tinfix(
      { desc: Tident(Qident({ name: b"x'x", .. })), .. },
      { name: b"infix =", span, .. },
      _
    ) &&
    span == key.span,
  )
  let default = desugar_test_term(b"default", 25)
  let default_only = desugar_term_function_literal(
    opening,
    closing,
    [],
    Some(default),
  )
  guard default_only.desc
    is Tattr(_, { desc: Tquant(_, [default_binder], [], default_body), .. }) else {
    fail("expected default-only lambda")
  }
  guard default_binder.ident is Some(default_ident) else {
    fail("expected default-only binder")
  }
  assert_eq(default_ident.name, b"_")
  assert_eq(default_body, default)
}

///|
test "sequence function-literal indices are decimal and inherit value spans" {
  let first = desugar_test_term(b"first", 10)
  let second = desugar_test_term(b"second", 20)
  let mappings = indexed_term_values([first, second])
  assert_eq(mappings.length(), 2)
  for index, mapping in mappings {
    let key = mapping.0
    guard key.desc is Tconst(ConstInt(constant)) else {
      fail("expected decimal sequence index")
    }
    assert_true(constant.kind is ILitDec)
    assert_eq(constant.value.compare_int(index), 0)
    assert_eq(key.span, mapping.1.span)
  }
}

///|
test "partial application accepts only parameterized functions and any nodes" {
  let span = desugar_test_span(0)
  let ident = desugar_test_ident(b"x", 1)
  let binder = make_binder(span, Some(ident), false, None)
  let body = desugar_test_expr(b"body", 2)
  let function = make_expr(
    Efun(
      [binder],
      None,
      { desc: Pwild, span },
      MaskVisible,
      Spec::empty(),
      body,
    ),
    span,
  )
  assert_true(
    apply_partial_expr(PartialModifier, function).desc
    is Efun(_, _, _, _, { partial: true, .. }, _),
  )
  let param = Param::{
    span,
    ident: Some(ident),
    ghost: false,
    param_type: PTtuple([]),
  }
  let any = make_expr(
    Eany(
      [param],
      RKnone,
      None,
      { desc: Pwild, span },
      MaskVisible,
      Spec::empty(),
    ),
    span,
  )
  assert_true(
    apply_partial_expr(PartialModifier, any).desc
    is Eany(_, _, _, _, _, { partial: true, .. }),
  )
  let invalid = desugar_test_error(() => {
    ignore(apply_partial_expr(PartialModifier, make_expr(Etrue, span)))
  })
  assert_true(invalid.kind is InvalidPartialDeclaration)
  assert_eq(apply_partial_expr(GhostModifier, function), function)
}

///|
test "ghost push and expression pattern-let follow the exact recursive branches" {
  let x = desugar_test_pattern(b"x", 1)
  let y = desugar_test_pattern(b"y", 2)
  let alias_ident = desugar_test_ident(b"z", 3)
  let ty = PTtyapp(Qident(desugar_test_ident(b"t", 4)), [])
  let nested = Pattern::{
    desc: Ptuple([
      {
        desc: Pcast(
          {
            desc: Pas(
              { desc: Por(x, y), span: desugar_test_span(1) },
              alias_ident,
              false,
            ),
            span: desugar_test_span(1),
          },
          ty,
        ),
        span: desugar_test_span(1),
      },
      y,
    ]),
    span: desugar_test_span(0),
  }
  assert_true(
    push_ghost_pattern(nested).desc
    is Ptuple(
      [
        {
          desc: Pcast(
            {
              desc: Pas(
                {
                  desc: Por({ desc: Pghost({ desc: Pvar(_), .. }), .. }, _),
                  ..,
                },
                _,
                false
              ),
              ..,
            },
            _
          ),
          ..,
        },
        { desc: Pvar({ name: b"y", .. }), .. },
      ]
    ),
  )
  let constructor_pattern = Pattern::{
    desc: Papp(Qident(desugar_test_ident(b"C", 5)), [x]),
    span: desugar_test_span(5),
  }
  assert_true(push_ghost_pattern(constructor_pattern).desc is Pghost(_))
  let value = desugar_test_expr(b"value", 10)
  let body = desugar_test_expr(b"body", 20)
  assert_true(
    simplify_expr_pattern_let(
      RKnone,
      value,
      { desc: Pghost(x), span: x.span },
      body,
      desugar_test_span(30),
    )
    is Elet({ name: b"x", .. }, true, RKnone, _, _),
  )
  assert_true(
    simplify_expr_pattern_let(
      RKnone,
      value,
      constructor_pattern,
      body,
      desugar_test_span(30),
    )
    is Ematch(_, [{ pattern, .. }], []) &&
    pattern == constructor_pattern,
  )
  let diagnostic = desugar_test_error(() => {
    ignore(
      simplify_expr_pattern_let(
        RKfunc,
        value,
        constructor_pattern,
        body,
        desugar_test_span(30),
      ),
    )
  })
  assert_true(diagnostic.kind is IllegalKindQualifier)
  assert_eq(diagnostic.span, desugar_test_span(30))
}

///|
test "assignment lowering handles references, arbitrary unary calls, arrays, and attrs" {
  let full = desugar_test_span(50)
  let x = desugar_test_expr(b"x", 1)
  let value = desugar_test_expr(b"v", 2)
  guard desugar_assignment(x, value, full)
    is Eassign([{ target: reference, field: None, value: actual }]) else {
    fail("expected reference assignment")
  }
  assert_true(reference.desc is Easref(Qident({ name: b"x", .. })))
  assert_eq(actual, value)
  let prefix = desugar_test_ident(b"prefix !", 3)
  let base = desugar_test_expr(b"base", 4)
  let unary = make_expr(Eidapp(Qident(prefix), [base]), desugar_test_span(3))
  assert_true(
    desugar_assignment(unary, value, full)
    is Eassign([{ target, field: Some(Qident({ name: b"prefix !", .. })), .. }]) &&
    target == base,
  )
  let get = desugar_test_ident(op_get(b"''"), 5)
  let index = desugar_test_expr(b"i", 6)
  let indexed = make_expr(
    Eidapp(Qident(get), [base, index]),
    desugar_test_span(5),
  )
  assert_true(
    desugar_assignment(indexed, value, full)
    is Eidapp(Qident({ name: b"mixfix []<-''", .. }), [_, _, _]),
  )
  let attributed_x = make_expr(
    Eattr(Text(b"outer"), make_expr(Eattr(Text(b"inner"), x), x.span)),
    x.span,
  )
  let field = make_expr(
    Eidapp(Qident(desugar_test_ident(b"f", 7)), [base]),
    desugar_test_span(7),
  )
  let attributed_field = make_expr(Eattr(Text(b"second"), field), field.span)
  let parallel = desugar_assignment(
    make_expr(Etuple([attributed_x, attributed_field]), full),
    make_expr(Etuple([value, base]), full),
    full,
  )
  guard parallel
    is Eattr(
      Text(b"outer"),
      {
        desc: Eattr(
          Text(b"inner"),
          {
            desc: Eattr(
              Text(b"second"),
              { desc: Eassign(items), span: inner_span }
            ),
            span: middle_span,
          }
        ),
        span: outer_span,
      }
    ) else {
    fail("expected hoisted assignment attributes")
  }
  assert_eq(items.length(), 2)
  assert_eq((inner_span, middle_span, outer_span), (full, full, full))
  let right_tuple = make_expr(Etuple([value, base]), full)
  assert_true(
    desugar_assignment(x, right_tuple, full)
    is Eassign([{ value: { desc: Etuple([_, _]), .. }, .. }]),
  )
}

///|
test "assignment lowering keeps invalid-target and parallel errors distinct" {
  let full = desugar_test_span(50)
  let value = desugar_test_expr(b"v", 2)
  let invalid = make_expr(Etrue, desugar_test_span(3))
  let invalid_diagnostic = desugar_test_error(() => {
    ignore(desugar_assignment(invalid, value, full))
  })
  assert_true(invalid_diagnostic.kind is InvalidAssignment)
  assert_eq(invalid_diagnostic.span, invalid.span)
  let mismatch = desugar_test_error(() => {
    ignore(
      desugar_assignment(
        make_expr(Etuple([value, value]), full),
        make_expr(Etuple([value]), full),
        full,
      ),
    )
  })
  assert_true(mismatch.kind is InvalidParallelAssignment)
  let getter = make_expr(
    Eidapp(Qident(desugar_test_ident(op_get(b""), 4)), [value, value]),
    desugar_test_span(4),
  )
  let array_parallel = desugar_test_error(() => {
    ignore(
      desugar_assignment(
        make_expr(Etuple([getter]), full),
        make_expr(Etuple([value]), full),
        full,
      ),
    )
  })
  assert_true(array_parallel.kind is InvalidParallelAssignment)
}

///|
test "any witness preconditions unfold simple posts and right-associate conjunctions" {
  let any_span = desugar_test_span(100)
  let return_type = PTtyapp(Qident(desugar_test_ident(b"t", 101)), [])
  let p = desugar_test_term(b"p", 10)
  let q = desugar_test_term(b"q", 20)
  let x = desugar_test_pattern(b"x", 11)
  let cast_result = Pattern::{
    desc: Pcast(desugar_test_pattern(b"result", 21), return_type),
    span: desugar_test_span(21),
  }
  let preconditions = preconditions_of_any(any_span, return_type, [
    { span: desugar_test_span(10), branches: [(x, p)] },
    { span: desugar_test_span(20), branches: [(cast_result, q)] },
  ])
  guard preconditions
    is [
      {
        desc: Tattr(
          Text(attribute),
          { desc: Tquant(DTexists, [binder], [], conjunction), .. }
        ),
        ..,
      },
    ] else {
    fail("expected witness existential")
  }
  assert_eq(attribute, witness_existence_attribute)
  guard binder.ident is Some(result_ident) else {
    fail("expected result witness binder")
  }
  assert_eq(result_ident.name, b"result")
  assert_true(
    result_ident.attributes is [Text(name)] && name == break_attribute,
  )
  assert_true(
    conjunction.desc
    is Tbinop(
      { desc: Tlet({ name: b"x", .. }, _, _), .. },
      DTandAsym,
      { desc: Tlet({ name: b"_", .. }, { desc: Tcast(_, _), .. }, _), .. }
    ),
  )
  let tuple = Pattern::{
    desc: Ptuple([x, desugar_test_pattern(b"y", 12)]),
    span: desugar_test_span(11),
  }
  let tuple_post = preconditions_of_any(any_span, return_type, [
    { span: desugar_test_span(10), branches: [(tuple, p)] },
  ])
  assert_true(
    tuple_post[0].desc
    is Tattr(_, { desc: Tquant(_, _, _, { desc: Tcase(_, [_]), .. }), .. }),
  )
}

///|
test "expression function literals reproduce proxy names and fold-left let order" {
  let d0 = desugar_test_expr(b"d0", 10)
  let r0 = desugar_test_expr(b"r0", 11)
  let d1 = desugar_test_expr(b"d1", 20)
  let r1 = desugar_test_expr(b"r1", 21)
  let default = desugar_test_expr(b"default", 30)
  let literal = desugar_expr_function_literal(
    desugar_test_span(0),
    desugar_test_span(40),
    [(d0, r0), (d1, r1)],
    Some(default),
  )
  guard literal.desc
    is Eattr(
      Text(attribute),
      {
        desc: Elet(
          def,
          false,
          RKnone,
          default_value,
          {
            desc: Elet(
              domain1,
              false,
              RKnone,
              domain1_value,
              {
                desc: Elet(
                  range1,
                  false,
                  RKnone,
                  range1_value,
                  {
                    desc: Elet(
                      domain0,
                      false,
                      RKnone,
                      domain0_value,
                      {
                        desc: Elet(
                          range0,
                          false,
                          RKnone,
                          range0_value,
                          { desc: Efun(_, _, _, _, _, body), .. }
                        ),
                        ..,
                      }
                    ),
                    ..,
                  }
                ),
                ..,
              }
            ),
            ..,
          }
        ),
        ..,
      }
    ) else {
    fail("expected proxy let tree")
  }
  assert_eq(attribute, function_literal_attribute)
  assert_eq(
    (def.name, domain1.name, range1.name, domain0.name, range0.name),
    (b"def'e", b"d'i1", b"r'i1", b"d'i0", b"r'i0"),
  )
  assert_eq(
    (default_value, domain1_value, range1_value, domain0_value, range0_value),
    (default, d1, r1, d0, r0),
  )
  assert_true(
    body.desc
    is Eif(
      _,
      { desc: Eident(Qident({ name: b"r'i0", .. })), .. },
      {
        desc: Eif(
          _,
          { desc: Eident(Qident({ name: b"r'i1", .. })), .. },
          { desc: Eident(Qident({ name: b"def'e", .. })), .. }
        ),
        ..,
      }
    ),
  )
}

///|
test "label traversal reaches only the first loop through allowed wrappers" {
  let label = desugar_test_ident(b"L", 0)
  let condition = make_expr(Etrue, desugar_test_span(1))
  let loop_body = desugar_test_expr(b"body", 2)
  let while_expr = make_expr(
    Ewhile(condition, { terms: [] }, { items: [] }, loop_body),
    desugar_test_span(1),
  )
  let untouched = desugar_test_expr(b"right", 3)
  let sequence = make_expr(
    Esequence(while_expr, untouched),
    desugar_test_span(1),
  )
  let labeled = label_over_loop(label, sequence)
  guard labeled.desc
    is Elabel(
      _,
      {
        desc: Esequence(
          {
            desc: Eoptexn(
              { name: b"L'Break", .. },
              MaskVisible,
              {
                desc: Ewhile(
                  _,
                  _,
                  _,
                  { desc: Eoptexn({ name: b"L'Continue", .. }, _, _), .. }
                ),
                ..,
              }
            ),
            ..,
          },
          actual_right
        ),
        ..,
      }
    ) else {
    fail("expected labeled loop exceptions")
  }
  assert_eq(actual_right, untouched)
}
