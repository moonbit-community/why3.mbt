// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "simplify_formula removes asymmetric split decoration" {
  let decorated = @logic.Term::true_formula().add_attributes([
    b"asym_split", b"keep",
  ])
  let stripped = remove_term_attribute(decorated, b"asym_split")
  assert_eq(stripped.attributes(), [b"keep"])
}

///|
test "simplify_formula removes asymmetric split from predicate formulas" {
  let context = @identity.CompilationContext::new()
  let origin = @identity.Origin::user(b"p", None, [])
  let predicate = @logic.LSymbol::new_predicate(context, b"p", origin, [], None)
  let decorated = @logic.Term::apply_predicate(predicate, [], None).add_attributes([
      b"asym_split", b"keep",
    ],
  )
  let simplified = simplify_formula_term(context, decorated)
  assert_eq(simplified.attributes(), [b"keep"])
}

///|
test "simplify_formula preserves nested structure while removing decoration" {
  let context = @identity.CompilationContext::new()
  let origin = @identity.Origin::user(b"nested", None, [])
  let symbol = @logic.TypeSymbol::new_abstract(context, b"t", origin, [], None)
  let ty = @logic.Ty::app(symbol, [], None)
  let first = @logic.VSymbol::new(context, b"x", origin, ty, None)
  let second = @logic.VSymbol::new(context, b"y", origin, ty, None)
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"p",
    origin,
    [ty],
    None,
  )
  let decorated = @logic.Term::apply_predicate(
    predicate,
    [@logic.Term::variable(first)],
    None,
  ).add_attributes([b"asym_split", b"keep"])
  let other = @logic.Term::apply_predicate(
    predicate,
    [@logic.Term::variable(second)],
    None,
  )
  let conjunction = @logic.Term::binary(And, decorated, other, None)
  guard simplify_formula_term(context, conjunction).view()
    is Tbinop(And, direct_left, _) else {
    fail("simplification changed the direct conjunction shape")
  }
  assert_eq(direct_left.attributes(), [b"keep"])
  let inner = @logic.Term::quantify(
    ForallQuantifier,
    [second],
    [],
    conjunction,
    None,
  )
  let nested = @logic.Term::quantify(ForallQuantifier, [first], [], inner, None)
  guard simplify_formula_term(context, nested).view()
    is Tquant(_, _, _, outer_body) &&
    outer_body.view() is Tquant(_, _, _, inner_body) &&
    inner_body.view() is Tbinop(And, left, _) else {
    fail("simplification changed the nested formula shape")
  }
  assert_eq(left.attributes(), [b"keep"])
}

///|
test "simplify_formula caches only surviving opened binder clones" {
  let context = @identity.CompilationContext::new()
  let origin = @identity.Origin::user(b"cached", None, [])
  let type_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"t",
    origin,
    [],
    None,
  )
  let ty = @logic.Ty::app(type_symbol, [], None)
  let binder = @logic.VSymbol::new(context, b"x", origin, ty, None)
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"p",
    origin,
    [ty],
    None,
  )
  let body = @logic.Term::apply_predicate(
    predicate,
    [@logic.Term::variable(binder)],
    None,
  ).add_attributes([b"asym_split"])
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    [binder],
    [],
    body,
    None,
  )
  let proposition = @logic.PrSymbol::new(context, b"cached_axiom", origin)
  let declaration = @logic.Decl::proposition(
    context,
    origin,
    Paxiom,
    proposition,
    formula,
    None,
  )
  let goal_symbol = @logic.PrSymbol::new(context, b"goal", origin)
  let goal = @logic.Decl::proposition(
    context,
    origin,
    Pgoal,
    goal_symbol,
    @logic.Term::true_formula(),
    None,
  )
  let task = @theory.Task::trusted_new(
    context.fresh_id(),
    [TheoryDecl(declaration), TheoryDecl(goal)],
    None,
  )
  let output_binder = fn(task : @theory.Task) -> @logic.VSymbol raise {
    for item in task.view().items {
      if item is TheoryDecl(declaration) &&
        declaration.view() is Dprop(Paxiom, _, simplified) &&
        simplified.view() is Tquant(ForallQuantifier, [opened], _, _) {
        return opened
      }
    }
    fail("simplify_formula lost the cached quantified axiom")
  }
  begin_declaration_cache_goal(task)
  let first = output_binder(simplify_formula(context, task))
  assert_true(first.identifier_id() != binder.identifier_id())
  assert_true(
    first.clone_source_identifier_id() == Some(binder.identifier_id()),
  )
  begin_declaration_cache_goal(task)
  let second = output_binder(simplify_formula(context, task))
  assert_true(second.identifier_id() == first.identifier_id())

  let unchanged_formula = @logic.Term::quantify(
    ForallQuantifier,
    [binder],
    [],
    @logic.Term::apply_predicate(
      predicate,
      [@logic.Term::variable(binder)],
      None,
    ),
    None,
  )
  guard simplify_formula_term(context, unchanged_formula).view()
    is Tquant(_, [unchanged], _, _) else {
    fail("simplify_formula lost the unchanged quantified formula")
  }
  assert_true(unchanged.identifier_id() == binder.identifier_id())
}

///|
test "term instantiation accepts a reconstruction span" {
  let context = @identity.CompilationContext::new()
  let origin = @identity.Origin::user(b"p", None, [])
  let predicate = @logic.LSymbol::new_predicate(context, b"p", origin, [], None)
  let original = @identity.SourceSpan::new(b"a", 1, 2, 1L, 1L, 1L, 2L)
  let replacement = @identity.SourceSpan::new(b"b", 3, 4, 2L, 1L, 2L, 2L)
  let term = @logic.Term::apply_predicate(predicate, [], Some(original)).source_decorate(
    Some(original),
    [],
  )
  let instantiated = instantiate_term(
    context,
    @logic.TySubstitution::new(),
    Map([]),
    term,
    @identity.InlineTrivial,
    Some(replacement),
  )
  assert_eq(instantiated.source_span(), Some(replacement))
}
