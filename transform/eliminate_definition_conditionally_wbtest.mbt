// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "definition insertion opens let and case binders but preserves epsilon binders" {
  let context = @identity.CompilationContext::new()
  let origin = @identity.Origin::user(b"definition", None, [])
  let type_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"item",
    origin,
    [],
    None,
  )
  let ty = @logic.Ty::app(type_symbol, [], None)
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"holds",
    origin,
    [ty],
    None,
  )
  let value = @logic.VSymbol::new(context, b"value", origin, ty, None)
  let let_binder = @logic.VSymbol::new(context, b"bound", origin, ty, None)
  let pattern_binder = @logic.VSymbol::new(
    context,
    b"matched",
    origin,
    ty,
    None,
  )
  let epsilon_binder = @logic.VSymbol::new(context, b"chosen", origin, ty, None)
  let epsilon = @logic.Term::epsilon(
    epsilon_binder,
    @logic.Term::apply_predicate(
      predicate,
      [@logic.Term::variable(epsilon_binder)],
      None,
    ),
    None,
  )
  let branch = @logic.Term::apply_predicate(predicate, [epsilon], None)
  let body = @logic.Term::let_in(
    let_binder,
    @logic.Term::variable(value),
    @logic.Term::case(
      @logic.Term::variable(let_binder),
      [(@logic.Pattern::variable(pattern_binder), branch)],
      None,
    ),
    None,
  )
  let head = @logic.Term::apply_predicate(
    predicate,
    [@logic.Term::variable(value)],
    None,
  )
  guard definition_relation(context, head, body, None).view()
    is Tlet(opened_let, _, case_term) &&
    case_term.view() is Tcase(scrutinee, [opened_branch]) &&
    scrutinee.view() is Tvar(scrutinee_variable) &&
    opened_branch.view().pattern.view() is Pvar(opened_pattern) &&
    opened_branch.view().body.view() is Tbinop(Iff, _, relation_body) &&
    relation_body.view() is Tapp(_, _, [epsilon_term]) &&
    epsilon_term.view() is Teps(opened_epsilon, _) else {
    fail("definition insertion changed the expected let/case/epsilon shape")
  }
  assert_true(opened_let == let_binder)
  assert_true(opened_let.identifier_id() != let_binder.identifier_id())
  assert_true(
    opened_let.clone_source_identifier_id() == Some(let_binder.identifier_id()),
  )
  assert_true(scrutinee_variable.identifier_id() == opened_let.identifier_id())
  assert_true(opened_pattern == pattern_binder)
  assert_true(opened_pattern.identifier_id() != pattern_binder.identifier_id())
  assert_true(opened_epsilon.identifier_id() == epsilon_binder.identifier_id())
}
