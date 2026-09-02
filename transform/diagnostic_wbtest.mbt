// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "checked transform tasks discard repeated declaration symbols" {
  let context = @identity.CompilationContext::new()
  let origin = @identity.Origin::user(b"duplicate", None, [])
  let symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"duplicate",
    origin,
    [],
    None,
  )
  let declaration = @logic.Decl::type_declaration(
    context,
    origin,
    [symbol],
    None,
  )
  let proposition = @logic.PrSymbol::new(context, b"goal", origin)
  let goal = @logic.Decl::proposition(
    context,
    origin,
    Pgoal,
    proposition,
    @logic.Term::true_formula(),
    None,
  )
  let task = @theory.Task::trusted_new(
    symbol.semantic_id(),
    [TheoryDecl(declaration), TheoryDecl(declaration), TheoryDecl(goal)],
    None,
  )
  let normalized = checked_task(
    task,
    task.view().items,
    @identity.SimplifyFormula,
  )
  assert_eq(normalized.view().items.length(), 2)
}
