// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn test_name(name : BytesView) -> @identity.Origin {
  @identity.Origin::user(name, None, [])
}

///|
fn test_theory_name(name : BytesView) -> @theory.SemanticName {
  @theory.SemanticName::new(name, [], None)
}

///|
test "namespace lookup is qualified and conflicting imports are rejected" {
  let context = @identity.CompilationContext::new()
  let left = @logic.TypeSymbol::new_abstract(
    context,
    b"t",
    test_name(b"t"),
    [],
    None,
  )
  let right = @logic.TypeSymbol::new_abstract(
    context,
    b"t",
    test_name(b"t"),
    [],
    None,
  )
  let inner = @theory.Namespace::empty().add_type(b"t", left, None)
  let outer = @theory.Namespace::empty().add_subspace(b"Inner", inner, None)
  assert_true(outer.find_type([b"Inner", b"t"], None) == left)
  let conflicting = @theory.Namespace::empty().add_type(b"t", right, None)
  try inner.merge(conflicting, None) catch {
    TheoryError(diagnostic) => assert_eq(diagnostic.kind, AmbiguousName)
  } noraise {
    _ => fail("expected ambiguous namespace import")
  }
}

///|
test "theory builder rejects cross-context imports" {
  let left_context = @identity.CompilationContext::new()
  let right_context = @identity.CompilationContext::new()
  let left = @theory.TheoryBuilder::new(
    left_context,
    @theory.TheoryKey::new([], b"Left"),
    test_theory_name(b"Left"),
  )
  let right = @theory.TheoryBuilder::new(
    right_context,
    @theory.TheoryKey::new([], b"Right"),
    test_theory_name(b"Right"),
  ).close()
  try left.add_use(right, true, None) catch {
    _ => ()
  } noraise {
    _ => fail("expected cross-context import rejection")
  }
}

///|
test "theory scopes inherit lookup and export only their local declarations" {
  let context = @identity.CompilationContext::new()
  let builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Scoped"),
    test_theory_name(b"Scoped"),
  )
  let outer = @logic.TypeSymbol::new_abstract(
    context,
    b"outer",
    test_name(b"outer"),
    [],
    None,
  )
  builder.add_decl(
    @logic.Decl::type_declaration(context, test_name(b"outer"), [outer], None),
    None,
  )
  builder.open_scope(b"Inner", None)
  assert_true(builder.current_namespace().find_type([b"outer"], None) == outer)
  let inner = @logic.TypeSymbol::new_abstract(
    context,
    b"inner",
    test_name(b"inner"),
    [],
    None,
  )
  builder.add_decl(
    @logic.Decl::type_declaration(context, test_name(b"inner"), [inner], None),
    None,
  )
  builder.close_scope(false, None)
  let exported = builder.close().export_namespace()
  assert_true(exported.find_type([b"outer"], None) == outer)
  assert_true(exported.find_type([b"Inner", b"inner"], None) == inner)
  try exported.find_type([b"inner"], None) catch {
    TheoryError(diagnostic) => assert_eq(diagnostic.kind, UnboundName)
  } noraise {
    _ => fail("expected the closed scope to remain qualified")
  }
}

///|
test "imported scope affects lookup without leaking into export" {
  let context = @identity.CompilationContext::new()
  let builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Scoped"),
    test_theory_name(b"Scoped"),
  )
  builder.open_scope(b"Inner", None)
  let inner = @logic.TypeSymbol::new_abstract(
    context,
    b"inner",
    test_name(b"inner"),
    [],
    None,
  )
  builder.add_decl(
    @logic.Decl::type_declaration(context, test_name(b"inner"), [inner], None),
    None,
  )
  builder.close_scope(false, None)
  builder.import_scope([b"Inner"], None)
  assert_true(builder.current_namespace().find_type([b"inner"], None) == inner)
  let exported = builder.close().export_namespace()
  try exported.find_type([b"inner"], None) catch {
    TheoryError(diagnostic) => assert_eq(diagnostic.kind, UnboundName)
  } noraise {
    _ => fail("expected scope import to remain resolution-only")
  }
}

///|
test "split_theory makes lemma goals and carries axioms forward" {
  let context = @identity.CompilationContext::new()
  let builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([b"demo"], b"Split"),
    test_theory_name(b"Split"),
  )
  let lemma_symbol = @logic.PrSymbol::new(
    context,
    b"lemma",
    test_name(b"lemma"),
  )
  let goal_symbol = @logic.PrSymbol::new(context, b"goal", test_name(b"goal"))
  builder.add_decl(
    @logic.Decl::proposition(
      context,
      test_name(b"lemma"),
      Plemma,
      lemma_symbol,
      @logic.Term::true_formula(),
      None,
    ),
    None,
  )
  builder.add_decl(
    @logic.Decl::proposition(
      context,
      test_name(b"goal"),
      Pgoal,
      goal_symbol,
      @logic.Term::true_formula(),
      None,
    ),
    None,
  )
  let tasks = @theory.split_theory(context, builder.close(), None)
  assert_eq(tasks.length(), 2)
  let first = tasks[0].view().items
  assert_eq(first.length(), 1)
  assert_true(first[0] is TheoryDecl(decl) && decl.view() is Dprop(Pgoal, _, _))
  let second = tasks[1].view().items
  assert_eq(second.length(), 2)
  assert_true(
    second[0] is TheoryDecl(decl) && decl.view() is Dprop(Paxiom, _, _),
  )
  assert_true(
    second[1] is TheoryDecl(decl) && decl.view() is Dprop(Pgoal, _, _),
  )
  assert_true(tasks[1].goal() == goal_symbol)
  guard tasks[1].head() is Some(goal_head) &&
    goal_head.view().task_prev is Some(previous_head) else {
    fail("task did not retain its linked declaration history")
  }
  assert_true(
    goal_head.view().task_decl.view().td_node is TheoryDecl(goal) &&
    goal.view() is Dprop(Pgoal, _, _) &&
    previous_head.view().task_decl.view().td_node is TheoryDecl(axiom) &&
    axiom.view() is Dprop(Paxiom, _, _),
  )
  assert_true(tasks[1].known() is Some(_))
}

///|
test "task invariant requires exactly one final goal" {
  let context = @identity.CompilationContext::new()
  let anchor = context.fresh_id()
  try @theory.Task::trusted_new(anchor, [], None) catch {
    TheoryError(diagnostic) => assert_eq(diagnostic.kind, MissingGoal)
  } noraise {
    _ => fail("expected missing goal rejection")
  }
}

///|
test "coercions form a checked transitive closure" {
  let context = @identity.CompilationContext::new()
  let source_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"source",
    test_name(b"source"),
    [],
    None,
  )
  let middle_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"middle",
    test_name(b"middle"),
    [],
    None,
  )
  let target_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"target",
    test_name(b"target"),
    [],
    None,
  )
  let source = @logic.Ty::app(source_symbol, [], None)
  let middle = @logic.Ty::app(middle_symbol, [], None)
  let target = @logic.Ty::app(target_symbol, [], None)
  let source_to_middle = @logic.LSymbol::new_function(
    context,
    b"source_to_middle",
    test_name(b"source_to_middle"),
    [source],
    middle,
    None,
  )
  let middle_to_target = @logic.LSymbol::new_function(
    context,
    b"middle_to_target",
    test_name(b"middle_to_target"),
    [middle],
    target,
    None,
  )
  let coercions = @theory.CoercionMap::empty()
    .add(source_to_middle, None)
    .add(middle_to_target, None)
  let path = coercions.find(source, target, None)
  assert_true(
    path.length() == 2 &&
    path[0] == source_to_middle &&
    path[1] == middle_to_target,
  )
  let target_to_source = @logic.LSymbol::new_function(
    context,
    b"target_to_source",
    test_name(b"target_to_source"),
    [target],
    source,
    None,
  )
  try coercions.add(target_to_source, None) catch {
    TheoryError(diagnostic) => assert_eq(diagnostic.kind, CoercionCycle)
  } noraise {
    _ => fail("expected a coercion cycle")
  }
  let alternate = @logic.LSymbol::new_function(
    context,
    b"alternate",
    test_name(b"alternate"),
    [source],
    middle,
    None,
  )
  try coercions.add(alternate, None) catch {
    TheoryError(diagnostic) =>
      assert_eq(diagnostic.kind, CoercionAlreadyDefined)
  } noraise {
    _ => fail("expected a duplicate coercion rejection")
  }
  let invalid = @logic.LSymbol::new_function(
    context,
    b"invalid",
    test_name(b"invalid"),
    [source, source],
    target,
    None,
  )
  try coercions.add(invalid, None) catch {
    TheoryError(diagnostic) => assert_eq(diagnostic.kind, NotACoercion)
  } noraise {
    _ => fail("expected an invalid coercion rejection")
  }
}

///|
test "registered metas validate signatures and update theory indexes" {
  let context = @identity.CompilationContext::new()
  let source_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"source",
    test_name(b"source"),
    [],
    None,
  )
  let target_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"target",
    test_name(b"target"),
    [],
    None,
  )
  let source = @logic.Ty::app(source_symbol, [], None)
  let target = @logic.Ty::app(target_symbol, [], None)
  let coercion = @logic.LSymbol::new_function(
    context,
    b"convert",
    test_name(b"convert"),
    [source],
    target,
    None,
  )
  let builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Metas"),
    test_theory_name(b"Metas"),
  )
  builder.add_decl(
    @logic.Decl::type_declaration(
      context,
      test_name(b"types"),
      [source_symbol, target_symbol],
      None,
    ),
    None,
  )
  builder.add_decl(
    @logic.Decl::parameter(context, test_name(b"convert"), coercion, None),
    None,
  )
  let descriptor = @theory.MetaDescriptor::new(
    b"coercion",
    [MetaLogicSymbolArgument],
    false,
    b"implicit coercion",
    None,
  )
  assert_eq(descriptor.view().description, b"implicit coercion")
  builder.add_meta(descriptor.apply([MetaLogicSymbol(coercion)], None), None)
  let theory = builder.close()
  let path = theory.coercions().find(source, target, None)
  assert_true(path.length() == 1 && path[0] == coercion)

  let type_tag = @theory.MetaDescriptor::new(
    b"type_tag",
    [MetaTypeArgument],
    true,
    b"type tag",
    None,
  )
  let application = type_tag.apply([MetaTypeSymbol(source_symbol)], None)
  assert_true(
    application.view().exclusive &&
    application.view().arguments is [MetaType(found)] &&
    found == source,
  )
  try type_tag.apply([], None) catch {
    TheoryError(diagnostic) => assert_eq(diagnostic.kind, BadMetaArity)
  } noraise {
    _ => fail("expected meta arity validation")
  }
}

///|
test "theory clone substitutes abstract types and records every fresh symbol" {
  let context = @identity.CompilationContext::new()
  let source_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Source"),
    test_theory_name(b"Source"),
  )
  let source_type = @logic.TypeSymbol::new_abstract(
    context,
    b"t",
    test_name(b"t"),
    [],
    None,
  )
  let source_ty = @logic.Ty::app(source_type, [], None)
  source_builder.add_decl(
    @logic.Decl::type_declaration(context, test_name(b"t"), [source_type], None),
    None,
  )
  let source_function = @logic.LSymbol::new_function(
    context,
    b"f",
    test_name(b"f"),
    [source_ty],
    source_ty,
    None,
  )
  source_builder.add_decl(
    @logic.Decl::parameter(context, test_name(b"f"), source_function, None),
    None,
  )
  let source_axiom = @logic.PrSymbol::new(
    context,
    b"source_axiom",
    test_name(b"source_axiom"),
  )
  source_builder.add_decl(
    @logic.Decl::proposition(
      context,
      test_name(b"source_axiom"),
      Paxiom,
      source_axiom,
      @logic.Term::true_formula(),
      None,
    ),
    None,
  )
  let source = source_builder.close()

  let target_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Target"),
    test_theory_name(b"Target"),
  )
  let target_type = @logic.TypeSymbol::new_abstract(
    context,
    b"u",
    test_name(b"u"),
    [],
    None,
  )
  let target_ty = @logic.Ty::app(target_type, [], None)
  target_builder.add_decl(
    @logic.Decl::type_declaration(context, test_name(b"u"), [target_type], None),
    None,
  )
  let instantiation = @theory.TheoryInstantiation::new(
    [(source_type, target_ty)],
    [],
    [],
    [],
    Plemma,
    None,
  )
  let symbol_map = target_builder.add_clone(source, instantiation, None)
  assert_true(symbol_map.find_type(source_type) == Some(target_ty))
  guard symbol_map.find_logic_symbol(source_function) is Some(cloned_function) else {
    fail("clone did not record the cloned function")
  }
  let cloned_function_view = cloned_function.view()
  assert_true(
    cloned_function != source_function &&
    cloned_function_view.argument_types == [target_ty] &&
    cloned_function_view.result_type == Some(target_ty),
  )
  guard symbol_map.find_proposition(source_axiom) is Some(cloned_axiom) else {
    fail("clone did not record the cloned axiom")
  }
  let target = target_builder.close()
  assert_true(
    target.export_namespace().find_logic([b"f"], None) == cloned_function,
  )
  try target.export_namespace().find_type([b"t"], None) catch {
    TheoryError(diagnostic) => assert_eq(diagnostic.kind, UnboundName)
  } noraise {
    _ => fail("a concrete type instance must erase the source type binding")
  }
  assert_true(
    target.view().items.any(item => {
      item is TheoryDecl(declaration) &&
      declaration.view() is Dprop(Plemma, proposition, _) &&
      proposition == cloned_axiom
    }),
  )
  guard target.view().items.last() is Some(TheoryClone(witness)) else {
    fail("clone did not append its source/symbol-map witness")
  }
  assert_true(witness.view().source == source.key())
}

///|
test "theory clone checks explicit logic signatures and rewrites binders" {
  let context = @identity.CompilationContext::new()
  let source_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Predicates"),
    test_theory_name(b"Predicates"),
  )
  let source_type = @logic.TypeSymbol::new_abstract(
    context,
    b"a",
    test_name(b"a"),
    [],
    None,
  )
  let source_ty = @logic.Ty::app(source_type, [], None)
  source_builder.add_decl(
    @logic.Decl::type_declaration(context, test_name(b"a"), [source_type], None),
    None,
  )
  let source_predicate = @logic.LSymbol::new_predicate(
    context,
    b"p",
    test_name(b"p"),
    [source_ty],
    None,
  )
  source_builder.add_decl(
    @logic.Decl::parameter(context, test_name(b"p"), source_predicate, None),
    None,
  )
  let variable = @logic.VSymbol::new(
    context,
    b"x",
    test_name(b"x"),
    source_ty,
    None,
  )
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    [variable],
    [],
    @logic.Term::apply_predicate(
      source_predicate,
      [@logic.Term::variable(variable)],
      None,
    ),
    None,
  )
  let source_axiom = @logic.PrSymbol::new(
    context,
    b"all_p",
    test_name(b"all_p"),
  )
  source_builder.add_decl(
    @logic.Decl::proposition(
      context,
      test_name(b"all_p"),
      Paxiom,
      source_axiom,
      formula,
      None,
    ),
    None,
  )
  let source = source_builder.close()

  let target_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"PredicateTarget"),
    test_theory_name(b"PredicateTarget"),
  )
  let target_type = @logic.TypeSymbol::new_abstract(
    context,
    b"b",
    test_name(b"b"),
    [],
    None,
  )
  let target_ty = @logic.Ty::app(target_type, [], None)
  target_builder.add_decl(
    @logic.Decl::type_declaration(context, test_name(b"b"), [target_type], None),
    None,
  )
  let target_predicate = @logic.LSymbol::new_predicate(
    context,
    b"q",
    test_name(b"q"),
    [target_ty],
    None,
  )
  target_builder.add_decl(
    @logic.Decl::parameter(context, test_name(b"q"), target_predicate, None),
    None,
  )
  let instantiation = @theory.TheoryInstantiation::new(
    [(source_type, target_ty)],
    [],
    [(source_predicate, target_predicate)],
    [],
    Plemma,
    None,
  )
  let symbol_map = target_builder.add_clone(source, instantiation, None)
  assert_true(
    symbol_map.find_logic_symbol(source_predicate) == Some(target_predicate),
  )
  guard symbol_map.find_proposition(source_axiom) is Some(cloned_axiom) else {
    fail("clone did not produce the translated proposition")
  }
  let target = target_builder.close()
  let mut cloned_declaration : @logic.Decl? = None
  for item in target.view().items {
    if item is TheoryDecl(declaration) &&
      declaration.view() is Dprop(_, proposition, _) &&
      proposition == cloned_axiom {
      cloned_declaration = Some(declaration)
    }
  }
  guard cloned_declaration is Some(cloned_declaration) else {
    fail("translated proposition is absent")
  }
  guard cloned_declaration.view() is Dprop(Plemma, _, cloned_formula) &&
    cloned_formula.view() is Tquant(_, [cloned_variable], _, cloned_body) &&
    cloned_body.view() is Tapp(cloned_predicate, _, [argument]) &&
    argument.view() is Tvar(argument_variable) else {
    fail("translated quantified proposition has the wrong shape")
  }
  assert_true(
    cloned_predicate == target_predicate &&
    cloned_variable != variable &&
    cloned_variable.ty() == target_ty &&
    argument_variable == cloned_variable,
  )

  let generalized_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"GeneralizedPredicateTarget"),
    test_theory_name(b"GeneralizedPredicateTarget"),
  )
  generalized_builder.add_use(target, false, None)
  let generalized_variable = @logic.TyVarSymbol::new(
    context,
    b"g",
    test_name(b"g"),
  )
  let generalized_predicate = @logic.LSymbol::new_predicate(
    context,
    b"generalized",
    test_name(b"generalized"),
    [@logic.Ty::variable(generalized_variable)],
    None,
  )
  generalized_builder.add_decl(
    @logic.Decl::parameter(
      context,
      test_name(b"generalized"),
      generalized_predicate,
      None,
    ),
    None,
  )
  let generalized_instantiation = @theory.TheoryInstantiation::new(
    [(source_type, target_ty)],
    [],
    [(source_predicate, generalized_predicate)],
    [],
    Plemma,
    None,
  )
  let generalized_map = generalized_builder.add_clone(
    source,
    generalized_instantiation,
    None,
  ) catch {
    @logic.TypeError(diagnostic) =>
      fail("generalized logic clone failed: \{diagnostic.message}")
    @theory.TheoryError(diagnostic) =>
      fail("generalized logic clone failed: \{diagnostic.message}")
    _ => fail("generalized logic clone raised another error")
  }
  assert_true(
    generalized_map.find_logic_symbol(source_predicate) ==
    Some(generalized_predicate),
  )

  let incompatible = @logic.LSymbol::new_predicate(
    context,
    b"bad",
    test_name(b"bad"),
    [],
    None,
  )
  let incompatible_instantiation = @theory.TheoryInstantiation::new(
    [(source_type, target_ty)],
    [],
    [(source_predicate, incompatible)],
    [],
    Plemma,
    None,
  )
  let incompatible_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Incompatible"),
    test_theory_name(b"Incompatible"),
  )
  try
    incompatible_builder.add_clone(source, incompatible_instantiation, None)
  catch {
    @theory.TheoryError(diagnostic) =>
      assert_eq(diagnostic.kind, CloneLogicArityMismatch)
    _ => fail("unexpected error from incompatible logic clone instance")
  } noraise {
    _ => fail("expected an incompatible logic clone instance")
  }
}

///|
test "theory clone rejects non-local and defined type substitutions" {
  let context = @identity.CompilationContext::new()
  let base_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Base"),
    test_theory_name(b"Base"),
  )
  let base_type = @logic.TypeSymbol::new_abstract(
    context,
    b"base",
    test_name(b"base"),
    [],
    None,
  )
  let base_ty = @logic.Ty::app(base_type, [], None)
  base_builder.add_decl(
    @logic.Decl::type_declaration(
      context,
      test_name(b"base"),
      [base_type],
      None,
    ),
    None,
  )
  let base = base_builder.close()

  let source_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Aliases"),
    test_theory_name(b"Aliases"),
  )
  source_builder.add_use(base, true, None)
  let alias_symbol = @logic.TypeSymbol::new_alias(
    context,
    b"alias",
    test_name(b"alias"),
    [],
    base_ty,
    None,
  )
  source_builder.add_decl(
    @logic.Decl::type_declaration(
      context,
      test_name(b"alias"),
      [alias_symbol],
      None,
    ),
    None,
  )
  let source = source_builder.close()
  let target_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"CloneErrors"),
    test_theory_name(b"CloneErrors"),
  )
  target_builder.add_use(base, true, None)
  try
    target_builder.add_clone(
      source,
      @theory.TheoryInstantiation::new(
        [(base_type, base_ty)],
        [],
        [],
        [],
        Plemma,
        None,
      ),
      None,
    )
  catch {
    @theory.TheoryError(diagnostic) =>
      assert_eq(diagnostic.kind, NonLocalCloneSymbol)
    _ => fail("unexpected error from non-local clone instance")
  } noraise {
    _ => fail("expected a non-local clone instance rejection")
  }
  try
    target_builder.add_clone(
      source,
      @theory.TheoryInstantiation::new(
        [(alias_symbol, base_ty)],
        [],
        [],
        [],
        Plemma,
        None,
      ),
      None,
    )
  catch {
    @theory.TheoryError(diagnostic) =>
      assert_eq(diagnostic.kind, CannotInstantiate)
    _ => fail("unexpected error from defined type clone instance")
  } noraise {
    _ => fail("expected a defined type clone instance rejection")
  }
  let target = target_builder.close()
  assert_true(target.view().items.all(item => !(item is TheoryClone(_))))
  try target.export_namespace().find_type([b"alias"], None) catch {
    TheoryError(diagnostic) => assert_eq(diagnostic.kind, UnboundName)
  } noraise {
    _ => fail("a rejected clone partially mutated its destination builder")
  }
}

///|
test "theory clone rebuilds data, coinductive, and meta declarations" {
  let context = @identity.CompilationContext::new()
  let source_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Structured"),
    test_theory_name(b"Structured"),
  )
  let field_type = @logic.TypeSymbol::new_abstract(
    context,
    b"field_type",
    test_name(b"field_type"),
    [],
    None,
  )
  let field_ty = @logic.Ty::app(field_type, [], None)
  source_builder.add_decl(
    @logic.Decl::type_declaration(
      context,
      test_name(b"field_type"),
      [field_type],
      None,
    ),
    None,
  )
  let record_type = @logic.TypeSymbol::new_abstract(
    context,
    b"record_type",
    test_name(b"record_type"),
    [],
    None,
  )
  let record_ty = @logic.Ty::app(record_type, [], None)
  let field = @logic.LSymbol::new_projection(
    context,
    b"field",
    test_name(b"field"),
    record_ty,
    field_ty,
    None,
  )
  let make_record = @logic.LSymbol::new_constructor(
    context,
    b"make_record",
    test_name(b"make_record"),
    [field_ty],
    record_ty,
    1,
    None,
  )
  let data_constructor = @logic.DataConstructor::new(
    make_record,
    [Some(field)],
    None,
  )
  source_builder.add_decl(
    @logic.Decl::data(
      context,
      test_name(b"record_type"),
      [@logic.DataDeclaration::new(record_type, [data_constructor], None)],
      None,
    ),
    None,
  )
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"productive",
    test_name(b"productive"),
    [record_ty],
    None,
  )
  let variable = @logic.VSymbol::new(
    context,
    b"x",
    test_name(b"x"),
    record_ty,
    None,
  )
  let case_formula = @logic.Term::quantify(
    ForallQuantifier,
    [variable],
    [],
    @logic.Term::apply_predicate(
      predicate,
      [@logic.Term::variable(variable)],
      None,
    ),
    None,
  )
  let case_proposition = @logic.PrSymbol::new(
    context,
    b"productive_intro",
    test_name(b"productive_intro"),
  )
  source_builder.add_decl(
    @logic.Decl::inductive(
      context,
      test_name(b"productive"),
      Coind,
      [
        @logic.InductiveDeclaration::new(
          predicate,
          [
            @logic.InductiveCase::new(
              context,
              case_proposition,
              case_formula,
              None,
            ),
          ],
          None,
        ),
      ],
      None,
    ),
    None,
  )
  let projection_meta = @theory.MetaDescriptor::new(
    b"model_projection",
    [MetaLogicSymbolArgument],
    false,
    b"record projection",
    None,
  )
  source_builder.add_meta(
    projection_meta.apply([MetaLogicSymbol(field)], None),
    None,
  )
  let source = source_builder.close()

  let target_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"StructuredClone"),
    test_theory_name(b"StructuredClone"),
  )
  let symbol_map = target_builder.add_clone(
    source,
    @theory.TheoryInstantiation::empty(),
    None,
  )
  guard symbol_map.find_type_symbol(record_type) is Some(cloned_record_type) &&
    symbol_map.find_logic_symbol(make_record) is Some(cloned_constructor) &&
    symbol_map.find_logic_symbol(field) is Some(cloned_field) &&
    symbol_map.find_logic_symbol(predicate) is Some(cloned_predicate) &&
    symbol_map.find_proposition(case_proposition) is Some(cloned_case) else {
    fail("structured clone omitted a symbol correspondence")
  }
  assert_true(
    cloned_record_type != record_type &&
    cloned_constructor != make_record &&
    cloned_field != field &&
    cloned_predicate != predicate &&
    cloned_case != case_proposition,
  )
  assert_true(
    cloned_field.semantic_id().local_id() <
    cloned_constructor.semantic_id().local_id(),
  )
  let target = target_builder.close()
  let mut clone_map_keeps_source_allocation_order = false
  for item in target.view().items {
    guard item is TheoryClone(witness) else { continue }
    let mut saw_field = false
    for entry in witness.view().logic_instantiations {
      let source_symbol = entry.0
      if source_symbol == field {
        saw_field = true
      } else if source_symbol == make_record {
        clone_map_keeps_source_allocation_order = saw_field
      }
    }
  }
  assert_true(clone_map_keeps_source_allocation_order)
  assert_true(
    target.view().items.any(item => {
      item is TheoryDecl(declaration) &&
      declaration.view() is Ddata([data]) &&
      data.view().type_symbol == cloned_record_type &&
      data.view().constructors is [cloned_data_constructor] &&
      cloned_data_constructor.view().symbol == cloned_constructor &&
      cloned_data_constructor.view().projections == [Some(cloned_field)]
    }),
  )
  assert_true(
    target.view().items.any(item => {
      item is TheoryDecl(declaration) &&
      declaration.view() is Dind(Coind, [inductive]) &&
      inductive.view().predicate == cloned_predicate &&
      inductive.view().cases is [case_] &&
      case_.view().proposition == cloned_case
    }),
  )
  assert_true(
    target.view().items.any(item => {
      item is TheoryMeta(meta) &&
      meta.view()
      is { name: b"model_projection", arguments: [MetaLogicSymbol(symbol)], .. } &&
      symbol == cloned_field
    }),
  )
}

///|
test "task caches preserve meta history, exclusivity, and tagging selectors" {
  let context = @identity.CompilationContext::new()
  let builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"TaskMetas"),
    test_theory_name(b"TaskMetas"),
  )
  let type_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"tagged",
    test_name(b"tagged"),
    [],
    None,
  )
  builder.add_decl(
    @logic.Decl::type_declaration(
      context,
      test_name(b"tagged"),
      [type_symbol],
      None,
    ),
    None,
  )
  let tag_descriptor = @theory.MetaDescriptor::new(
    b"tag_type",
    [MetaTypeSymbolArgument],
    false,
    b"type tag",
    None,
  )
  let tag = tag_descriptor.apply([MetaTypeSymbol(type_symbol)], None)
  builder.add_meta(tag, None)
  builder.add_meta(tag, None)
  let exclusive_descriptor = @theory.MetaDescriptor::new(
    b"exclusive_counter",
    [MetaIntegerArgument],
    true,
    b"exclusive counter",
    None,
  )
  let first = exclusive_descriptor.apply([MetaInteger(1L)], None)
  let second = exclusive_descriptor.apply([MetaInteger(2L)], None)
  builder.add_meta(first, None)
  builder.add_meta(second, None)
  let goal = @logic.PrSymbol::new(
    context,
    b"meta_goal",
    test_name(b"meta_goal"),
  )
  builder.add_decl(
    @logic.Decl::proposition(
      context,
      test_name(b"meta_goal"),
      Pgoal,
      goal,
      @logic.Term::true_formula(),
      None,
    ),
    None,
  )
  let tasks = @theory.split_theory(context, builder.close(), None)
  guard tasks is [task] else { fail("expected one meta task") }
  assert_eq(task.meta_applications(tag).length(), 2)
  let tagged = task.tagged_type_symbols(tag, None)
  assert_true(tagged == [type_symbol])
  assert_true(task.exclusive_meta(first, None) is Some([MetaInteger(2L)]))
}

///|
test "vc:proved_wf validates and indexes the encoded relation lambda" {
  let context = @identity.CompilationContext::new()
  let builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"WellFounded"),
    test_theory_name(b"WellFounded"),
  )
  let element_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"element",
    test_name(b"element"),
    [],
    None,
  )
  let boolean_symbol = @logic.TypeSymbol::new_builtin(
    context,
    b"bool",
    test_name(b"bool"),
    BuiltinBoolean,
  )
  let parameter_left = @logic.TyVarSymbol::new(context, b"a", test_name(b"a"))
  let parameter_right = @logic.TyVarSymbol::new(context, b"b", test_name(b"b"))
  let function_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"infix ->",
    test_name(b"infix ->"),
    [parameter_left, parameter_right],
    None,
  )
  builder.add_decl(
    @logic.Decl::type_declaration(
      context,
      test_name(b"well_founded_types"),
      [element_symbol, boolean_symbol, function_symbol],
      None,
    ),
    None,
  )
  let element_ty = @logic.Ty::app(element_symbol, [], None)
  let boolean_ty = @logic.Ty::app(boolean_symbol, [], None)
  let inner_function_ty = @logic.Ty::app(
    function_symbol,
    [element_ty, boolean_ty],
    None,
  )
  let relation_function_ty = @logic.Ty::app(
    function_symbol,
    [element_ty, inner_function_ty],
    None,
  )
  let apply_outer = @logic.LSymbol::new_function(
    context,
    b"apply_outer",
    test_name(b"apply_outer"),
    [relation_function_ty, element_ty],
    inner_function_ty,
    None,
  )
  let apply_inner = @logic.LSymbol::new_function(
    context,
    b"apply_inner",
    test_name(b"apply_inner"),
    [inner_function_ty, element_ty],
    boolean_ty,
    None,
  )
  let equality = @logic.LSymbol::new_predicate(
    context,
    b"infix =",
    test_name(b"infix ="),
    [boolean_ty, boolean_ty],
    None,
  )
  let true_value = @logic.LSymbol::new_function(
    context,
    b"True",
    test_name(b"True"),
    [],
    boolean_ty,
    None,
  )
  let relation = @logic.LSymbol::new_predicate(
    context,
    b"relation",
    test_name(b"relation"),
    [element_ty, element_ty],
    None,
  )
  let well_founded = @logic.LSymbol::new_predicate(
    context,
    b"well_founded",
    test_name(b"well_founded"),
    [relation_function_ty],
    None,
  )
  for
    symbol in [
      apply_outer, apply_inner, equality, true_value, relation, well_founded,
    ] {
    builder.add_decl(
      @logic.Decl::parameter(context, symbol.view().origin, symbol, None),
      None,
    )
  }
  let function_variable = @logic.VSymbol::new(
    context,
    b"fc",
    test_name(b"fc"),
    relation_function_ty,
    None,
  )
  let left = @logic.VSymbol::new(
    context,
    b"x",
    test_name(b"x"),
    element_ty,
    None,
  )
  let right = @logic.VSymbol::new(
    context,
    b"y",
    test_name(b"y"),
    element_ty,
    None,
  )
  let applied_function = @logic.Term::apply_function(
    apply_inner,
    [
      @logic.Term::apply_function(
        apply_outer,
        [@logic.Term::variable(function_variable), @logic.Term::variable(left)],
        None,
      ),
      @logic.Term::variable(right),
    ],
    None,
  )
  let function_side = @logic.Term::apply_predicate(
    equality,
    [applied_function, @logic.Term::apply_function(true_value, [], None)],
    None,
  )
  let relation_side = @logic.Term::apply_predicate(
    relation,
    [@logic.Term::variable(left), @logic.Term::variable(right)],
    None,
  )
  let encoded_lambda = @logic.Term::epsilon(
    function_variable,
    @logic.Term::quantify(
      ForallQuantifier,
      [left, right],
      [],
      @logic.Term::binary(Iff, function_side, relation_side, None),
      None,
    ),
    None,
  )
  let proof = @logic.PrSymbol::new(
    context,
    b"relation_wf",
    test_name(b"relation_wf"),
  )
  builder.add_decl(
    @logic.Decl::proposition(
      context,
      test_name(b"relation_wf"),
      Plemma,
      proof,
      @logic.Term::apply_predicate(well_founded, [encoded_lambda], None),
      None,
    ),
    None,
  )
  let descriptor = @theory.MetaDescriptor::new(
    b"vc:proved_wf",
    [MetaLogicSymbolArgument, MetaPropositionSymbolArgument],
    false,
    b"proved well-founded relation",
    None,
  )
  builder.add_meta(
    descriptor.apply(
      [MetaLogicSymbol(relation), MetaPropositionSymbol(proof)],
      None,
    ),
    None,
  )
  assert_true(
    builder.close().proved_wf(relation) == Some((proof, well_founded)),
  )
}

///|
test "task splitting suppresses cloned instances of proved lemmas" {
  let context = @identity.CompilationContext::new()
  let source_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"ProvedSource"),
    test_theory_name(b"ProvedSource"),
  )
  let source_lemma = @logic.PrSymbol::new(
    context,
    b"already_proved",
    test_name(b"already_proved"),
  )
  source_builder.add_decl(
    @logic.Decl::proposition(
      context,
      test_name(b"already_proved"),
      Plemma,
      source_lemma,
      @logic.Term::true_formula(),
      None,
    ),
    None,
  )
  let source = source_builder.close()
  let target_builder = @theory.TheoryBuilder::new(
    context,
    @theory.TheoryKey::new([], b"ProvedTarget"),
    test_theory_name(b"ProvedTarget"),
  )
  let symbol_map = target_builder.add_clone(
    source,
    @theory.TheoryInstantiation::empty(),
    None,
  )
  guard symbol_map.find_proposition(source_lemma) is Some(cloned_lemma) else {
    fail("lemma clone did not produce a proposition correspondence")
  }
  let independent_goal = @logic.PrSymbol::new(
    context,
    b"independent",
    test_name(b"independent"),
  )
  target_builder.add_decl(
    @logic.Decl::proposition(
      context,
      test_name(b"independent"),
      Pgoal,
      independent_goal,
      @logic.Term::true_formula(),
      None,
    ),
    None,
  )
  let tasks = @theory.split_theory(context, target_builder.close(), None)
  guard tasks is [task] else {
    fail("cloned proved lemma unexpectedly generated another task")
  }
  assert_true(task.goal() == independent_goal)
  assert_true(task.goal() != cloned_lemma)
  assert_eq(task.cloned_theory_maps(source).length(), 1)
}
