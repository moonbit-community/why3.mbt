// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn compile_match_wildcard_fixture(
  context : @identity.CompilationContext,
) -> (@logic.Term, @logic.LSymbol) raise @logic.TypeError {
  let origin = fn(name : BytesView) { @identity.Origin::user(name, None, []) }
  let payload_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"payload",
    origin(b"payload"),
    [],
    None,
  )
  let payload_type = @logic.Ty::app(payload_symbol, [], None)
  let sum_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"sum",
    origin(b"sum"),
    [],
    None,
  )
  let sum_type = @logic.Ty::app(sum_symbol, [], None)
  let constructor = @logic.LSymbol::new_constructor(
    context,
    b"Wrap",
    origin(b"Wrap"),
    [payload_type],
    sum_type,
    1,
    None,
  )
  let scrutinee = @logic.VSymbol::new(
    context,
    b"value",
    origin(b"value"),
    sum_type,
    None,
  )
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    [scrutinee],
    [],
    @logic.Term::case(
      @logic.Term::variable(scrutinee),
      [
        (
          @logic.Pattern::app(
            constructor,
            [@logic.Pattern::wild(payload_type)],
            sum_type,
            None,
          ),
          @logic.Term::true_formula(),
        ),
      ],
      None,
    ),
    None,
  )
  (formula, constructor)
}

///|
test "compile_match gives wildcard constructor fields primitive binders" {
  let context = @identity.CompilationContext::new()
  let (formula, constructor) = compile_match_wildcard_fixture(context)
  guard compile_match_term(context, formula, true).view()
    is Tquant(ForallQuantifier, _, _, body) &&
    body.view() is Tcase(_, [branch]) &&
    branch.view().pattern.view() is Papp(actual, [argument], _) &&
    actual == constructor &&
    argument.view() is Pvar(_) else {
    fail("compile_match retained a nested wildcard constructor pattern")
  }
}

///|
fn discrimination_test_origin(name : BytesView) -> @identity.Origin {
  @identity.Origin::user(name, None, [])
}

///|
test "goal-dependent kept types retain result-before-argument discovery order" {
  let context = @identity.CompilationContext::new()
  let parameter = @logic.TyVarSymbol::new(
    context,
    b"p",
    discrimination_test_origin(b"p"),
  )
  let argument_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"a",
    @identity.Origin::generated(
      @identity.DiscriminateMonomorphiseGoal,
      b"a",
      None,
      [],
    ),
    [],
    None,
  )
  let argument = @logic.Ty::app(argument_symbol, [], None)
  let value_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"value",
    discrimination_test_origin(b"value"),
    [parameter],
    None,
  )
  let tree_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"tree",
    discrimination_test_origin(b"tree"),
    [parameter],
    None,
  )
  let model_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"model",
    discrimination_test_origin(b"model"),
    [parameter],
    None,
  )
  // Allocation order deliberately disagrees with the instance signature.
  let value = @logic.Ty::app(value_symbol, [argument], None)
  let tree = @logic.Ty::app(tree_symbol, [argument], None)
  let model = @logic.Ty::app(model_symbol, [argument], None)
  let discovery = [tree, value, model]
  let ordered = [value, tree, model]
  ordered.sort_by((left, right) => {
    compare_discrimination_kept_type_with_discovery(
      left,
      right,
      Some(discovery),
    )
  })
  assert_true(
    ordered.length() == 3 &&
    ordered[0] == tree &&
    ordered[1] == value &&
    ordered[2] == model,
  )
  let sequence_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"sequence",
    discrimination_test_origin(b"sequence"),
    [parameter],
    None,
  )
  let sequence = @logic.Ty::app(sequence_symbol, [argument], None)
  let direct_goal_order = [sequence, argument]
  direct_goal_order.sort_by((left, right) => {
    compare_discrimination_kept_type_with_discovery(
      left,
      right,
      Some([sequence, argument]),
    )
  })
  assert_true(
    direct_goal_order.length() == 2 &&
    direct_goal_order[0] == argument &&
    direct_goal_order[1] == sequence,
  )
  let nested_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"nested",
    discrimination_test_origin(b"nested"),
    [parameter],
    None,
  )
  let nested = @logic.Ty::app(nested_symbol, [value], None)
  let depth_order = [nested, tree]
  depth_order.sort_by((left, right) => {
    compare_discrimination_kept_type_with_discovery(
      left,
      right,
      Some([nested, tree]),
    )
  })
  assert_true(
    depth_order.length() == 2 &&
    depth_order[0] == tree &&
    depth_order[1] == nested,
  )
}

///|
test "monomorphise_goal declares free type variables in identifier order" {
  let context = @identity.CompilationContext::new()
  let origin = discrimination_test_origin(b"monomorphise-goal-order")
  // Why3's Stv order follows allocation order, while the formula below
  // deliberately discovers the variables in the opposite order.
  let d = @logic.TyVarSymbol::new(context, b"d", origin)
  let a = @logic.TyVarSymbol::new(context, b"a", origin)
  let d_type = @logic.Ty::variable(d)
  let a_type = @logic.Ty::variable(a)
  let a_value = @logic.VSymbol::new(context, b"a_value", origin, a_type, None)
  let d_value = @logic.VSymbol::new(context, b"d_value", origin, d_type, None)
  let formula = @logic.Term::binary(
    And,
    @logic.Term::quantify(
      ForallQuantifier,
      [a_value],
      [],
      @logic.Term::true_formula(),
      None,
    ),
    @logic.Term::quantify(
      ForallQuantifier,
      [d_value],
      [],
      @logic.Term::true_formula(),
      None,
    ),
    None,
  )
  let proposition = @logic.PrSymbol::new(context, b"goal", origin)
  let goal = @logic.Decl::proposition(
    context,
    origin,
    Pgoal,
    proposition,
    formula,
    None,
  )
  let task = @theory.Task::trusted_new(
    context.fresh_id(),
    [TheoryDecl(goal)],
    None,
  )
  let transformed = discriminate_monomorphise_goal(context, task)
  guard transformed.view().items
    is [
      TheoryDecl(first),
      TheoryDecl(second),
      TheoryDecl(_),
    ] &&
    first.view() is Dtype([first_symbol]) &&
    second.view() is Dtype([second_symbol]) else {
    fail("monomorphise_goal produced an unexpected declaration sequence")
  }
  assert_eq(first_symbol.view().name, b"d")
  assert_eq(second_symbol.view().name, b"a")
  let transformed_again = discriminate_monomorphise_goal(context, task)
  guard transformed_again.view().items
    is [
      TheoryDecl(first_again),
      TheoryDecl(second_again),
      TheoryDecl(_),
    ] &&
    first_again.view() is Dtype([first_symbol_again]) &&
    second_again.view() is Dtype([second_symbol_again]) else {
    fail("monomorphise_goal did not preserve its declaration sequence")
  }
  assert_true(
    first_symbol_again.semantic_id() == first_symbol.semantic_id() &&
    second_symbol_again.semantic_id() == second_symbol.semantic_id(),
  )
  assert_true(
    !upstream_kept_type_shape_equal(
      @logic.Ty::app(first_symbol, [], None),
      @logic.Ty::app(second_symbol, [], None),
    ),
  )
}

///|
test "algebraic instances use type allocation order within one constructor" {
  let context = @identity.CompilationContext::new()
  let origin = discrimination_test_origin(b"algebraic-instance-order")
  let parameter = @logic.TyVarSymbol::new(context, b"a", origin)
  let first_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"first",
    origin,
    [],
    None,
  )
  let second_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"second",
    origin,
    [],
    None,
  )
  let container_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"container",
    origin,
    [parameter],
    None,
  )
  let first = @logic.Ty::app(first_symbol, [], None)
  let second = @logic.Ty::app(second_symbol, [], None)
  let first_container = @logic.Ty::app(container_symbol, [first], None)
  let second_container = @logic.Ty::app(container_symbol, [second], None)
  let reversed = [second_container, first_container]
  reversed.sort_by(compare_discriminated_algebraic_types)
  assert_true(
    reversed.length() == 2 &&
    reversed[0] == first_container &&
    reversed[1] == second_container,
  )
}

///|
test "select-kept preserves discovery subject to type dependencies" {
  let context = @identity.CompilationContext::new()
  let parameter = @logic.TyVarSymbol::new(
    context,
    b"p",
    discrimination_test_origin(b"p"),
  )
  let goal_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"a",
    @identity.Origin::generated(
      @identity.DiscriminateMonomorphiseGoal,
      b"a",
      None,
      [],
    ),
    [],
    None,
  )
  let goal = @logic.Ty::app(goal_symbol, [], None)
  let unary = fn(name : BytesView) -> @logic.TypeSymbol raise @logic.TypeError {
    @logic.TypeSymbol::new_abstract(
      context,
      name,
      discrimination_test_origin(name),
      [parameter],
      None,
    )
  }
  let tree = @logic.Ty::app(unary(b"tree"), [goal], None)
  let element = @logic.Ty::app(unary(b"element"), [goal], None)
  let sequence = @logic.Ty::app(unary(b"sequence"), [element], None)
  let program = @logic.Ty::app(unary(b"program"), [goal], None)
  let model = @logic.Ty::app(unary(b"model"), [goal], None)
  let result_parameter = @logic.TyVarSymbol::new(
    context,
    b"r",
    discrimination_test_origin(b"r"),
  )
  let function_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"infix ->",
    @identity.Origin::user(b"infix ->", None, [b"why3:builtin:function-type"]),
    [parameter, result_parameter],
    None,
  )
  let function = @logic.Ty::app(function_symbol, [element, program], None)
  let later_function = @logic.Ty::app(function_symbol, [program, element], None)
  guard element.view() is TyApp(element_symbol, _) &&
    program.view() is TyApp(program_symbol, _) else {
    fail("kept-order fixture lost its unary type shapes")
  }
  let later_goal_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"a2",
    @identity.Origin::generated(
      @identity.DiscriminateMonomorphiseGoal,
      b"a2",
      None,
      [],
    ),
    [],
    None,
  )
  let later_goal = @logic.Ty::app(later_goal_symbol, [], None)
  let rediscovered_function = @logic.Ty::app(
    function_symbol,
    [
      @logic.Ty::app(element_symbol, [later_goal], None),
      @logic.Ty::app(program_symbol, [later_goal], None),
    ],
    None,
  )
  let later_view = @logic.Ty::app(unary(b"view"), [later_goal], None)
  ignore(order_upstream_kept_types([tree]))
  ignore(order_upstream_kept_types([sequence, goal]))
  let first_discovery = [sequence, function, tree, element]
  let first_ordered = order_upstream_kept_types(first_discovery)
  assert_true(
    first_ordered.length() == 4 &&
    first_ordered[0] == tree &&
    first_ordered[1] == element &&
    first_ordered[2] == sequence &&
    first_ordered[3] == function,
  )
  let discovery = [
    tree, sequence, element, later_function, function, program, model,
  ]
  let ordered = order_upstream_kept_types(discovery)
  assert_true(
    ordered.length() == 7 &&
    ordered[0] == tree &&
    ordered[1] == element &&
    ordered[2] == sequence &&
    ordered[3] == program &&
    ordered[4] == function &&
    ordered[5] == model &&
    ordered[6] == later_function,
  )
  let rediscovered = order_upstream_kept_types([
    later_function, rediscovered_function,
  ])
  assert_true(
    rediscovered.length() == 2 &&
    rediscovered[0] == rediscovered_function &&
    rediscovered[1] == later_function,
  )
  let prior_shape = order_upstream_kept_types([
    later_view, rediscovered_function,
  ])
  assert_true(
    prior_shape.length() == 2 &&
    prior_shape[0] == rediscovered_function &&
    prior_shape[1] == later_view,
  )
  let rediscovered_shapes = order_upstream_kept_types([
    later_view, rediscovered_function,
  ])
  assert_true(
    rediscovered_shapes.length() == 2 &&
    rediscovered_shapes[0] == rediscovered_function &&
    rediscovered_shapes[1] == later_view,
  )
}

///|
test "existing kept chronology precedes later select-kept types" {
  let context = @identity.CompilationContext::new()
  let parameter = @logic.TyVarSymbol::new(
    context,
    b"p",
    discrimination_test_origin(b"p"),
  )
  let result_parameter = @logic.TyVarSymbol::new(
    context,
    b"r",
    discrimination_test_origin(b"r"),
  )
  let function_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"infix ->",
    @identity.Origin::user(b"infix ->", None, [b"why3:builtin:function-type"]),
    [parameter, result_parameter],
    None,
  )
  let allocated_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"allocated",
    discrimination_test_origin(b"allocated"),
    [parameter],
    None,
  )
  let goal = fn(name : BytesView) -> @logic.Ty raise @logic.TypeError {
    @logic.Ty::app(
      @logic.TypeSymbol::new_abstract(
        context,
        name,
        @identity.Origin::generated(
          @identity.DiscriminateMonomorphiseGoal,
          name,
          None,
          [],
        ),
        [],
        None,
      ),
      [],
      None,
    )
  }
  let first_goal = goal(b"a1")
  let later_goal = goal(b"a2")
  let first_function = @logic.Ty::app(
    function_symbol,
    [first_goal, first_goal],
    None,
  )
  ignore(order_upstream_kept_types([first_function]))
  let later_function = @logic.Ty::app(
    function_symbol,
    [later_goal, later_goal],
    None,
  )
  let allocated = @logic.Ty::app(allocated_symbol, [later_goal], None)
  let ordered = order_upstream_kept_types_with_existing(
    [later_function, allocated],
    [allocated],
  )
  assert_true(
    ordered.length() == 2 &&
    ordered[0] == allocated &&
    ordered[1] == later_function,
  )
}

///|
test "an unrelated goal constant preserves the composite allocation boundary" {
  let context = @identity.CompilationContext::new()
  let origin = discrimination_test_origin(b"unrelated-goal-constant-order")
  let parameter = @logic.TyVarSymbol::new(context, b"p", origin)
  let goal = fn(name : BytesView) -> @logic.Ty raise @logic.TypeError {
    @logic.Ty::app(
      @logic.TypeSymbol::new_abstract(
        context,
        name,
        @identity.Origin::generated(
          @identity.DiscriminateMonomorphiseGoal,
          name,
          None,
          [],
        ),
        [],
        None,
      ),
      [],
      None,
    )
  }
  let a = goal(b"a")
  let early_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"early",
    origin,
    [parameter],
    None,
  )
  let early_a = @logic.Ty::app(early_symbol, [a], None)
  let d = goal(b"d")
  let late_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"late",
    origin,
    [parameter],
    None,
  )
  let late_a = @logic.Ty::app(late_symbol, [a], None)
  let ordered = order_upstream_kept_types([late_a, d, early_a])
  assert_true(
    ordered.length() == 3 &&
    ordered[0] == early_a &&
    ordered[1] == d &&
    ordered[2] == late_a,
  )
}

///|
test "a new direct function binder precedes a peer body type" {
  let context = @identity.CompilationContext::new()
  let origin = discrimination_test_origin(b"direct-function-binder-order")
  let parameter = @logic.TyVarSymbol::new(context, b"p", origin)
  let result_parameter = @logic.TyVarSymbol::new(context, b"r", origin)
  let source = @logic.TyVarSymbol::new(context, b"a", origin)
  let (_, goal) = monomorphised_goal_type(context, source)
  let sequence_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"sequence",
    origin,
    [parameter],
    None,
  )
  let function_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"infix ->",
    @identity.Origin::user(
      b"infix ->",
      None,
      [b"why3:builtin:function-type"],
    ),
    [parameter, result_parameter],
    None,
  )
  // MoonBit has already retained the body type, while Why3 recreates both
  // weakly held types during goal substitution and visits the binder first.
  let sequence = @logic.Ty::app(sequence_symbol, [goal], None)
  let function = @logic.Ty::app(function_symbol, [goal, goal], None)
  assert_true(sequence.allocation_order() < function.allocation_order())
  assert_true(
    compare_upstream_kept_type_priority(
      function,
      sequence,
      [],
      [],
      [sequence_symbol, function_symbol],
      [sequence, function],
      0,
      [],
    ) <
    0,
  )
  let static_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"static",
    origin,
    [],
    None,
  )
  let static_type = @logic.Ty::app(static_symbol, [], None)
  let static_sequence = @logic.Ty::app(
    sequence_symbol,
    [static_type],
    None,
  )
  assert_true(
    compare_upstream_kept_type_priority(
      function,
      static_sequence,
      [function, sequence],
      [],
      [sequence_symbol, function_symbol],
      [sequence, function],
      0,
      [],
    ) <
    0,
  )
}

///|
test "a direct function follows prior static select-kept chronology" {
  let context = @identity.CompilationContext::new()
  let origin = discrimination_test_origin(b"mixed-direct-function-order")
  let parameter = @logic.TyVarSymbol::new(context, b"p", origin)
  let result_parameter = @logic.TyVarSymbol::new(context, b"r", origin)
  let function_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"infix ->",
    @identity.Origin::user(
      b"infix ->",
      None,
      [b"why3:builtin:function-type"],
    ),
    [parameter, result_parameter],
    None,
  )
  let option_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"option",
    origin,
    [parameter],
    None,
  )
  let previous_option_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"option",
    origin,
    [parameter],
    None,
  )
  let sequence_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"sequence",
    origin,
    [parameter],
    None,
  )
  let source_a = @logic.TyVarSymbol::new(context, b"a", origin)
  let (_, a) = monomorphised_goal_type(context, source_a)
  let t_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"t",
    origin,
    [],
    None,
  )
  let t = @logic.Ty::app(t_symbol, [], None)
  // Deliberately allocate the new direct goal before the older composite:
  // the observed Why3 discovery frontier, not MoonBit allocation, decides
  // their order at the next goal.
  let previous_option_t = @logic.Ty::app(previous_option_symbol, [t], None)
  let option_t = @logic.Ty::app(option_symbol, [t], None)
  let previous_select = upstream_previous_select_kept_types.val
  upstream_previous_select_kept_types.val = [previous_option_t]
  assert_true(
    compare_upstream_kept_type_priority(
      option_t,
      a,
      [a],
      [],
      [option_symbol],
      [a],
      0,
      [],
    ) <
    0,
  )
  let sequence_a = @logic.Ty::app(sequence_symbol, [a], None)
  let previous_algebraic = upstream_current_algebraic_kept_types.val
  upstream_current_algebraic_kept_types.val = [sequence_a]
  assert_true(
    compare_upstream_kept_type_priority(
      option_t,
      sequence_a,
      [sequence_a],
      [],
      [],
      [sequence_a],
      1,
      [],
    ) <
    0,
  )
  upstream_current_algebraic_kept_types.val = previous_algebraic
  let option_a = @logic.Ty::app(option_symbol, [a], None)
  let mixed_function = @logic.Ty::app(
    function_symbol,
    [a, option_t],
    None,
  )
  let previous_current_select = upstream_current_select_kept_types.val
  upstream_current_select_kept_types.val = [mixed_function, option_t, option_a]
  assert_true(
    compare_upstream_kept_type_priority(
      option_t,
      option_a,
      [option_a],
      [],
      [],
      [option_a],
      0,
      [],
    ) >
    0,
  )
  upstream_previous_select_kept_types.val = [option_t]
  assert_true(
    compare_upstream_kept_type_priority(
      option_t,
      option_a,
      [option_a],
      [],
      [],
      [option_a],
      1,
      [],
    ) <
    0,
  )
  upstream_previous_select_kept_types.val = [previous_option_t]
  assert_true(
    compare_upstream_kept_type_priority(
      mixed_function,
      sequence_a,
      [sequence_a],
      [],
      [option_symbol, sequence_symbol, function_symbol],
      [a, sequence_a, mixed_function],
      0,
      [],
    ) <
    0,
  )
  upstream_previous_select_kept_types.val = [option_t]
  let previous_nested_algebraic = upstream_current_algebraic_kept_types.val
  upstream_current_algebraic_kept_types.val = [option_a]
  let nested_mixed_function = @logic.Ty::app(
    function_symbol,
    [sequence_a, option_t],
    None,
  )
  let tree_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"tree",
    origin,
    [parameter],
    None,
  )
  let tree_a = @logic.Ty::app(tree_symbol, [a], None)
  assert_true(
    compare_upstream_kept_type_priority(
      nested_mixed_function,
      option_a,
      [],
      [],
      [],
      [],
      0,
      [],
    ) <
    0,
  )
  upstream_current_algebraic_kept_types.val = []
  assert_true(
    compare_upstream_kept_type_priority(
      nested_mixed_function,
      tree_a,
      [],
      [],
      [],
      [],
      0,
      [],
    ) <
    0,
  )
  upstream_current_algebraic_kept_types.val = previous_nested_algebraic
  upstream_previous_select_kept_types.val = [previous_option_t]
  let static_result_function = @logic.Ty::app(
    function_symbol,
    [a, t],
    None,
  )
  assert_true(
    compare_upstream_kept_type_priority(
      sequence_a,
      static_result_function,
      [sequence_a],
      [],
      [],
      [],
      0,
      [],
    ) <
    0,
  )
  upstream_current_select_kept_types.val = previous_current_select
  upstream_previous_select_kept_types.val = previous_select
}

///|
test "a weak direct type is recreated after new peers" {
  let context = @identity.CompilationContext::new()
  let origin = discrimination_test_origin(b"weak-direct-type-order")
  let parameter = @logic.TyVarSymbol::new(context, b"p", origin)
  let source = @logic.TyVarSymbol::new(context, b"a", origin)
  let (_, goal) = monomorphised_goal_type(context, source)
  let weak_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"weak",
    origin,
    [parameter],
    None,
  )
  let fresh_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"fresh",
    origin,
    [parameter],
    None,
  )
  let weak = @logic.Ty::app(weak_symbol, [goal], None)
  let fresh = @logic.Ty::app(fresh_symbol, [goal], None)
  assert_true(
    compare_upstream_kept_type_priority(
      fresh,
      weak,
      [goal],
      [],
      [weak_symbol, fresh_symbol],
      [weak, fresh],
      1,
      [],
    ) <
    0,
  )
  let result_parameter = @logic.TyVarSymbol::new(context, b"r", origin)
  let function_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"infix ->",
    @identity.Origin::user(
      b"infix ->",
      None,
      [b"why3:builtin:function-type"],
    ),
    [parameter, result_parameter],
    None,
  )
  let weak_function = @logic.Ty::app(
    function_symbol,
    [goal, goal],
    None,
  )
  assert_true(
    compare_upstream_kept_type_priority(
      weak_function,
      fresh,
      [goal],
      [],
      [function_symbol, fresh_symbol],
      [weak_function, fresh],
      1,
      [],
    ) <
    0,
  )
}

///|
test "select-kept uses family order for nested function types" {
  let context = @identity.CompilationContext::new()
  let origin = discrimination_test_origin(b"nested-function-family-order")
  let parameter = @logic.TyVarSymbol::new(context, b"p", origin)
  let result_parameter = @logic.TyVarSymbol::new(context, b"r", origin)
  let source = @logic.TyVarSymbol::new(context, b"a", origin)
  let (_, goal) = monomorphised_goal_type(context, source)
  let unary = fn(name : BytesView) -> @logic.TypeSymbol raise @logic.TypeError {
    @logic.TypeSymbol::new_abstract(
      context,
      name,
      origin,
      [parameter],
      None,
    )
  }
  let element_symbol = unary(b"element")
  let sequence_symbol = unary(b"sequence")
  let split_symbol = unary(b"split")
  let function_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"infix ->",
    @identity.Origin::user(
      b"infix ->",
      None,
      [b"why3:builtin:function-type"],
    ),
    [parameter, result_parameter],
    None,
  )
  let element = @logic.Ty::app(element_symbol, [goal], None)
  let sequence = @logic.Ty::app(sequence_symbol, [element], None)
  let function = @logic.Ty::app(
    function_symbol,
    [element, element],
    None,
  )
  let split = @logic.Ty::app(split_symbol, [element], None)
  let families = [sequence_symbol, function_symbol, split_symbol]
  let prior_algebraic = upstream_current_algebraic_kept_types.val
  upstream_current_algebraic_kept_types.val = [split]
  assert_true(
    compare_upstream_kept_type_priority(
      sequence,
      function,
      [sequence, split],
      [],
      families,
      [sequence, function, split],
      0,
      [],
    ) <
    0,
  )
  assert_true(
    compare_upstream_kept_type_priority(
      function,
      split,
      [sequence, split],
      [],
      families,
      [sequence, function, split],
      0,
      [],
    ) <
    0,
  )
  upstream_current_algebraic_kept_types.val = prior_algebraic
}

///|
test "newly retained signatures override stale kept pair order" {
  let context = @identity.CompilationContext::new()
  let parameter = @logic.TyVarSymbol::new(
    context,
    b"p",
    discrimination_test_origin(b"p"),
  )
  let goal_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"a",
    @identity.Origin::generated(
      @identity.DiscriminateMonomorphiseGoal,
      b"a",
      None,
      [],
    ),
    [],
    None,
  )
  let goal = @logic.Ty::app(goal_symbol, [], None)
  let unary = fn(name : BytesView) -> @logic.Ty raise @logic.TypeError {
    @logic.Ty::app(
      @logic.TypeSymbol::new_abstract(
        context,
        name,
        discrimination_test_origin(name),
        [parameter],
        None,
      ),
      [goal],
      None,
    )
  }
  let view = unary(b"current-view")
  let split = unary(b"current-split")
  ignore(order_upstream_kept_types([view, split]))
  let first = order_upstream_algebraic_kept_types([view, split], [])
  assert_true(first.length() == 2 && first[0] == view && first[1] == split)
  retain_upstream_kept_types([split])
  let later = order_upstream_algebraic_kept_types(
    [view, split],
    upstream_newly_retained_kept_types.val,
  )
  assert_true(later.length() == 2 && later[0] == split && later[1] == view)
  let persisted = order_upstream_algebraic_kept_types([view, split], [])
  assert_true(
    persisted.length() == 2 && persisted[0] == split && persisted[1] == view,
  )
  upstream_prior_retained_kept_types.val = [split]
  let select_kept = order_upstream_kept_types_with_existing([view, split], [])
  assert_true(
    select_kept.length() == 2 &&
    select_kept[0] == split &&
    select_kept[1] == view,
  )
}

///|
test "discriminate metas preserve distinct Why3 algebraic fold orders" {
  let context = @identity.CompilationContext::new()
  let parameter = @logic.TyVarSymbol::new(
    context,
    b"p",
    discrimination_test_origin(b"p"),
  )
  let parameter_type = @logic.Ty::variable(parameter)
  let tree_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"tree",
    discrimination_test_origin(b"tree"),
    [parameter],
    None,
  )
  let tree_type = @logic.Ty::app(tree_symbol, [parameter_type], None)
  let empty = @logic.LSymbol::new_constructor(
    context,
    b"Empty",
    discrimination_test_origin(b"Empty"),
    [],
    tree_type,
    2,
    None,
  )
  let node = @logic.LSymbol::new_constructor(
    context,
    b"Node",
    discrimination_test_origin(b"Node"),
    [],
    tree_type,
    2,
    None,
  )
  let tree = @logic.DataDeclaration::new(
    tree_symbol,
    [
      @logic.DataConstructor::new(empty, [], None),
      @logic.DataConstructor::new(node, [], None),
    ],
    None,
  )
  let record_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"record",
    discrimination_test_origin(b"record"),
    [parameter],
    None,
  )
  let record_type = @logic.Ty::app(record_symbol, [parameter_type], None)
  let record_constructor = @logic.LSymbol::new_constructor(
    context,
    b"Record",
    discrimination_test_origin(b"Record"),
    [parameter_type, parameter_type],
    record_type,
    1,
    None,
  )
  let first = @logic.LSymbol::new_projection(
    context,
    b"first",
    discrimination_test_origin(b"first"),
    record_type,
    parameter_type,
    None,
  )
  let second = @logic.LSymbol::new_projection(
    context,
    b"second",
    discrimination_test_origin(b"second"),
    record_type,
    parameter_type,
    None,
  )
  let record = @logic.DataDeclaration::new(
    record_symbol,
    [
      @logic.DataConstructor::new(
        record_constructor,
        [Some(first), Some(second)],
        None,
      ),
    ],
    None,
  )
  let declaration = @logic.Decl::data(
    context,
    discrimination_test_origin(b"data"),
    [tree, record],
    None,
  )
  let argument_symbol = @logic.TypeSymbol::new_abstract(
    context,
    b"a",
    @identity.Origin::generated(
      @identity.DiscriminateMonomorphiseGoal,
      b"a",
      None,
      [],
    ),
    [],
    None,
  )
  let argument = @logic.Ty::app(argument_symbol, [], None)
  let actual_tree = @logic.Ty::app(tree_symbol, [argument], None)
  let actual_record = @logic.Ty::app(record_symbol, [argument], None)
  // Why3's `algebraic:kept` set is keyed by the full type hashcons tag, whose
  // cross-goal order can disagree with the type-symbol order used by
  // `encoding:alginst`.
  ignore(order_upstream_kept_types([actual_record, actual_tree]))
  let observed_pair_count = upstream_kept_type_pair_order.val.length()
  let items : Array[@theory.TheoryItem] = []
  append_discrimination_metas(
    items,
    [],
    [actual_tree, actual_record],
    [tree_symbol, record_symbol],
    [TheoryDecl(declaration)],
  )
  assert_eq(upstream_kept_type_pair_order.val.length(), observed_pair_count)
  let algebraic_kept : Array[Bytes] = []
  let labels : Array[(Bytes, Bytes)] = []
  for item in items.rev() {
    guard item is TheoryMeta(meta) else { continue }
    let view = meta.view()
    match (view.name, view.arguments) {
      (b"algebraic:kept", [MetaType(ty)]) =>
        if ty.view() is TyApp(symbol, _) {
          algebraic_kept.push(symbol.name().to_owned())
        }
      (b"encoding:alginst", [MetaType(ty)]) =>
        if ty.view() is TyApp(symbol, _) {
          labels.push((view.name, symbol.name().to_owned()))
        }
      (
        b"encoding:lsinst_contr"
        | b"encoding:lsinst_proj",
        [MetaLogicSymbol(symbol), MetaType(_)],
      ) => labels.push((view.name, symbol.view().name))
      _ => ()
    }
  }
  assert_eq(algebraic_kept, [b"record", b"tree"])
  assert_eq(labels, [
    (b"encoding:alginst", b"tree"),
    (b"encoding:lsinst_contr", b"Empty"),
    (b"encoding:lsinst_contr", b"Node"),
    (b"encoding:alginst", b"record"),
    (b"encoding:lsinst_contr", b"Record"),
    (b"encoding:lsinst_proj", b"first"),
    (b"encoding:lsinst_proj", b"second"),
  ])
}
