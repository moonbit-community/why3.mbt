// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn mlw_test_origin(
  name : BytesView,
  _kind : @identity.SourceSymbolKind,
  _item : UInt,
) -> @identity.Origin {
  @identity.Origin::user(name, None, [])
}

///|
fn empty_program_flags() -> @mlw.ProgramTypeFlags {
  {
    nonfree: false,
    private_: false,
    mutable_: false,
    fragile: false,
    argument_flags: [],
    region_flags: [],
  }
}

///|
fn integer_program_type(
  context : @identity.CompilationContext,
) -> (@logic.TypeSymbol, @mlw.ProgramTypeSymbol, @mlw.Ity) raise {
  let logic_type = @logic.TypeSymbol::new_builtin(
    context,
    b"int",
    mlw_test_origin(b"int", Type, 0U),
    BuiltinInteger,
  )
  let program_type = @mlw.ProgramTypeSymbol::new(
    context,
    logic_type,
    mlw_test_origin(b"int", Program, 1U),
    empty_program_flags(),
    ProgramNoDef,
    [],
    [],
    None,
  )
  (logic_type, program_type, @mlw.Ity::app(program_type, [], None))
}

///|
fn boolean_program_type(
  context : @identity.CompilationContext,
) -> (@logic.TypeSymbol, @mlw.ProgramTypeSymbol, @mlw.Ity) raise {
  let logic_type = @logic.TypeSymbol::new_builtin(
    context,
    b"bool",
    mlw_test_origin(b"bool", Type, 60U),
    BuiltinBoolean,
  )
  let program_type = @mlw.ProgramTypeSymbol::new(
    context,
    logic_type,
    mlw_test_origin(b"bool", Program, 61U),
    empty_program_flags(),
    ProgramNoDef,
    [],
    [],
    None,
  )
  (logic_type, program_type, @mlw.Ity::app(program_type, [], None))
}

///|
fn unit_program_type(
  context : @identity.CompilationContext,
) -> (@logic.TypeSymbol, @mlw.ProgramTypeSymbol, @mlw.Ity) raise {
  let logic_type = @logic.TypeSymbol::new_abstract(
    context,
    b"unit",
    @identity.Origin::user(b"unit", None, []),
    [],
    None,
  )
  let program_type = @mlw.ProgramTypeSymbol::new(
    context,
    logic_type,
    mlw_test_origin(b"unit", Program, 62U),
    empty_program_flags(),
    ProgramNoDef,
    [],
    [],
    None,
  )
  (logic_type, program_type, @mlw.Ity::app(program_type, [], None))
}

///|
fn formula_reading_program_variable(
  context : @identity.CompilationContext,
  name : BytesView,
  variable : @mlw.PVariable,
) -> @logic.Term raise {
  let symbol = variable.view().pure_symbol
  let predicate = @logic.LSymbol::new_predicate(
    context,
    name,
    @identity.Origin::user(name, None, []),
    [symbol.ty()],
    None,
  )
  @logic.Term::apply_predicate(predicate, [@logic.Term::variable(symbol)], None)
}

///|
test "routine preserves Cty and RLls identity" {
  let context = @identity.CompilationContext::new()
  let (logic_type, program_type, integer) = integer_program_type(context)
  let x = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"x", [], None),
    integer,
    false,
    None,
  )
  let pure_integer = @logic.Ty::app(logic_type, [], None)
  let logic_add = @logic.LSymbol::new_function(
    context,
    b"infix +",
    mlw_test_origin(b"infix +", Logic, 2U),
    [pure_integer, pure_integer],
    pure_integer,
    None,
  )
  let result = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", None, []),
    pure_integer,
    None,
  )
  let cty = @mlw.Cty::trusted_new(
    program_type.semantic_id(),
    [x],
    [x],
    [@logic.Term::true_formula()],
    [@mlw.Postcondition::trusted_new(result, @logic.Term::true_formula(), None)],
    @mlw.Effect::pure(false),
    integer,
    Visible,
    None,
  )
  let routine = @mlw.RoutineSymbol::new(
    context,
    b"infix +",
    mlw_test_origin(b"infix +", Program, 3U),
    cty,
    RLls(logic_add),
    None,
    None,
  )
  let program_space = @mlw.ProgramNamespace::empty()
    .add_type(b"int", program_type, None)
    .add_routine(b"infix +", routine, None)
  assert_true(program_space.find_type([b"int"], None) == program_type)
  assert_true(program_space.find_routine([b"infix +"], None) == routine)
  let view = routine.view()
  assert_true(view.logic is RLls(symbol) && symbol == logic_add)
  assert_eq(view.cty.view().arguments.length(), 1)
  assert_eq(view.cty.view().postconditions.length(), 1)
}

///|
test "program symbol construction accepts source origin" {
  let context = @identity.CompilationContext::new()
  let (logic_type, _, _) = integer_program_type(context)
  let symbol = @mlw.ProgramTypeSymbol::new(
    context,
    logic_type,
    @identity.Origin::user(b"source", None, []),
    empty_program_flags(),
    ProgramNoDef,
    [],
    [],
    None,
  )
  assert_true(symbol.view().origin.kind().view() is UserKind)
}

///|
fn mutable_cell_type(
  context : @identity.CompilationContext,
) -> (@mlw.PVariable, @mlw.ProgramTypeSymbol, @mlw.Ity) raise {
  let (_, _, integer) = integer_program_type(context)
  let field = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"contents", [], None),
    integer,
    false,
    None,
  )
  let logic_type = @logic.TypeSymbol::new_abstract(
    context,
    b"cell",
    @identity.Origin::user(b"cell", None, []),
    [],
    None,
  )
  let symbol = @mlw.ProgramTypeSymbol::new(
    context,
    logic_type,
    mlw_test_origin(b"cell", Program, 20U),
    {
      nonfree: false,
      private_: false,
      mutable_: true,
      fragile: false,
      argument_flags: [],
      region_flags: [],
    },
    ProgramNoDef,
    [field],
    [],
    None,
  )
  (field, symbol, @mlw.Ity::instantiate(symbol, [], [], None))
}

///|
test "mutable Ity allocates a region and purifies to an application" {
  let context = @identity.CompilationContext::new()
  let (_, symbol, cell) = mutable_cell_type(context)
  guard cell.view() is ItyReg(region) else {
    fail("mutable application did not allocate a region")
  }
  assert_true(region.view().symbol == symbol)
  assert_false(cell.is_pure())
  assert_true(cell.purify().is_pure())
  let reachable = cell.reachable_regions()
  assert_true(reachable.length() == 1 && reachable[0] == region)
}

///|
test "record flags follow exposed frozen fixed and visible traversals" {
  let context = @identity.CompilationContext::new()
  let parameter = @logic.TyVarSymbol::new(
    context,
    b"a",
    @identity.Origin::user(b"a", None, []),
  )
  let logic_type = @logic.TypeSymbol::new_abstract(
    context,
    b"box",
    @identity.Origin::user(b"box", None, []),
    [parameter],
    None,
  )
  let payload = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"payload", [], None),
    @mlw.Ity::variable(parameter),
    false,
    None,
  )
  let symbol = @mlw.ProgramTypeSymbol::new_record(
    context,
    logic_type,
    @identity.Origin::user(b"box", None, []),
    false,
    false,
    [],
    [payload],
    [],
    None,
  )
  let flags = symbol.view().flags
  assert_eq(flags.argument_flags, [
    { frozen: false, exposed: true, liable: false, fixed: true, visible: true },
  ])
  assert_false(flags.nonfree)
  assert_false(flags.mutable_)
  assert_false(flags.fragile)
}

///|
test "program aliases retain nested shareable regions" {
  let context = @identity.CompilationContext::new()
  let (_, _, inner) = mutable_cell_type(context)
  guard inner.view() is ItyReg(inner_region) else {
    fail("expected inner region")
  }
  let slot = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"slot", [], None),
    inner,
    false,
    None,
  )
  let wrapper_logic = @logic.TypeSymbol::new_abstract(
    context,
    b"wrapper",
    @identity.Origin::user(b"wrapper", None, []),
    [],
    None,
  )
  let wrapper = @mlw.ProgramTypeSymbol::new_record(
    context,
    wrapper_logic,
    @identity.Origin::user(b"wrapper", None, []),
    false,
    false,
    [],
    [slot],
    [],
    None,
  )
  let wrapped = @mlw.Ity::app_with_regions(wrapper, [], [inner], None)
  let alias_logic = @logic.TypeSymbol::new_alias(
    context,
    b"alias",
    @identity.Origin::user(b"alias", None, []),
    [],
    wrapped.to_ty(None),
    None,
  )
  let alias_symbol = @mlw.ProgramTypeSymbol::new_alias(
    context,
    alias_logic,
    @identity.Origin::user(b"alias", None, []),
    wrapped,
    None,
  )
  let regions = alias_symbol.view().regions
  assert_true(regions.length() == 1 && regions[0] == inner_region)
}

///|
test "range float and variant program-type constructors mirror core types" {
  let context = @identity.CompilationContext::new()
  let lower = BigInt::from_int(-8)
  let upper = BigInt::from_int(7)
  let range_logic = @logic.TypeSymbol::new_range(
    context,
    b"small",
    @identity.Origin::user(b"small", None, []),
    lower,
    upper,
    None,
  )
  let range = @mlw.ProgramTypeSymbol::new_range(
    context,
    range_logic,
    @identity.Origin::user(b"small", None, []),
    lower,
    upper,
    None,
  )
  assert_true(
    range.view().definition is ProgramRange(low, high) &&
    low == lower &&
    high == upper,
  )

  let float_logic = @logic.TypeSymbol::new_float(
    context,
    b"binary32",
    @identity.Origin::user(b"binary32", None, []),
    8,
    24,
    None,
  )
  let float = @mlw.ProgramTypeSymbol::new_float(
    context,
    float_logic,
    @identity.Origin::user(b"binary32", None, []),
    8,
    24,
    None,
  )
  assert_true(float.view().definition is ProgramFloat(8, 24))

  let (_, _, integer) = integer_program_type(context)
  let field = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"payload", [], None),
    integer,
    false,
    None,
  )
  let variant_logic = @logic.TypeSymbol::new_abstract(
    context,
    b"option",
    @identity.Origin::user(b"option", None, []),
    [],
    None,
  )
  let variant = @mlw.ProgramTypeSymbol::new_variant(
    context,
    variant_logic,
    @identity.Origin::user(b"option", None, []),
    [[], [field]],
    None,
  )
  assert_true(
    variant.view().immutable_fields.length() == 1 &&
    variant.view().immutable_fields[0] == field,
  )
}

///|
test "effect assignment records writes and rejects duplicate fields" {
  let context = @identity.CompilationContext::new()
  let (field, _, cell) = mutable_cell_type(context)
  let integer = field.view().ity
  let target = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"target", [], None),
    cell,
    false,
    None,
  )
  let value = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"value", [], None),
    integer,
    false,
    None,
  )
  let effect = @mlw.Effect::assign([(target, field, value)], None)
  assert_eq(effect.view().writes.length(), 1)
  assert_eq(effect.view().covers.length(), 1)
  assert_true(effect.view().termination is Total)
  try
    @mlw.Effect::assign([(target, field, value), (target, field, value)], None)
  catch {
    MlwError(diagnostic) => assert_eq(diagnostic.kind, DuplicateEffectField)
  } noraise {
    _ => fail("expected duplicate assignment rejection")
  }
}

///|
test "assignment stitches replaced nested region identities" {
  let context = @identity.CompilationContext::new()
  let (_, inner_symbol, inner_template) = mutable_cell_type(context)
  let slot = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"slot", [], None),
    inner_template,
    false,
    None,
  )
  let outer_logic = @logic.TypeSymbol::new_abstract(
    context,
    b"outer",
    @identity.Origin::user(b"outer", None, []),
    [],
    None,
  )
  let outer_symbol = @mlw.ProgramTypeSymbol::new_record(
    context,
    outer_logic,
    @identity.Origin::user(b"outer", None, []),
    false,
    false,
    [slot],
    [],
    [],
    None,
  )
  let outer = @mlw.Ity::instantiate(outer_symbol, [], [], None)
  guard outer.view() is ItyReg(outer_region) &&
    outer_region.view().regions.length() == 1 &&
    outer_region.view().regions[0].view() is ItyReg(old_nested) else {
    fail("expected outer and nested regions")
  }
  let replacement = @mlw.Ity::instantiate(inner_symbol, [], [], None)
  guard replacement.view() is ItyReg(new_nested) else {
    fail("expected replacement region")
  }
  let target = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"target", [], None),
    outer,
    false,
    None,
  )
  let value = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"value", [], None),
    replacement,
    false,
    None,
  )
  let resets = @mlw.Effect::assign([(target, slot, value)], None).view().resets
  assert_eq(resets.length(), 2)
  assert_true(resets.any(region => region == old_nested))
  assert_true(resets.any(region => region == new_nested))
}

///|
test "overwriting a region field resets the displaced nested region" {
  let context = @identity.CompilationContext::new()
  let (_, _, inner) = mutable_cell_type(context)
  guard inner.view() is ItyReg(inner_region) else {
    fail("expected inner region")
  }
  let slot = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"slot", [], None),
    inner,
    false,
    None,
  )
  let logic_type = @logic.TypeSymbol::new_abstract(
    context,
    b"outer",
    @identity.Origin::user(b"outer", None, []),
    [],
    None,
  )
  let outer_symbol = @mlw.ProgramTypeSymbol::new_record(
    context,
    logic_type,
    @identity.Origin::user(b"outer", None, []),
    false,
    false,
    [slot],
    [],
    [],
    None,
  )
  let outer = @mlw.Ity::instantiate(outer_symbol, [], [], None)
  guard outer.view() is ItyReg(outer_region) else {
    fail("expected outer region")
  }
  let nested = outer_region.view().regions
  guard nested.length() == 1 && nested[0].view() is ItyReg(nested_region) else {
    fail("expected instantiated nested region")
  }
  assert_false(nested_region == inner_region)
  let write = @mlw.EffectWrite::new(outer_region, [slot], None)
  let effect = @mlw.Effect::trusted_new(
    outer_region.semantic_id(),
    [],
    [write],
    [],
    [outer_region],
    [],
    [],
    [],
    Total,
    false,
    None,
  ).reset_overwritten(None)
  let resets = effect.view().resets
  assert_eq(resets.length(), 1)
  assert_true(resets[0] == nested_region)
}

///|
test "effect detects stale reads and ghost divergence" {
  let context = @identity.CompilationContext::new()
  let (_, _, cell) = mutable_cell_type(context)
  guard cell.view() is ItyReg(region) else { fail("expected cell region") }
  let target = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"target", [], None),
    cell,
    false,
    None,
  )
  let reset = @mlw.Effect::pure(false).reset([region], None)
  try reset.read_post([target], None) catch {
    MlwError(diagnostic) => assert_eq(diagnostic.kind, StaleVariable)
  } noraise {
    _ => fail("expected stale-variable rejection")
  }
  try @mlw.Effect::pure(true).diverge(None) catch {
    MlwError(diagnostic) => assert_eq(diagnostic.kind, GhostDivergence)
  } noraise {
    _ => fail("expected ghost divergence rejection")
  }
}

///|
test "effect rejects ghost writes visible through a regular alias" {
  let context = @identity.CompilationContext::new()
  let (field, _, cell) = mutable_cell_type(context)
  guard cell.view() is ItyReg(region) else { fail("expected cell region") }
  let regular_alias = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"alias", [], None),
    cell,
    false,
    None,
  )
  let write = @mlw.EffectWrite::new(region, [field], None)
  let effect = @mlw.Effect::write([regular_alias], [write], None)
  try effect.ghostify(true, None) catch {
    MlwError(diagnostic) => assert_eq(diagnostic.kind, BadGhostWrite)
  } noraise {
    _ => fail("expected visible ghost-write rejection")
  }
}

///|
test "effect rejects updates through frozen components" {
  let context = @identity.CompilationContext::new()
  let (field, _, cell) = mutable_cell_type(context)
  guard cell.view() is ItyReg(region) else { fail("expected cell region") }
  let logic_box = @logic.TypeSymbol::new_abstract(
    context,
    b"box",
    @identity.Origin::user(b"box", None, []),
    [],
    None,
  )
  let box_symbol = @mlw.ProgramTypeSymbol::new(
    context,
    logic_box,
    mlw_test_origin(b"box", Program, 24U),
    {
      nonfree: false,
      private_: false,
      mutable_: false,
      fragile: false,
      argument_flags: [],
      region_flags: [
        {
          frozen: true,
          exposed: true,
          liable: false,
          fixed: true,
          visible: true,
        },
      ],
    },
    ProgramNoDef,
    [],
    [],
    None,
  )
  let boxed = @mlw.Ity::app_with_regions(box_symbol, [], [cell], None)
  let live = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"boxed", [], None),
    boxed,
    false,
    None,
  )
  let write = @mlw.EffectWrite::new(region, [field], None)
  let effect = @mlw.Effect::write([live], [write], None)
  try effect.read_post([live], None) catch {
    MlwError(diagnostic) => assert_eq(diagnostic.kind, IllegalUpdate)
  } noraise {
    _ => fail("expected frozen-region update rejection")
  }
}

///|
test "effect instantiation rejects aliases between affected regions" {
  let context = @identity.CompilationContext::new()
  let (_, symbol, first) = mutable_cell_type(context)
  let second = @mlw.Ity::instantiate(symbol, [], [], None)
  let target = @mlw.Ity::instantiate(symbol, [], [], None)
  guard first.view() is ItyReg(first_region) &&
    second.view() is ItyReg(second_region) else {
    fail("expected source regions")
  }
  let effect = @mlw.Effect::pure(false).reset(
    [first_region, second_region],
    None,
  )
  let substitution = @mlw.ItySubstitution::empty()
    .match_region(first_region, target, None)
    .match_region(second_region, target, None)
  try effect.instantiate(substitution, None) catch {
    MlwError(diagnostic) => assert_eq(diagnostic.kind, IllegalAlias)
  } noraise {
    _ => fail("expected affected-region alias rejection")
  }
}

///|
test "program type matching resolves only explicit inference aliases transitively" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let first = @logic.TyVarSymbol::new(
    context,
    b"first",
    @identity.Origin::user(b"first", None, []),
  )
  let second = @logic.TyVarSymbol::new(
    context,
    b"second",
    @identity.Origin::user(b"second", None, [b"mlw:inference_type_variable"]),
  )
  let third = @logic.TyVarSymbol::new(
    context,
    b"third",
    @identity.Origin::user(b"third", None, [b"mlw:inference_type_variable"]),
  )
  let first_ity = @mlw.Ity::variable(first)
  let second_ity = @mlw.Ity::variable(second)
  let third_ity = @mlw.Ity::variable(third)
  let substitution = @mlw.ItySubstitution::empty()
    .match_ity(first_ity, second_ity, None)
    .match_ity(first_ity, third_ity, None)
    .match_ity(first_ity, integer, None)
  let resolved = substitution.instantiate_partial(
    [first_ity, second_ity, third_ity],
    None,
  )
  assert_true(resolved.length() == 3 && resolved.all(item => item == integer))
  let self_alias = @mlw.ItySubstitution::empty()
    .match_ity(first_ity, first_ity, None)
    .match_ity(first_ity, second_ity, None)
    .instantiate_partial([first_ity, second_ity], None)
  assert_true(self_alias.length() == 2 && self_alias[0] == self_alias[1])
  let rigid = @logic.TyVarSymbol::new(
    context,
    b"rigid",
    @identity.Origin::user(b"rigid", None, []),
  )
  try
    @mlw.ItySubstitution::empty()
    .match_ity(first_ity, @mlw.Ity::variable(rigid), None)
    .match_ity(first_ity, integer, None)
  catch {
    @mlw.MlwError(diagnostic) =>
      assert_eq(diagnostic.kind, @mlw.ProgramTypeMismatch)
  } noraise {
    _ => fail("captured actual type variable was not kept rigid")
  }
  let layered = @mlw.ItySubstitution::empty()
    .match_ity(first_ity, @mlw.Ity::variable(rigid), None)
    .match_ity(@mlw.Ity::variable(rigid), integer, None)
    .instantiate_partial([first_ity, @mlw.Ity::variable(rigid)], None)
  assert_true(layered[0] == @mlw.Ity::variable(rigid))
  assert_true(layered[1] == integer)
  try
    @mlw.ItySubstitution::empty()
    .freeze(first_ity, None)
    .match_ity(first_ity, integer, None)
  catch {
    @mlw.MlwError(diagnostic) =>
      assert_eq(diagnostic.kind, @mlw.ProgramTypeMismatch)
  } noraise {
    _ => fail("frozen type variable unexpectedly accepted an instantiation")
  }
}

///|
test "inferred program regions specialize to an actual argument region" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let parameter = @logic.TyVarSymbol::new(
    context,
    b"a",
    @identity.Origin::user(b"a", None, []),
  )
  let logic_type = @logic.TypeSymbol::new_abstract(
    context,
    b"container",
    @identity.Origin::user(b"container", None, []),
    [parameter],
    None,
  )
  let symbol = @mlw.ProgramTypeSymbol::new(
    context,
    logic_type,
    @identity.Origin::user(b"container", None, []),
    {
      nonfree: false,
      private_: false,
      mutable_: true,
      fragile: false,
      argument_flags: [
        {
          frozen: false,
          exposed: true,
          liable: true,
          fixed: false,
          visible: true,
        },
      ],
      region_flags: [],
    },
    ProgramNoDef,
    [],
    [],
    None,
  )
  let template = @mlw.Ity::instantiate(
    symbol,
    [@mlw.Ity::variable(parameter)],
    [],
    None,
  )
  let (inferred, inferred_expected) = @mlw.ItySubstitution::empty().instantiate_inference_expected(
    context,
    template,
    None,
  )
  let actual = @mlw.Ity::instantiate(symbol, [integer], [], None)
  let specialized = inferred
    .match_ity(template, actual, None)
    .instantiate(template, None)
  assert_true(specialized == actual)
  let captured = @logic.TyVarSymbol::new(
    context,
    b"captured",
    @identity.Origin::user(b"captured", None, []),
  )
  let captured_ity = @mlw.Ity::variable(captured)
  let resolved = inferred
    .match_ity(captured_ity, inferred_expected, None)
    .match_ity(captured_ity, actual, None)
    .instantiate_partial([captured_ity], None)
  assert_true(resolved is [resolved_ity] && resolved_ity == actual)
  guard inferred_expected.view() is ItyReg(inferred_region) &&
    inferred_region.view().arguments is [inferred_argument] else {
    fail("inference expected type lost its generated region and argument")
  }
  let region_only_inference = inferred.match_ity(
    inferred_argument,
    integer,
    None,
  )
  let concrete_inference = region_only_inference.instantiate_partial(
      [inferred_expected],
      None,
    )[0]
  assert_true(concrete_inference.free_type_variables().is_empty())
  let region_resolved = region_only_inference
    .match_ity(captured_ity, concrete_inference, None)
    .match_ity(captured_ity, actual, None)
    .instantiate_partial([captured_ity], None)
  assert_true(region_resolved is [resolved_ity] && resolved_ity == actual)
}

///|
test "effect instantiation rejects a snapshot around an affected region" {
  let context = @identity.CompilationContext::new()
  let (_, _, inner_template) = mutable_cell_type(context)
  let slot = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"slot", [], None),
    inner_template,
    false,
    None,
  )
  let outer_logic = @logic.TypeSymbol::new_abstract(
    context,
    b"outer",
    @identity.Origin::user(b"outer", None, []),
    [],
    None,
  )
  let outer_symbol = @mlw.ProgramTypeSymbol::new_record(
    context,
    outer_logic,
    @identity.Origin::user(b"outer", None, []),
    false,
    false,
    [slot],
    [],
    [],
    None,
  )
  let outer = @mlw.Ity::instantiate(outer_symbol, [], [], None)
  guard outer.view() is ItyReg(outer_region) &&
    outer_region.view().regions.length() == 1 &&
    outer_region.view().regions[0].view() is ItyReg(nested_region) else {
    fail("expected outer and nested regions")
  }
  let effect = @mlw.Effect::pure(false).reset([nested_region], None)
  let substitution = @mlw.ItySubstitution::empty().match_region(
    outer_region,
    outer.purify(),
    None,
  )
  try effect.instantiate(substitution, None) catch {
    MlwError(diagnostic) => assert_eq(diagnostic.kind, IllegalSnapshot)
  } noraise {
    _ => fail("expected enclosing snapshot rejection")
  }
}

///|
test "tuple masks reduce and validate component arity" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let a = @logic.TyVarSymbol::new(
    context,
    b"a",
    @identity.Origin::user(b"a", None, []),
  )
  let b = @logic.TyVarSymbol::new(
    context,
    b"b",
    @identity.Origin::user(b"b", None, []),
  )
  let logic_tuple = @logic.TypeSymbol::new_abstract(
    context,
    b"tuple2",
    @identity.Origin::user(b"tuple2", None, []),
    [a, b],
    None,
  )
  let tuple = @mlw.ProgramTypeSymbol::new(
    context,
    logic_tuple,
    mlw_test_origin(b"tuple2", Program, 30U),
    {
      nonfree: false,
      private_: false,
      mutable_: false,
      fragile: false,
      argument_flags: [
        {
          frozen: true,
          exposed: true,
          liable: false,
          fixed: true,
          visible: true,
        },
        {
          frozen: true,
          exposed: true,
          liable: false,
          fixed: true,
          visible: true,
        },
      ],
      region_flags: [],
    },
    ProgramNoDef,
    [],
    [],
    None,
  )
  let tuple_ity = @mlw.Ity::app(tuple, [integer, integer], None)
  assert_true(
    @mlw.Tuple([Visible, Visible]).validate_for_ity(tuple_ity, None) is Visible,
  )
  try @mlw.Tuple([Visible]).validate_for_ity(tuple_ity, None) catch {
    MlwError(diagnostic) => assert_eq(diagnostic.kind, InvalidProgramMask)
  } noraise {
    _ => fail("expected tuple-mask arity rejection")
  }
}

///|
test "full Cty retains exceptional posts oldies and freeze" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let argument = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"x", [], None),
    integer,
    false,
    None,
  )
  let snapshot = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"old_x", [], None),
    integer,
    true,
    None,
  )
  let oldie = @mlw.OldSnapshot::new(snapshot, argument, None)
  let exception = @mlw.XSymbol::new(
    context,
    @theory.SemanticName::new(b"E", [], None),
    integer,
    None,
  )
  let result = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", None, []),
    integer.to_ty(None),
    None,
  )
  let post = @mlw.Postcondition::trusted_new(
    result,
    formula_reading_program_variable(context, b"uses_old_x", snapshot),
    None,
  )
  let exceptional = @mlw.ExceptionalPostconditions::new(exception, [post], None)
  let cty = @mlw.Cty::new(
    [argument],
    [],
    [post],
    [exceptional],
    [oldie],
    @mlw.Effect::pure(false).raise_exception(exception),
    integer,
    None,
  )
  assert_eq(cty.view().exceptional_postconditions.length(), 1)
  assert_eq(cty.view().oldies.length(), 1)
  assert_eq(cty.view().effect.view().raises.length(), 1)
}

///|
test "Cty completes reads from postconditions" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let external = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"external", [], None),
    integer,
    false,
    None,
  )
  let result = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", None, []),
    integer.to_ty(None),
    None,
  )
  let post = @mlw.Postcondition::trusted_new(
    result,
    formula_reading_program_variable(context, b"uses_external", external),
    None,
  )
  let cty = @mlw.Cty::new_with_variables(
    [external],
    [],
    [],
    [post],
    [],
    [],
    @mlw.Effect::pure(false),
    integer,
    None,
  )
  let reads = cty.view().effect.view().reads
  assert_true(reads.length() == 1 && reads[0] == external)
}

///|
test "Cty incrementally captures specification dependencies" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let type_variable = @logic.TyVarSymbol::new(
    context,
    b"a",
    @identity.Origin::user(b"a", None, []),
  )
  let external = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"external", [], None),
    @mlw.Ity::variable(type_variable),
    false,
    None,
  )
  let precondition = formula_reading_program_variable(
    context, b"uses_generic_external", external,
  )
  let cty = @mlw.Cty::new(
    [],
    [],
    [],
    [],
    [],
    @mlw.Effect::pure(false),
    integer,
    None,
  ).add_preconditions_with_variables([external], [precondition], None)
  let view = cty.view()
  let reads = view.effect.view().reads
  assert_true(reads.length() == 1 && reads[0] == external)
  assert_eq(view.preconditions.length(), 1)
  assert_eq(view.freeze.view().type_variables.length(), 1)
}

///|
test "Cty replaces retained old-snapshot reads with originals" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let original = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"x", [], None),
    integer,
    false,
    None,
  )
  let snapshot = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"old_x", [], None),
    integer,
    true,
    None,
  )
  let oldie = @mlw.OldSnapshot::new(snapshot, original, None)
  let result = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", None, []),
    integer.to_ty(None),
    None,
  )
  let post = @mlw.Postcondition::trusted_new(
    result,
    formula_reading_program_variable(context, b"uses_snapshot", snapshot),
    None,
  )
  let cty = @mlw.Cty::new_with_variables(
    [snapshot, original],
    [],
    [],
    [post],
    [],
    [oldie],
    @mlw.Effect::pure(false),
    integer,
    None,
  )
  let view = cty.view()
  let reads = view.effect.view().reads
  assert_true(reads.length() == 1 && reads[0] == original)
  assert_eq(view.oldies.length(), 1)
}

///|
test "Cty removes exceptions with a singleton false postcondition" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let exception = @mlw.XSymbol::new(
    context,
    @theory.SemanticName::new(b"Impossible", [], None),
    integer,
    None,
  )
  let result = @logic.VSymbol::new(
    context,
    b"exception_result",
    @identity.Origin::user(b"exception_result", None, []),
    integer.to_ty(None),
    None,
  )
  let impossible = @mlw.Postcondition::trusted_new(
    result,
    @logic.Term::false_formula(),
    None,
  )
  let exceptional = @mlw.ExceptionalPostconditions::new(
    exception,
    [impossible],
    None,
  )
  let cty = @mlw.Cty::new(
    [],
    [],
    [],
    [exceptional],
    [],
    @mlw.Effect::pure(false).raise_exception(exception),
    integer,
    None,
  )
  assert_true(cty.view().effect.view().raises.is_empty())
}

///|
test "Cty drops writes to regions absent from its reads" {
  let context = @identity.CompilationContext::new()
  let (field, _, cell) = mutable_cell_type(context)
  guard cell.view() is ItyReg(region) else { fail("expected cell region") }
  let write = @mlw.EffectWrite::new(region, [field], None)
  let effect = @mlw.Effect::trusted_new(
    region.semantic_id(),
    [],
    [write],
    [],
    [region],
    [],
    [],
    [],
    Total,
    false,
    None,
  )
  let cty = @mlw.Cty::new([], [], [], [], [], effect, field.view().ity, None)
  assert_true(cty.view().effect.view().writes.is_empty())
  assert_true(cty.view().effect.view().covers.is_empty())
}

///|
test "defensive Cty resets fresh results and spoils escaping variables" {
  let context = @identity.CompilationContext::new()
  let (_, _, cell) = mutable_cell_type(context)
  let allocating = @mlw.Cty::new(
    [],
    [],
    [],
    [],
    [],
    @mlw.Effect::pure(false),
    cell,
    None,
    defensive=true,
  )
  assert_eq(allocating.view().effect.view().resets.length(), 1)

  let type_variable = @logic.TyVarSymbol::new(
    context,
    b"a",
    @identity.Origin::user(b"a", None, []),
  )
  let generic = @mlw.Cty::new(
    [],
    [],
    [],
    [],
    [],
    @mlw.Effect::pure(false),
    @mlw.Ity::variable(type_variable),
    None,
    defensive=true,
  )
  let spoils = generic.view().effect.view().spoils
  assert_true(spoils.length() == 1 && spoils[0] == type_variable)
}

///|
test "Cty application instantiates polymorphic specifications" {
  let context = @identity.CompilationContext::new()
  let type_variable = @logic.TyVarSymbol::new(
    context,
    b"a",
    @identity.Origin::user(b"a", None, []),
  )
  let generic_ity = @mlw.Ity::variable(type_variable)
  let formal = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"x", [], None),
    generic_ity,
    false,
    None,
  )
  let generic_type = @logic.Ty::variable(type_variable)
  let predicate = @logic.LSymbol::new_predicate(
    context,
    b"p",
    @identity.Origin::user(b"p", None, []),
    [generic_type],
    None,
  )
  let result = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", None, []),
    generic_type,
    None,
  )
  let post = @mlw.Postcondition::trusted_new(
    result,
    @logic.Term::apply_predicate(
      predicate,
      [@logic.Term::variable(result)],
      None,
    ),
    None,
  )
  let cty = @mlw.Cty::trusted_new(
    type_variable.semantic_id(),
    [formal],
    [formal],
    [],
    [post],
    @mlw.Effect::pure(false),
    generic_ity,
    Visible,
    None,
  )
  let (_, _, integer) = integer_program_type(context)
  let actual = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"actual", [], None),
    integer,
    false,
    None,
  )
  let applied = cty.apply(context, [actual], [], integer, None)
  assert_true(applied.view().result == integer)
  assert_true(applied.view().arguments.is_empty())
  assert_eq(applied.view().effect.view().reads.length(), 1)
  let applied_post = applied.view().postconditions[0].view()
  assert_true(applied_post.result.ty() == integer.to_ty(None))
  let free = applied_post.formula.free_variables()
  assert_true(free.length() == 1 && free[0] == applied_post.result)
}

///|
test "Cty application normalizes nested inference target substitutions" {
  let context = @identity.CompilationContext::new()
  let (_, _, state) = integer_program_type(context)
  let formal_type = @logic.TyVarSymbol::new(
    context,
    b"a",
    @identity.Origin::user(b"a", None, []),
  )
  let left_inference = @logic.TyVarSymbol::new(
    context,
    b"left",
    @identity.Origin::user(b"left", None, [b"mlw:inference_type_variable"]),
  )
  let right_inference = @logic.TyVarSymbol::new(
    context,
    b"right",
    @identity.Origin::user(b"right", None, [b"mlw:inference_type_variable"]),
  )
  let pair_left = @logic.TyVarSymbol::new(
    context,
    b"left",
    @identity.Origin::user(b"left", None, []),
  )
  let pair_right = @logic.TyVarSymbol::new(
    context,
    b"right",
    @identity.Origin::user(b"right", None, []),
  )
  let pair_logic = @logic.TypeSymbol::new_abstract(
    context,
    b"pair",
    @identity.Origin::user(b"pair", None, []),
    [pair_left, pair_right],
    None,
  )
  let pair = @mlw.ProgramTypeSymbol::new(
    context,
    pair_logic,
    @identity.Origin::user(b"pair", None, []),
    {
      ..empty_program_flags(),
      argument_flags: [
        {
          frozen: false,
          exposed: true,
          liable: false,
          fixed: false,
          visible: true,
        },
        {
          frozen: false,
          exposed: true,
          liable: false,
          fixed: false,
          visible: true,
        },
      ],
    },
    ProgramNoDef,
    [],
    [],
    None,
  )
  let wrapper_parameter = @logic.TyVarSymbol::new(
    context,
    b"value",
    @identity.Origin::user(b"value", None, []),
  )
  let wrapper_logic = @logic.TypeSymbol::new_abstract(
    context,
    b"wrapper",
    @identity.Origin::user(b"wrapper", None, []),
    [wrapper_parameter],
    None,
  )
  let wrapper = @mlw.ProgramTypeSymbol::new(
    context,
    wrapper_logic,
    @identity.Origin::user(b"wrapper", None, []),
    {
      ..empty_program_flags(),
      argument_flags: [
        {
          frozen: false,
          exposed: true,
          liable: false,
          fixed: false,
          visible: true,
        },
      ],
    },
    ProgramNoDef,
    [],
    [],
    None,
  )
  let wrap = fn(argument) raise { @mlw.Ity::app(wrapper, [argument], None) }
  let formal = @mlw.Ity::variable(formal_type)
  let formal_left = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"left", [], None),
    wrap(formal),
    false,
    None,
  )
  let formal_right = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"right", [], None),
    wrap(@mlw.Ity::app(pair, [formal, state], None)),
    false,
    None,
  )
  let computation = @mlw.Cty::trusted_new(
    formal_type.semantic_id(),
    [formal_left, formal_right],
    [formal_left, formal_right],
    [],
    [],
    @mlw.Effect::pure(false),
    wrap(formal),
    Visible,
    None,
  )
  let left = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"actual_left", [], None),
    wrap(@mlw.Ity::variable(left_inference)),
    false,
    None,
  )
  let right = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"actual_right", [], None),
    wrap(@mlw.Ity::variable(right_inference)),
    false,
    None,
  )
  let applied = computation.apply(
    context,
    [left, right],
    [],
    wrap(@mlw.Ity::variable(left_inference)),
    None,
  )
  assert_true(applied.view().arguments.is_empty())
}

///|
test "full expression call stores the instantiated computation type" {
  let context = @identity.CompilationContext::new()
  let (logic_integer, _, integer) = integer_program_type(context)
  let formal = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"formal", [], None),
    integer,
    false,
    None,
  )
  let result_symbol = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", None, []),
    @logic.Ty::app(logic_integer, [], None),
    None,
  )
  let post = @mlw.Postcondition::trusted_new(
    result_symbol,
    formula_reading_program_variable(context, b"uses_formal", formal),
    None,
  )
  let cty = @mlw.Cty::trusted_new(
    formal.semantic_id(),
    [formal],
    [formal],
    [],
    [post],
    @mlw.Effect::pure(false),
    integer,
    Visible,
    None,
  )
  let routine = @mlw.RoutineSymbol::new_user(
    context,
    b"call",
    @identity.Origin::user(b"call", None, []),
    cty,
    None,
  )
  let actual = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"actual", [], None),
    integer,
    false,
    None,
  )
  let expression = @mlw.Expr::routine_call(
    routine,
    [actual],
    integer,
    @identity.Origin::user(b"call actual", None, []),
    [],
    None,
  )
  guard expression.view() is Eexec(computation, attached) &&
    computation.view() is Capp(symbol, arguments) else {
    fail("routine call did not use the full Eexec/Capp representation")
  }
  assert_true(symbol == routine)
  assert_true(arguments.length() == 1 && arguments[0] == actual)
  assert_true(attached.view().arguments.is_empty())
  assert_true(
    attached.view().effect.view().reads.any(variable => variable == actual),
  )
  let declaration = @mlw.ProgramDeclaration::routine(
    routine.semantic_id(),
    routine,
    Cfun(cty, Some(expression)),
    [],
    [],
    None,
  )
  assert_true(
    declaration
    .introduced_symbols()
    .any(dependency => {
      dependency is RoutineDependency(stored) && stored == routine
    }),
  )
  assert_true(
    declaration
    .dependencies()
    .any(dependency => {
      dependency is ProgramVariableDependency(stored) && stored == actual
    }),
  )
}

///|
test "assignment expression records projection writes in its effect" {
  let context = @identity.CompilationContext::new()
  let (field, _, cell) = mutable_cell_type(context)
  let integer = field.view().ity
  let (_, _, unit) = unit_program_type(context)
  let target = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"target", [], None),
    cell,
    false,
    None,
  )
  let value = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"value", [], None),
    integer,
    false,
    None,
  )
  let projection_logic = @logic.LSymbol::new_projection(
    context,
    b"contents",
    @identity.Origin::user(b"contents", None, []),
    cell.to_ty(None),
    integer.to_ty(None),
    None,
  )
  let projection_cty = @mlw.Cty::trusted_new(
    target.semantic_id(),
    [target],
    [target],
    [],
    [],
    @mlw.Effect::from_reads([target], false),
    integer,
    Visible,
    None,
  )
  let projection = @mlw.RoutineSymbol::new(
    context,
    b"contents",
    mlw_test_origin(b"contents", Program, 63U),
    projection_cty,
    RLls(projection_logic),
    Some(field),
    None,
  )
  let assignment = @mlw.Assignment::new(target, projection, value, None)
  let expression = @mlw.Expr::assignment(
    [assignment],
    unit,
    @identity.Origin::user(b"target.contents <- value", None, []),
    [],
    None,
  )
  guard expression.view() is Eassign([stored]) else {
    fail("assignment expression lost its full assignment node")
  }
  assert_true(stored.view().field == projection)
  let writes = expression.effect().view().writes
  assert_true(
    writes.length() == 1 &&
    writes[0].view().fields.length() == 1 &&
    writes[0].view().fields[0] == field,
  )
}

///|
test "while expressions read specifications and enforce self sequencing" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let (_, _, boolean) = boolean_program_type(context)
  let (_, _, unit) = unit_program_type(context)
  let condition_variable = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"condition", [], None),
    boolean,
    false,
    None,
  )
  let body_variable = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"body", [], None),
    unit,
    false,
    None,
  )
  let measure = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"measure", [], None),
    integer,
    true,
    None,
  )
  let variant = @mlw.ProgramVariant::new(
    @logic.Term::variable(measure.view().pure_symbol),
    None,
    None,
  )
  let loop_ = @mlw.Expr::while_loop(
    @mlw.Expr::variable(
      condition_variable,
      @identity.Origin::user(b"condition", None, []),
      [],
    ),
    [@logic.Term::true_formula()],
    [variant],
    @mlw.Expr::variable(
      body_variable,
      @identity.Origin::user(b"body", None, []),
      [],
    ),
    boolean,
    unit,
    [condition_variable, body_variable, measure],
    @identity.Origin::user(b"while", None, []),
    [],
    None,
  )
  guard loop_.view() is Ewhile(_, invariants, variants, _) else {
    fail("while smart constructor lost its loop contracts")
  }
  assert_eq(invariants.length(), 1)
  assert_eq(variants.length(), 1)
  assert_true(loop_.effect().view().termination is Total)
  assert_true(loop_.effect().view().reads.any(variable => variable == measure))

  let divergent = @mlw.Expr::while_loop(
    @mlw.Expr::variable(
      condition_variable,
      @identity.Origin::user(b"condition", None, []),
      [],
    ),
    [],
    [],
    @mlw.Expr::variable(
      body_variable,
      @identity.Origin::user(b"body", None, []),
      [],
    ),
    boolean,
    unit,
    [condition_variable, body_variable],
    @identity.Origin::user(b"while", None, []),
    [],
    None,
  )
  assert_true(divergent.effect().view().termination is Diverges)
}

///|
test "for expressions bind both indices but retain bound reads" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let (_, _, unit) = unit_program_type(context)
  let external = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"i", [], None),
    integer,
    false,
    None,
  )
  let internal = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"i_internal", [], None),
    integer,
    true,
    None,
  )
  let first = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"first", [], None),
    integer,
    false,
    None,
  )
  let last = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"last", [], None),
    integer,
    false,
    None,
  )
  let body_variable = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"body", [], None),
    unit,
    false,
    None,
  )
  let bounds = @mlw.ForBounds::new(first, To, last, None)
  let loop_ = @mlw.Expr::for_loop(
    external,
    bounds,
    internal,
    [@logic.Term::true_formula()],
    @mlw.Expr::variable(
      body_variable,
      @identity.Origin::user(b"body", None, []),
      [],
    ),
    integer,
    unit,
    [external, internal, first, last, body_variable],
    @identity.Origin::user(b"for", None, []),
    [],
    None,
  )
  let reads = loop_.effect().view().reads
  assert_true(reads.any(variable => variable == first))
  assert_true(reads.any(variable => variable == last))
  assert_false(reads.any(variable => variable == external))
  assert_false(reads.any(variable => variable == internal))
}

///|
test "exception match catches raises and local scope rejects leaks" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let (_, _, unit) = unit_program_type(context)
  let exception = @mlw.XSymbol::new(
    context,
    @theory.SemanticName::new(b"Failure", [], None),
    integer,
    None,
  )
  let payload_variable = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"payload", [], None),
    integer,
    false,
    None,
  )
  let raised = @mlw.Expr::raise_exception(
    exception,
    @mlw.Expr::variable(
      payload_variable,
      @identity.Origin::user(b"payload", None, []),
      [],
    ),
    integer,
    unit,
    @identity.Origin::user(b"raise Failure", None, []),
    [],
    None,
  )
  assert_true(raised.effect().view().raises.any(symbol => symbol == exception))
  try
    ignore(
      @mlw.Expr::exception_scope(
        exception,
        raised,
        @identity.Origin::user(b"exception Failure", None, []),
        [],
        None,
      ),
    )
  catch {
    MlwError(diagnostic) =>
      assert_eq(diagnostic.kind, InvalidProgramDeclaration)
  } noraise {
    _ => fail("expected escaping local exception rejection")
  }
  let caught = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"caught", [], None),
    integer,
    false,
    None,
  )
  let branch = @mlw.ExceptionalBranch::new(
    exception,
    [caught],
    @mlw.Expr::variable(caught, @identity.Origin::user(b"caught", None, []), []),
    None,
  )
  let handled = @mlw.Expr::match_with(
    raised,
    [],
    [branch],
    unit,
    @identity.Origin::user(b"try", None, []),
    [],
    None,
  )
  assert_false(
    handled.effect().view().raises.any(symbol => symbol == exception),
  )
  let scoped = @mlw.Expr::exception_scope(
    exception,
    handled,
    @identity.Origin::user(b"exception Failure", None, []),
    [],
    None,
  )
  assert_true(scoped.view() is Eexn(symbol, _) && symbol == exception)
}

///|
test "program patterns track refutable ghost constructors" {
  let context = @identity.CompilationContext::new()
  let (logic_boolean, _, boolean) = boolean_program_type(context)
  let constructor_logic = @logic.LSymbol::new_constructor(
    context,
    b"True",
    @identity.Origin::user(b"True", None, []),
    [],
    @logic.Ty::app(logic_boolean, [], None),
    2,
    None,
  )
  let constructor_cty = @mlw.Cty::trusted_new(
    boolean.context_anchor(),
    [],
    [],
    [],
    [],
    @mlw.Effect::pure(false),
    boolean,
    Visible,
    None,
  )
  let constructor_routine = @mlw.RoutineSymbol::new(
    context,
    b"True",
    mlw_test_origin(b"True", Program, 64U),
    constructor_cty,
    RLls(constructor_logic),
    None,
    None,
  )
  let pattern = @mlw.ProgramPattern::new(
    context,
    PPapp(constructor_routine, []),
    boolean,
    Ghost,
    None,
  )
  assert_true(pattern.view().failure is PGlast)
  assert_true(pattern.view().mask is Ghost)

  let named = @mlw.ProgramPattern::new(
    context,
    PPvar(@theory.SemanticName::new(b"value", [], None), false),
    boolean,
    Ghost,
    None,
  )
  assert_true(
    named.view().variables.length() == 1 &&
    named.view().variables[0].view().ghost,
  )
}

///|
test "assert pure and ghost expressions preserve Why3 effect rules" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let (_, _, unit) = unit_program_type(context)
  let variable = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"x", [], None),
    integer,
    false,
    None,
  )
  let formula = formula_reading_program_variable(context, b"p", variable)
  let assertion = @mlw.Expr::assertion_with_variables(
    Check,
    formula,
    [variable],
    unit,
    @identity.Origin::user(b"check", None, []),
    [],
    None,
  )
  assert_true(assertion.view() is Eassert(Check, _))
  assert_true(assertion.effect().view().reads[0] == variable)

  let pure = @mlw.Expr::pure_term(
    @logic.Term::variable(variable.view().pure_symbol),
    integer,
    [variable],
    @identity.Origin::user(b"pure", None, []),
    [],
    None,
  )
  assert_true(pure.view() is Epure(_))
  assert_true(pure.mask() is Ghost)
  assert_true(pure.effect().view().spoils.is_empty())

  let ghost = @mlw.Expr::variable(
    variable,
    @identity.Origin::user(b"x", None, []),
    [],
  ).ghostify(true, @identity.Origin::user(b"ghost x", None, []), [], None)
  assert_true(ghost.view() is Eghost(_))
  assert_true(ghost.effect().view().ghost)
}

///|
test "program type declarations retain checked witnesses" {
  let context = @identity.CompilationContext::new()
  let (_, program_type, integer) = integer_program_type(context)
  let witness_variable = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"witness", [], None),
    integer,
    false,
    None,
  )
  let witness = @mlw.Expr::variable(
    witness_variable,
    @identity.Origin::user(b"witness", None, []),
    [],
  )
  let declaration = @mlw.ProgramTypeDeclaration::trusted_new(
    program_type,
    [],
    [],
    [],
    None,
    witness=Some(witness),
  )
  assert_true(
    declaration.view().witness is Some(stored) && stored.ity() == integer,
  )
}

///|
test "program type declarations validate projection ownership" {
  let context = @identity.CompilationContext::new()
  let (field, symbol, cell) = mutable_cell_type(context)
  let target = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"target", [], None),
    cell,
    false,
    None,
  )
  let projection_logic = @logic.LSymbol::new_projection(
    context,
    b"contents",
    @identity.Origin::user(b"contents", None, []),
    cell.to_ty(None),
    field.view().ity.to_ty(None),
    None,
  )
  let projection = @mlw.RoutineSymbol::new(
    context,
    b"contents",
    mlw_test_origin(b"contents", Program, 65U),
    @mlw.Cty::trusted_new(
      target.semantic_id(),
      [target],
      [target],
      [],
      [],
      @mlw.Effect::from_reads([target], false),
      field.view().ity,
      Visible,
      None,
    ),
    RLls(projection_logic),
    Some(field),
    None,
  )
  let declaration = @mlw.ProgramTypeDeclaration::new(
    symbol,
    [projection],
    [],
    [],
    None,
  )
  assert_true(
    declaration.view().fields.length() == 1 &&
    declaration.view().fields[0] == projection,
  )

  let foreign_field = @mlw.PVariable::trusted_new(
    context,
    @theory.SemanticName::new(b"foreign", [], None),
    field.view().ity,
    false,
    None,
  )
  let invalid = @mlw.RoutineSymbol::new(
    context,
    b"foreign",
    mlw_test_origin(b"foreign", Program, 66U),
    projection.view().cty,
    RLls(projection_logic),
    Some(foreign_field),
    None,
  )
  try
    ignore(@mlw.ProgramTypeDeclaration::new(symbol, [invalid], [], [], None))
  catch {
    MlwError(diagnostic) =>
      assert_eq(diagnostic.kind, InvalidProgramDeclaration)
  } noraise {
    _ => fail("expected projection ownership rejection")
  }
}

///|
test "program module exception declarations populate the exception namespace" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let exception = @mlw.XSymbol::new(
    context,
    @theory.SemanticName::new(b"Failure", [], None),
    integer,
    None,
  )
  let key = @theory.TheoryKey::new([], b"Exceptions")
  let builder = @mlw.PmoduleBuilder::new(
    context,
    key,
    @theory.SemanticName::new(b"Exceptions", [], None),
  )
  let meta = @theory.Meta::new(b"exception_tag", [MetaString(b"Failure")])
  builder.add_exception_decl_with_metas(exception, [], [meta], None)
  let pmodule = builder.close()
  assert_true(
    pmodule.export_namespace().find_exception([b"Failure"], None) == exception,
  )
  guard pmodule.view().items is [Udecl(PDexn(stored, [], [stored_meta]))] else {
    fail("program exception declaration was not retained")
  }
  assert_true(stored == exception)
  assert_true(stored_meta.view().name == b"exception_tag")
}

///|
fn empty_pmodule(
  context : @identity.CompilationContext,
  path : ArrayView[Bytes],
  name : BytesView,
) -> @mlw.Pmodule raise {
  @mlw.PmoduleBuilder::new(
    context,
    @theory.TheoryKey::new(path, name),
    @theory.SemanticName::new(name, [], None),
  ).close()
}

///|
test "program module scopes retain structure and import only on request" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let cty = @mlw.Cty::trusted_new(
    integer.context_anchor(),
    [],
    [],
    [],
    [],
    @mlw.Effect::pure(false),
    integer,
    Visible,
    None,
  )
  let routine = @mlw.RoutineSymbol::new(
    context,
    b"value",
    mlw_test_origin(b"value", Program, 70U),
    cty,
    RLnone,
    None,
    None,
  )
  let used_builder = @mlw.PmoduleBuilder::new(
    context,
    @theory.TheoryKey::new([b"lib"], b"Used"),
    @theory.SemanticName::new(b"Used", [], None),
  )
  used_builder.add_program_decl(routine, Cany(cty), [], None)
  let used = used_builder.close()

  let qualified = @mlw.PmoduleBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Qualified"),
    @theory.SemanticName::new(b"Qualified", [], None),
  )
  qualified.add_scoped_use(b"Alias", used, false, None)
  assert_true(
    qualified.program_namespace().find_routine([b"Alias", b"value"], None) ==
    routine,
  )
  assert_true(
    qualified.program_namespace().find_routine_option([b"value"]) is None,
  )
  guard qualified.close().view().items is [Uscope(name, [Uuse(source)])] else {
    fail("program use scope was flattened")
  }
  assert_eq(name, b"Alias")
  assert_true(source == used.key())

  let imported = @mlw.PmoduleBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Imported"),
    @theory.SemanticName::new(b"Imported", [], None),
  )
  imported.add_scoped_use(b"Alias", used, true, None)
  assert_true(
    imported.program_namespace().find_routine([b"value"], None) == routine,
  )
}

///|
test "program module records scoped metas and low-level clone witnesses" {
  let context = @identity.CompilationContext::new()
  let source = empty_pmodule(context, [b"lib"], b"Source")
  let builder = @mlw.PmoduleBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Target"),
    @theory.SemanticName::new(b"Target", [], None),
  )
  builder.open_scope(b"Metadata", None)
  let meta = @theory.Meta::new(b"tag", [MetaString(b"nested")])
  builder.add_meta(meta, None)
  builder.close_scope(false, None)
  let witness = @mlw.ProgramCloneWitness::trusted_new(
    context.fresh_id(),
    source.key(),
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    [],
    Plemma,
    None,
  )
  builder.add_clone(
    source,
    @theory.TheoryInstantiation::empty(),
    witness,
    @mlw.ProgramNamespace::empty(),
    None,
  )
  guard builder.close().view().items
    is [Uscope(name, [Umeta(stored)]), Uclone(clone)] else {
    fail("program scope/meta/clone structure was not retained")
  }
  assert_eq(name, b"Metadata")
  assert_true(stored.view().name == b"tag")
  assert_true(clone.view().source == source.key())
  assert_true(clone.view().exception_instantiations.is_empty())
}

///|
test "module interface matching maps routines and feeds clone operations" {
  let context = @identity.CompilationContext::new()
  let (_, _, integer) = integer_program_type(context)
  let cty = @mlw.Cty::trusted_new(
    integer.context_anchor(),
    [],
    [],
    [],
    [],
    @mlw.Effect::pure(false),
    integer,
    Visible,
    None,
  )
  let interface_routine = @mlw.RoutineSymbol::new(
    context,
    b"get",
    mlw_test_origin(b"get", Program, 71U),
    cty,
    RLnone,
    None,
    None,
  )
  let implementation_routine = @mlw.RoutineSymbol::new(
    context,
    b"get",
    mlw_test_origin(b"get", Program, 72U),
    cty,
    RLnone,
    None,
    None,
  )
  let interface_builder = @mlw.PmoduleBuilder::new(
    context,
    @theory.TheoryKey::new([b"sig"], b"Signature"),
    @theory.SemanticName::new(b"Signature", [], None),
  )
  interface_builder.add_program_decl(interface_routine, Cany(cty), [], None)
  let interface_module = interface_builder.close()
  let implementation_builder = @mlw.PmoduleBuilder::new(
    context,
    @theory.TheoryKey::new([b"impl"], b"Implementation"),
    @theory.SemanticName::new(b"Implementation", [], None),
  )
  implementation_builder.add_program_decl(
    implementation_routine,
    Cany(cty),
    [],
    None,
  )
  let implementation = implementation_builder.close()
  let matched = implementation.match_interface(interface_module, None)
  assert_true(
    matched.view().routine_instantiations is [(source, target)] &&
    source == interface_routine &&
    target == implementation_routine,
  )

  let witness = matched.clone_witness(context.fresh_id())
  let target = @mlw.PmoduleBuilder::new(
    context,
    @theory.TheoryKey::new([], b"Public"),
    @theory.SemanticName::new(b"Public", [], None),
  )
  target.add_clone(
    interface_module,
    matched.pure_instantiation(),
    witness,
    @mlw.ProgramNamespace::empty().add_routine(
      b"get",
      implementation_routine,
      None,
    ),
    None,
  )
  assert_true(
    target.program_namespace().find_routine([b"get"], None) ==
    implementation_routine,
  )

  let missing = empty_pmodule(context, [b"impl"], b"Missing")
  try ignore(missing.match_interface(interface_module, None)) catch {
    MlwError(diagnostic) =>
      assert_eq(diagnostic.kind, ProgramInterfaceSymbolNotFound)
  } noraise {
    _ => fail("expected a missing interface routine")
  }
}
