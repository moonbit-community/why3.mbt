// SPDX-License-Identifier: LGPL-2.1-only WITH OCAML-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-28.

///|
priv struct AlgebraicOptions {
  keep_enums : Bool
  keep_records : Bool
  keep_monomorphic : Bool
  no_index : Bool
  no_inversion : Bool
  no_selector : Bool
}

///|
priv struct AlgebraicState {
  context : @identity.CompilationContext
  known : @logic.KnownMap
  equality : @logic.LSymbol
  integer_type : @logic.Ty
  options : AlgebraicOptions
  selectors : Map[@logic.TypeSymbol, @logic.LSymbol]
  constructors : Map[@logic.LSymbol, @logic.LSymbol]
  constructor_projections : Map[@logic.LSymbol, Array[@logic.LSymbol]]
  projections : Map[@logic.LSymbol, @logic.LSymbol]
  kept : Map[@logic.TypeSymbol, Array[@logic.Ty]]
  kept_order : Array[@logic.Ty]
  infinite : Map[@logic.TypeSymbol, Unit]
  material : Map[@logic.TypeSymbol, Array[Bool]]
}

///|
priv struct DeferredTupleDeclaration {
  symbol : @logic.TypeSymbol
  declaration : @logic.Decl
  data : Array[@logic.DataDeclaration]
  use_key : @theory.TheoryKey
}

///|
fn required_builtin_type(
  candidate : @logic.TypeSymbol?,
  expected : @logic.BuiltinTypeKind,
  stage : @identity.GeneratedStage,
) -> @logic.TypeSymbol raise TransformError {
  guard candidate is Some(symbol) && symbol.builtin_kind() == Some(expected) else {
    return fail_transform(
      InvariantFailure,
      stage,
      "static profile is missing an encoding base type",
    )
  }
  symbol
}

///|
fn algebraic_options(
  task : @theory.Task,
) -> AlgebraicOptions raise TransformError {
  let stage = @identity.EliminateAlgebraicIfPoly
  let mut keep_enums = false
  let mut keep_records = false
  let mut keep_monomorphic = false
  let mut no_index = false
  let mut no_inversion = false
  let mut no_selector = false
  for item in task.view().items {
    guard item is TheoryMeta(meta) && meta.view().name == b"eliminate_algebraic" else {
      continue
    }
    guard meta.view().arguments is [MetaString(option)] else {
      return fail_transform(
        UnsupportedStructure,
        stage,
        "eliminate_algebraic expects one string argument",
      )
    }
    match option {
      b"keep_enums" => keep_enums = true
      b"keep_recs" => keep_records = true
      b"keep_mono" => keep_monomorphic = true
      b"no_index" => no_index = true
      b"no_inversion" => no_inversion = true
      b"no_selector" => no_selector = true
      _ =>
        return fail_transform(
          UnsupportedStructure,
          stage,
          "unknown eliminate_algebraic option",
        )
    }
  }
  {
    keep_enums,
    keep_records,
    keep_monomorphic,
    no_index,
    no_inversion,
    no_selector,
  }
}

///|
fn tagged_algebraic_types(task : @theory.Task) -> Array[@logic.Ty] {
  let kept : Array[@logic.Ty] = []
  for item in task.view().items {
    guard item is TheoryMeta(meta) else { continue }
    let view = meta.view()
    if view.name == b"algebraic:kept" &&
      view.arguments is [MetaType(ty)] &&
      !kept.contains(ty) {
      kept.push(ty)
    }
  }
  kept
}

///|
fn algebraic_material_arguments(
  task : @theory.Task,
) -> Map[@logic.TypeSymbol, Array[Bool]] {
  let result : Map[@logic.TypeSymbol, Array[Bool]] = Map([])
  for item in task.view().items {
    guard item is TheoryMeta(meta) &&
      meta.view().name == b"material_type_arg" &&
      meta.view().arguments is [MetaTypeSymbol(symbol), MetaInteger(index)] else {
      continue
    }
    let index = index.to_int()
    if index < 0 || index >= symbol.arity() {
      continue
    }
    let material = match result.get(symbol) {
      Some(material) => material
      None => {
        let material = [ for _ in symbol.view().parameters => false ]
        result[symbol] = material
        material
      }
    }
    material[index] = true
  }
  result
}

///|
fn algebraic_infinite_types(
  task : @theory.Task,
) -> Map[@logic.TypeSymbol, Unit] {
  let result : Map[@logic.TypeSymbol, Unit] = Map([])
  for item in task.view().items {
    guard item is TheoryMeta(meta) &&
      meta.view().name == b"infinite_type" &&
      meta.view().arguments is [MetaTypeSymbol(symbol)] else {
      continue
    }
    result[symbol] = ()
  }
  result
}

///|
fn type_contains_one_of(
  ty : @logic.Ty,
  symbols : Map[@logic.TypeSymbol, Unit],
) -> Bool {
  match ty.view() {
    TyVar(_) => false
    TyApp(symbol, arguments) =>
      symbols.contains(symbol) ||
      arguments.any(argument => type_contains_one_of(argument, symbols))
  }
}

///|
fn data_group_symbols(
  known : @logic.KnownMap,
  symbol : @logic.TypeSymbol,
) -> Map[@logic.TypeSymbol, Unit] {
  let result : Map[@logic.TypeSymbol, Unit] = Map([])
  guard known.find_declaration(@logic.TypeDependency(symbol))
    is Some(declaration) &&
    declaration.view() is Ddata(declarations) else {
    return result
  }
  for data in declarations {
    result[data.view().type_symbol] = ()
  }
  result
}

///|
fn complete_kept_type(
  known : @logic.KnownMap,
  ty : @logic.Ty,
  completed : Array[@logic.Ty],
) -> Unit raise TransformError {
  if completed.contains(ty) {
    return
  }
  completed.push(ty)
  guard ty.view() is TyApp(symbol, arguments) else { return }
  for argument in arguments {
    complete_kept_type(known, argument, completed)
  }
  let constructors = known.find_constructors(symbol, None) catch { _ => return }
  if constructors.is_empty() {
    return
  }
  let view = symbol.view()
  let formal = @logic.Ty::app(
    symbol,
    view.parameters.map(@logic.Ty::variable),
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        @identity.EliminateAlgebraicIfPoly,
        "cannot construct an algebraic type template",
      )
  }
  let substitution = @logic.TySubstitution::new().match_type(formal, ty, None) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        @identity.EliminateAlgebraicIfPoly,
        "cannot instantiate an algebraic type template",
      )
  }
  let recursive = data_group_symbols(known, symbol)
  for data_constructor in constructors {
    for field in data_constructor.view().symbol.view().argument_types {
      if type_contains_one_of(field, recursive) {
        continue
      }
      complete_kept_type(
        known,
        substitution.apply(field, None) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              @identity.EliminateAlgebraicIfPoly,
              "cannot instantiate an algebraic field type",
            )
        },
        completed,
      )
    }
  }
}

///|
fn completed_kept_types(
  known : @logic.KnownMap,
  task : @theory.Task,
) -> Array[@logic.Ty] raise TransformError {
  let completed : Array[@logic.Ty] = []
  for ty in tagged_algebraic_types(task) {
    complete_kept_type(known, ty, completed)
  }
  completed
}

///|
fn add_kept_type(state : AlgebraicState, ty : @logic.Ty) -> Unit {
  guard ty.view() is TyApp(symbol, _) else { return }
  let instances = match state.kept.get(symbol) {
    Some(instances) => instances
    None => {
      let instances : Array[@logic.Ty] = []
      state.kept[symbol] = instances
      instances
    }
  }
  if !instances.contains(ty) {
    instances.push(ty)
  }
  if !state.kept_order.contains(ty) {
    state.kept_order.push(ty)
  }
}

///|
fn compare_algebraic_kept_type(left : @logic.Ty, right : @logic.Ty) -> Int {
  left.allocation_order().compare(right.allocation_order())
}

///|
fn ordered_algebraic_kept_types(state : AlgebraicState) -> Array[@logic.Ty] {
  let entries = [ for symbol, instances in state.kept => (symbol, instances) ]
  entries.sort_by((left, right) => {
    left.0.semantic_id().local_id().compare(right.0.semantic_id().local_id())
  })
  let result : Array[@logic.Ty] = []
  for entry in entries {
    let instances = entry.1.copy()
    instances.sort_by(compare_algebraic_kept_type)
    result.push_iter(instances.iter())
  }
  result
}

///|
fn algebraic_generated_origin(
  name : BytesView,
  parent : @identity.Origin,
) -> @identity.Origin {
  let attributes = derived_generated_attributes(parent)
  if parent
    .attributes()
    .any(attribute => attribute == b"why3:builtin:tuple-constructor") &&
    !attributes.contains(b"builtin") {
    attributes.push(b"builtin")
  }
  derived_generated_origin(
    @identity.EliminateAlgebraicIfPoly,
    name,
    parent,
    attributes,
  )
}

///|
fn algebraic_fresh_origin(name : BytesView) -> @identity.Origin {
  @identity.Origin::generated(@identity.EliminateAlgebraicIfPoly, name, None, [])
}

///|
fn algebraic_fresh_variable(
  state : AlgebraicState,
  name : BytesView,
  ty : @logic.Ty,
) -> @logic.VSymbol raise TransformError {
  @logic.VSymbol::new(
    state.context,
    name,
    algebraic_fresh_origin(name),
    ty,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateAlgebraicIfPoly,
        "cannot create an algebraic axiom binder",
      )
  }
}

///|
fn algebraic_parameter_item(
  state : AlgebraicState,
  symbol : @logic.LSymbol,
) -> @theory.TheoryItem raise TransformError {
  TheoryDecl(
    @logic.Decl::parameter(state.context, symbol.view().origin, symbol, None) catch {
      _ =>
        fail_transform(
          InvariantFailure,
          @identity.EliminateAlgebraicIfPoly,
          "cannot declare an algebraic encoding symbol",
        )
    },
  )
}

///|
fn algebraic_proposition_item(
  state : AlgebraicState,
  name : BytesView,
  parent : @identity.Origin,
  formula : @logic.Term,
) -> @theory.TheoryItem raise TransformError {
  let origin = algebraic_generated_origin(name, parent)
  let proposition = @logic.PrSymbol::new(state.context, name, origin)
  TheoryDecl(
    @logic.Decl::proposition(
      state.context,
      origin,
      Paxiom,
      proposition,
      formula,
      None,
    ) catch {
      _ =>
        fail_transform(
          InvariantFailure,
          @identity.EliminateAlgebraicIfPoly,
          "cannot declare an algebraic encoding axiom",
        )
    },
  )
}

///|
fn algebraic_type_item(
  state : AlgebraicState,
  symbol : @logic.TypeSymbol,
) -> @theory.TheoryItem raise TransformError {
  TheoryDecl(
    @logic.Decl::type_declaration(
      state.context,
      symbol.origin(),
      [symbol],
      None,
    ) catch {
      _ =>
        fail_transform(
          InvariantFailure,
          @identity.EliminateAlgebraicIfPoly,
          "cannot retain an abstract algebraic type",
        )
    },
  )
}

///|
fn ordinary_clone(
  state : AlgebraicState,
  source : @logic.LSymbol,
) -> @logic.LSymbol raise TransformError {
  let view = source.view()
  let origin = algebraic_generated_origin(view.name, view.origin)
  match view.result_type {
    Some(result) =>
      @logic.LSymbol::new_function(
        state.context,
        view.name,
        origin,
        view.argument_types,
        result,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.EliminateAlgebraicIfPoly,
            "cannot clone an algebraic function",
          )
      }
    None =>
      @logic.LSymbol::new_predicate(
        state.context,
        view.name,
        origin,
        view.argument_types,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.EliminateAlgebraicIfPoly,
            "cannot clone an algebraic predicate",
          )
      }
  }
}

///|
fn algebraic_apply(
  symbol : @logic.LSymbol,
  arguments : ArrayView[@logic.Term],
  result_type : @logic.Ty?,
) -> @logic.Term raise TransformError {
  @logic.Term::elaborated_apply(symbol, arguments, result_type, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateAlgebraicIfPoly,
        "cannot apply an algebraic encoding symbol",
      )
  }
}

///|
fn algebraic_equality(
  state : AlgebraicState,
  left : @logic.Term,
  right : @logic.Term,
) -> @logic.Term raise TransformError {
  algebraic_apply(state.equality, [left, right], None)
}

///|
fn encoded_algebraic_type(state : AlgebraicState, ty : @logic.Ty?) -> Bool {
  guard ty is Some(ty) && ty.view() is TyApp(symbol, _) else { return false }
  match state.kept.get(symbol) {
    Some(instances) => !instances.contains(ty)
    None => true
  }
}

///|
fn algebraic_constructors(
  state : AlgebraicState,
  symbol : @logic.TypeSymbol,
) -> Array[@logic.DataConstructor] raise TransformError {
  state.known.find_constructors(symbol, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateAlgebraicIfPoly,
        "algebraic type has no known declaration",
      )
  }
}

///|
fn algebraic_constructor_term(
  state : AlgebraicState,
  original : @logic.LSymbol,
  arguments : ArrayView[@logic.Term],
  result_type : @logic.Ty,
) -> @logic.Term raise TransformError {
  guard state.constructors.get(original) is Some(replacement) else {
    return fail_transform(
      InvariantFailure,
      @identity.EliminateAlgebraicIfPoly,
      "algebraic constructor has no encoding",
    )
  }
  algebraic_apply(replacement, arguments, Some(result_type))
}

///|
fn algebraic_projection_term(
  projection : @logic.LSymbol,
  argument : @logic.Term,
) -> @logic.Term raise TransformError {
  @logic.Term::apply_function(projection, [argument], None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateAlgebraicIfPoly,
        "cannot infer an algebraic projection",
      )
  }
}

///|
fn remove_available_variables(
  available : Map[@logic.VSymbol, Unit],
  term : @logic.Term,
) -> Map[@logic.VSymbol, Unit] {
  let result = available.copy()
  for variable in term.free_variables() {
    result.remove(variable)
  }
  result
}

///|
fn algebraic_quantify(
  quantifier : @logic.Quantifier,
  variables : ArrayView[@logic.VSymbol],
  body : @logic.Term,
) -> @logic.Term raise TransformError {
  quantifier_simplified(
    quantifier,
    variables,
    [],
    body,
    @identity.EliminateAlgebraicIfPoly,
  )
}

///|
fn algebraic_rewrite_any(
  state : AlgebraicState,
  term : @logic.Term,
) -> @logic.Term raise TransformError {
  if term.ty() is Some(_) {
    algebraic_rewrite_value(state, term)
  } else {
    algebraic_rewrite_formula(state, Map([]), true, term)
  }
}

///|
fn algebraic_value_case(
  state : AlgebraicState,
  source : @logic.Term,
  scrutinee : @logic.Term,
  branches : ArrayView[@logic.TermBranch],
) -> @logic.Term raise TransformError {
  let scrutinee = algebraic_rewrite_value(state, scrutinee)
  guard scrutinee.ty() is Some(ty) && ty.view() is TyApp(type_symbol, _) else {
    return fail_transform(
      UnsupportedStructure,
      @identity.EliminateAlgebraicIfPoly,
      "encoded match has a non-algebraic scrutinee",
    )
  }
  let bodies : Map[@logic.LSymbol, @logic.Term] = Map([])
  let mut wildcard : @logic.Term? = None
  for branch in branches {
    let view = branch.view()
    let body = algebraic_rewrite_any(state, view.body)
    match view.pattern.view() {
      Papp(constructor, patterns, _) => {
        guard state.constructor_projections.get(constructor)
          is Some(projections) &&
          projections.length() == patterns.length() else {
          return fail_transform(
            InvariantFailure,
            @identity.EliminateAlgebraicIfPoly,
            "compiled match has no constructor projections",
          )
        }
        let mut body = body
        for index, pattern in patterns {
          guard pattern.view() is Pvar(variable) else {
            return fail_transform(
              UnsupportedStructure,
              @identity.EliminateAlgebraicIfPoly,
              "compile_match left a nested value pattern",
            )
          }
          body = let_simplified(
            state.context,
            variable,
            algebraic_projection_term(projections[index], scrutinee),
            body,
            false,
            @identity.EliminateAlgebraicIfPoly,
          )
        }
        bodies[constructor] = body
      }
      Pwild(_) => wildcard = Some(body)
      _ =>
        return fail_transform(
          UnsupportedStructure,
          @identity.EliminateAlgebraicIfPoly,
          "compile_match left an unsupported value pattern",
        )
    }
  }
  let alternatives : Array[@logic.Term] = []
  for data_constructor in algebraic_constructors(state, type_symbol) {
    let constructor = data_constructor.view().symbol
    match bodies.get(constructor) {
      Some(body) => alternatives.push(body)
      None =>
        match wildcard {
          Some(body) => alternatives.push(body)
          None =>
            return fail_transform(
              UnsupportedStructure,
              @identity.EliminateAlgebraicIfPoly,
              "compiled value match is not exhaustive",
            )
        }
    }
  }
  let replacement = match alternatives {
    [only] => only
    _ => {
      guard state.selectors.get(type_symbol) is Some(selector) else {
        return fail_transform(
          InvariantFailure,
          @identity.EliminateAlgebraicIfPoly,
          "encoded value match has no selector",
        )
      }
      let arguments = [scrutinee]
      for alternative in alternatives {
        arguments.push(alternative)
      }
      algebraic_apply(selector, arguments, source.ty())
    }
  }
  copy_term_decoration(source, replacement)
}

///|
fn algebraic_rewrite_value(
  state : AlgebraicState,
  term : @logic.Term,
) -> @logic.Term raise TransformError {
  match term.view() {
    Tcase(scrutinee, branches) if encoded_algebraic_type(state, scrutinee.ty()) =>
      algebraic_value_case(state, term, scrutinee, branches)
    Tapp(symbol, _, arguments) if symbol.view().role is Constructor(_) &&
      encoded_algebraic_type(state, term.ty()) => {
      guard term.ty() is Some(result_type) &&
        state.constructors.get(symbol) is Some(replacement) else {
        return fail_transform(
          InvariantFailure,
          @identity.EliminateAlgebraicIfPoly,
          "constructor application has no algebraic encoding",
        )
      }
      copy_term_decoration(
        term,
        algebraic_apply(
          replacement,
          arguments.map(argument => algebraic_rewrite_any(state, argument)),
          Some(result_type),
        ),
      )
    }
    Tapp(symbol, _, [argument]) if symbol.view().role is Projection &&
      encoded_algebraic_type(state, argument.ty()) => {
      guard state.projections.get(symbol) is Some(replacement) else {
        return fail_transform(
          InvariantFailure,
          @identity.EliminateAlgebraicIfPoly,
          "projection application has no algebraic encoding: " +
          symbol.view().name.to_string(),
        )
      }
      copy_term_decoration(
        term,
        algebraic_apply(
          replacement,
          [algebraic_rewrite_value(state, argument)],
          term.ty(),
        ),
      )
    }
    _ =>
      map_plain(
        term,
        child => algebraic_rewrite_any(state, child),
        @identity.EliminateAlgebraicIfPoly,
      )
  }
}

///|
fn algebraic_formula_branch(
  state : AlgebraicState,
  scrutinee : @logic.Term,
  available : Map[@logic.VSymbol, Unit],
  positive : Bool,
  variables : ArrayView[@logic.VSymbol],
  body : @logic.Term,
  constructor : @logic.LSymbol,
) -> @logic.Term raise TransformError {
  guard scrutinee.ty() is Some(result_type) else {
    return fail_transform(
      InvariantFailure,
      @identity.EliminateAlgebraicIfPoly,
      "algebraic formula match lost its scrutinee type",
    )
  }
  let head = algebraic_constructor_term(
    state,
    constructor,
    variables.map(@logic.Term::variable),
    result_type,
  )
  match scrutinee.view() {
    Tvar(variable) if available.contains(variable) => {
      let body = let_simplified(
        state.context,
        variable,
        head,
        body,
        false,
        @identity.EliminateAlgebraicIfPoly,
      )
      algebraic_quantify(
        if positive {
          ForallQuantifier
        } else {
          ExistsQuantifier
        },
        variables,
        body,
      )
    }
    _ => {
      let equality = algebraic_equality(state, scrutinee, head)
      let guarded = binary_simplified(
        if positive {
          Implies
        } else {
          And
        },
        equality,
        body,
        @identity.EliminateAlgebraicIfPoly,
      )
      algebraic_quantify(
        if positive {
          ForallQuantifier
        } else {
          ExistsQuantifier
        },
        variables,
        guarded,
      )
    }
  }
}

///|
fn algebraic_formula_case(
  state : AlgebraicState,
  source : @logic.Term,
  available : Map[@logic.VSymbol, Unit],
  positive : Bool,
  scrutinee : @logic.Term,
  branches : ArrayView[@logic.TermBranch],
) -> @logic.Term raise TransformError {
  let scrutinee = algebraic_rewrite_value(state, scrutinee)
  guard scrutinee.ty() is Some(ty) && ty.view() is TyApp(type_symbol, _) else {
    return fail_transform(
      UnsupportedStructure,
      @identity.EliminateAlgebraicIfPoly,
      "encoded formula match has a non-algebraic scrutinee",
    )
  }
  let branch_available = remove_available_variables(available, scrutinee)
  let bodies : Map[@logic.LSymbol, (@logic.Term, Array[@logic.VSymbol])] = Map([])
  let mut wildcard : @logic.Term? = None
  for branch in branches {
    let view = branch.view()
    let body = algebraic_rewrite_formula(
      state,
      branch_available,
      positive,
      view.body,
    )
    match view.pattern.view() {
      Papp(constructor, patterns, _) => {
        let variables : Array[@logic.VSymbol] = []
        for pattern in patterns {
          guard pattern.view() is Pvar(variable) else {
            return fail_transform(
              UnsupportedStructure,
              @identity.EliminateAlgebraicIfPoly,
              "compile_match left a nested formula pattern",
            )
          }
          variables.push(variable)
        }
        bodies[constructor] = (body, variables)
      }
      Pwild(_) => wildcard = Some(body)
      _ =>
        return fail_transform(
          UnsupportedStructure,
          @identity.EliminateAlgebraicIfPoly,
          "compile_match left an unsupported formula pattern",
        )
    }
  }
  let alternatives : Array[@logic.Term] = []
  for data_constructor in algebraic_constructors(state, type_symbol) {
    let constructor_view = data_constructor.view()
    let (body, variables) = match bodies.get(constructor_view.symbol) {
      Some(found) => found
      None => {
        guard wildcard is Some(body) &&
          state.constructor_projections.get(constructor_view.symbol)
          is Some(projections) else {
          return fail_transform(
            UnsupportedStructure,
            @identity.EliminateAlgebraicIfPoly,
            "compiled formula match is not exhaustive",
          )
        }
        let variables : Array[@logic.VSymbol] = []
        for projection in projections {
          let projected = algebraic_projection_term(projection, scrutinee)
          guard projected.ty() is Some(field_type) else {
            return fail_transform(
              InvariantFailure,
              @identity.EliminateAlgebraicIfPoly,
              "algebraic projection lost its result type",
            )
          }
          variables.push(algebraic_fresh_variable(state, b"w", field_type))
        }
        (body, variables)
      }
    }
    alternatives.push(
      algebraic_formula_branch(
        state,
        scrutinee,
        available,
        positive,
        variables,
        body,
        constructor_view.symbol,
      ),
    )
  }
  guard !alternatives.is_empty() else {
    return fail_transform(
      InvariantFailure,
      @identity.EliminateAlgebraicIfPoly,
      "algebraic formula match has no constructors",
    )
  }
  let mut replacement = alternatives[0]
  for index = 1; index < alternatives.length(); index = index + 1 {
    replacement = binary_simplified(
      if positive {
        And
      } else {
        Or
      },
      replacement,
      alternatives[index],
      @identity.EliminateAlgebraicIfPoly,
    )
  }
  copy_term_decoration(source, replacement)
}

///|
fn algebraic_rewrite_formula_if(
  state : AlgebraicState,
  positive : Bool,
  condition : @logic.Term,
  yes : @logic.Term,
  no : @logic.Term,
) -> @logic.Term raise TransformError {
  let positive_condition = algebraic_rewrite_formula(
    state,
    Map([]),
    positive,
    condition,
  )
  let negative_condition = algebraic_rewrite_formula(
    state,
    Map([]),
    !positive,
    condition,
  )
  let yes = algebraic_rewrite_formula(state, Map([]), positive, yes)
  let no = algebraic_rewrite_formula(state, Map([]), positive, no)
  if positive_condition == negative_condition {
    return @logic.Term::if_then_else(positive_condition, yes, no, None) catch {
      _ =>
        fail_transform(
          InvariantFailure,
          @identity.EliminateAlgebraicIfPoly,
          "cannot rebuild a formula conditional",
        )
    }
  }
  if positive {
    binary_simplified(
      And,
      binary_simplified(
        Implies,
        negative_condition,
        yes,
        @identity.EliminateAlgebraicIfPoly,
      ),
      binary_simplified(
        Implies,
        not_simplified(positive_condition),
        no,
        @identity.EliminateAlgebraicIfPoly,
      ),
      @identity.EliminateAlgebraicIfPoly,
    )
  } else {
    binary_simplified(
      Or,
      binary_simplified(
        And,
        positive_condition,
        yes,
        @identity.EliminateAlgebraicIfPoly,
      ),
      binary_simplified(
        And,
        not_simplified(negative_condition),
        no,
        @identity.EliminateAlgebraicIfPoly,
      ),
      @identity.EliminateAlgebraicIfPoly,
    )
  }
}

///|
fn algebraic_rewrite_formula_iff(
  state : AlgebraicState,
  positive : Bool,
  left : @logic.Term,
  right : @logic.Term,
) -> @logic.Term raise TransformError {
  let left_positive = algebraic_rewrite_formula(state, Map([]), positive, left)
  let left_negative = algebraic_rewrite_formula(state, Map([]), !positive, left)
  let right_positive = algebraic_rewrite_formula(
    state,
    Map([]),
    positive,
    right,
  )
  let right_negative = algebraic_rewrite_formula(
    state,
    Map([]),
    !positive,
    right,
  )
  if left_positive == left_negative && right_positive == right_negative {
    return @logic.Term::binary(Iff, left_positive, right_positive, None) catch {
      _ =>
        fail_transform(
          InvariantFailure,
          @identity.EliminateAlgebraicIfPoly,
          "cannot rebuild an algebraic equivalence",
        )
    }
  }
  if positive {
    binary_simplified(
      And,
      binary_simplified(
        Implies,
        left_negative,
        right_positive,
        @identity.EliminateAlgebraicIfPoly,
      ),
      binary_simplified(
        Implies,
        right_negative,
        left_positive,
        @identity.EliminateAlgebraicIfPoly,
      ),
      @identity.EliminateAlgebraicIfPoly,
    )
  } else {
    binary_simplified(
      Implies,
      binary_simplified(
        Or,
        left_negative,
        right_negative,
        @identity.EliminateAlgebraicIfPoly,
      ),
      binary_simplified(
        And,
        left_positive,
        right_positive,
        @identity.EliminateAlgebraicIfPoly,
      ),
      @identity.EliminateAlgebraicIfPoly,
    )
  }
}

///|
fn algebraic_rewrite_formula(
  state : AlgebraicState,
  available : Map[@logic.VSymbol, Unit],
  positive : Bool,
  formula : @logic.Term,
) -> @logic.Term raise TransformError {
  match formula.view() {
    Tcase(scrutinee, branches) if encoded_algebraic_type(state, scrutinee.ty()) =>
      algebraic_formula_case(
        state, formula, available, positive, scrutinee, branches,
      )
    Tquant(quantifier, binders, triggers, body) if (
        quantifier == ForallQuantifier && positive
      ) ||
      (quantifier == ExistsQuantifier && !positive) => {
      let nested = available.copy()
      for binder in binders {
        nested[binder] = ()
      }
      let mapped_triggers = triggers.map(group => {
        group.map(trigger => algebraic_rewrite_any(state, trigger))
      })
      copy_term_decoration(
        formula,
        quantifier_simplified(
          quantifier,
          binders,
          mapped_triggers,
          algebraic_rewrite_formula(state, nested, positive, body),
          @identity.EliminateAlgebraicIfPoly,
        ),
      )
    }
    Tbinop(And, left, right) if positive =>
      copy_term_decoration(
        formula,
        @logic.Term::binary(
          And,
          algebraic_rewrite_formula(state, available, positive, left),
          algebraic_rewrite_formula(state, available, positive, right),
          None,
        ) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              @identity.EliminateAlgebraicIfPoly,
              "cannot rebuild a positive conjunction",
            )
        },
      )
    Tbinop(Or, left, right) if !positive =>
      copy_term_decoration(
        formula,
        @logic.Term::binary(
          Or,
          algebraic_rewrite_formula(state, available, positive, left),
          algebraic_rewrite_formula(state, available, positive, right),
          None,
        ) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              @identity.EliminateAlgebraicIfPoly,
              "cannot rebuild a negative disjunction",
            )
        },
      )
    Tlet(variable, value, body) => {
      let nested = remove_available_variables(available, value)
      copy_term_decoration(
        formula,
        @logic.Term::let_in(
          variable,
          algebraic_rewrite_value(state, value),
          algebraic_rewrite_formula(state, nested, positive, body),
          None,
        ) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              @identity.EliminateAlgebraicIfPoly,
              "cannot rebuild an algebraic formula let",
            )
        },
      )
    }
    Tbinop(Implies, left, right) =>
      copy_term_decoration(
        formula,
        @logic.Term::binary(
          Implies,
          algebraic_rewrite_formula(state, Map([]), !positive, left),
          algebraic_rewrite_formula(state, Map([]), positive, right),
          None,
        ) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              @identity.EliminateAlgebraicIfPoly,
              "cannot rebuild an algebraic implication",
            )
        },
      )
    Tbinop(Iff, left, right) =>
      copy_term_decoration(
        formula,
        algebraic_rewrite_formula_iff(state, positive, left, right),
      )
    Tnot(inner) =>
      copy_term_decoration(
        formula,
        @logic.Term::not(
          algebraic_rewrite_formula(state, Map([]), !positive, inner),
          None,
        ) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              @identity.EliminateAlgebraicIfPoly,
              "cannot rebuild an algebraic negation",
            )
        },
      )
    Tif(condition, yes, no) =>
      copy_term_decoration(
        formula,
        algebraic_rewrite_formula_if(state, positive, condition, yes, no),
      )
    _ =>
      map_plain(
        formula,
        child => {
          if child.ty() is Some(_) {
            algebraic_rewrite_value(state, child)
          } else {
            algebraic_rewrite_formula(state, Map([]), positive, child)
          }
        },
        @identity.EliminateAlgebraicIfPoly,
      )
  }
}

///|
fn nonnegative_decimal_bytes(value : Int) -> Bytes {
  let digits : Array[Byte] = []
  let mut value = value
  if value == 0 {
    digits.push(b'0')
  } else {
    while value > 0 {
      digits.push((b'0'.to_int() + value % 10).to_byte())
      value = value / 10
    }
  }
  let buffer = @buffer.Buffer(size_hint=digits.length())
  for index = digits.length() - 1; index >= 0; index = index - 1 {
    buffer.write_byte(digits[index])
  }
  buffer.to_bytes()
}

///|
fn generic_data_type(
  symbol : @logic.TypeSymbol,
) -> @logic.Ty raise TransformError {
  @logic.Ty::app(
    symbol,
    symbol.view().parameters.map(@logic.Ty::variable),
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateAlgebraicIfPoly,
        "cannot construct a generic algebraic type",
      )
  }
}

///|
fn algebraic_raw_forall(
  variables : ArrayView[@logic.VSymbol],
  triggers : ArrayView[Array[@logic.Term]],
  body : @logic.Term,
) -> @logic.Term raise TransformError {
  quantifier_simplified(
    ForallQuantifier,
    variables,
    triggers,
    body,
    @identity.EliminateAlgebraicIfPoly,
  )
}

///|
fn add_abstract_constructors(
  state : AlgebraicState,
  constructors : ArrayView[@logic.DataConstructor],
  output : Array[@theory.TheoryItem],
) -> Unit raise TransformError {
  for data_constructor in constructors {
    let original = data_constructor.view().symbol
    let replacement = ordinary_clone(state, original)
    state.constructors[original] = replacement
    output.push(algebraic_parameter_item(state, replacement))
  }
}

///|
fn add_selector(
  state : AlgebraicState,
  type_symbol : @logic.TypeSymbol,
  ty : @logic.Ty,
  constructors : ArrayView[@logic.DataConstructor],
  output : Array[@theory.TheoryItem],
) -> Unit raise TransformError {
  if state.options.no_selector || constructors.length() <= 1 {
    return
  }
  let type_variable = @logic.TyVarSymbol::new(
    state.context,
    b"a",
    algebraic_fresh_origin(b"a"),
  )
  let result_type = @logic.Ty::variable(type_variable)
  let argument_types = [ty]
  for _ in constructors {
    argument_types.push(result_type)
  }
  let name = b"match_" + type_symbol.name().to_owned()
  let selector = @logic.LSymbol::new_function(
    state.context,
    name,
    algebraic_generated_origin(name, type_symbol.origin()),
    argument_types,
    result_type,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        @identity.EliminateAlgebraicIfPoly,
        "cannot create an algebraic selector",
      )
  }
  state.selectors[type_symbol] = selector
  output.push(algebraic_parameter_item(state, selector))
  let selector_variables : Array[@logic.VSymbol] = []
  for _ in constructors {
    selector_variables.push(algebraic_fresh_variable(state, b"z", result_type))
  }
  let selector_terms = selector_variables.map(@logic.Term::variable)
  for index, data_constructor in constructors {
    let constructor = data_constructor.view().symbol
    let constructor_variables : Array[@logic.VSymbol] = []
    for reverse_index = 0
        reverse_index < constructor.view().argument_types.length()
        reverse_index = reverse_index + 1 {
      let argument_index = constructor.view().argument_types.length() -
        reverse_index -
        1
      constructor_variables.push(
        algebraic_fresh_variable(
          state,
          b"u",
          constructor.view().argument_types[argument_index],
        ),
      )
    }
    let constructor_arguments : Array[@logic.Term] = []
    for reverse_index = 0
        reverse_index < constructor_variables.length()
        reverse_index = reverse_index + 1 {
      constructor_arguments.push(
        @logic.Term::variable(
          constructor_variables[constructor_variables.length() -
          reverse_index -
          1],
        ),
      )
    }
    let head = algebraic_constructor_term(
      state, constructor, constructor_arguments, ty,
    )
    let selector_arguments = [head]
    for term in selector_terms {
      selector_arguments.push(term)
    }
    let selected = algebraic_apply(
      selector,
      selector_arguments,
      Some(result_type),
    )
    let body = algebraic_equality(state, selected, selector_terms[index])
    let binders : Array[@logic.VSymbol] = []
    for variable in selector_variables {
      binders.push(variable)
    }
    for reverse_index = 0
        reverse_index < constructor_variables.length()
        reverse_index = reverse_index + 1 {
      binders.push(
        constructor_variables[constructor_variables.length() - reverse_index - 1],
      )
    }
    let axiom = algebraic_raw_forall(binders, [], body)
    let axiom_name = name + b"_" + constructor.view().name
    output.push(
      algebraic_proposition_item(
        state,
        axiom_name,
        constructor.view().origin,
        axiom,
      ),
    )
  }
}

///|
fn integer_constant(
  state : AlgebraicState,
  value : Int,
) -> @logic.Term raise TransformError {
  @logic.Term::constant(
    @logic.Constant::integer(@literal.ILitUnk, BigInt::from_int(value)),
    state.integer_type,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateAlgebraicIfPoly,
        "cannot create an algebraic constructor index",
      )
  }
}

///|
fn add_indexer(
  state : AlgebraicState,
  type_symbol : @logic.TypeSymbol,
  ty : @logic.Ty,
  constructors : ArrayView[@logic.DataConstructor],
  output : Array[@theory.TheoryItem],
) -> Unit raise TransformError {
  if constructors.length() <= 1 || state.options.no_index {
    return
  }
  let name = b"index_" + type_symbol.name().to_owned()
  let indexer = @logic.LSymbol::new_function(
    state.context,
    name,
    algebraic_generated_origin(name, type_symbol.origin()),
    [ty],
    state.integer_type,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        @identity.EliminateAlgebraicIfPoly,
        "cannot create an algebraic indexer",
      )
  }
  output.push(algebraic_parameter_item(state, indexer))
  for index, data_constructor in constructors {
    let constructor = data_constructor.view().symbol
    let variables : Array[@logic.VSymbol] = []
    for reverse_index = 0
        reverse_index < constructor.view().argument_types.length()
        reverse_index = reverse_index + 1 {
      let argument_index = constructor.view().argument_types.length() -
        reverse_index -
        1
      variables.push(
        algebraic_fresh_variable(
          state,
          b"u",
          constructor.view().argument_types[argument_index],
        ),
      )
    }
    let arguments : Array[@logic.Term] = []
    for reverse_index = 0
        reverse_index < variables.length()
        reverse_index = reverse_index + 1 {
      arguments.push(
        @logic.Term::variable(variables[variables.length() - reverse_index - 1]),
      )
    }
    let head = algebraic_constructor_term(state, constructor, arguments, ty)
    let indexed = algebraic_apply(indexer, [head], Some(state.integer_type))
    let body = algebraic_equality(
      state,
      indexed,
      integer_constant(state, index),
    )
    let binders : Array[@logic.VSymbol] = []
    for reverse_index = 0
        reverse_index < variables.length()
        reverse_index = reverse_index + 1 {
      binders.push(variables[variables.length() - reverse_index - 1])
    }
    let axiom = algebraic_raw_forall(
      binders,
      if binders.is_empty() {
        []
      } else {
        [[head]]
      },
      body,
    )
    output.push(
      algebraic_proposition_item(
        state,
        name + b"_" + constructor.view().name,
        constructor.view().origin,
        axiom,
      ),
    )
  }
}

///|
fn complete_constructor_projections(
  state : AlgebraicState,
  data_constructor : @logic.DataConstructor,
) -> Array[@logic.LSymbol] raise TransformError {
  let view = data_constructor.view()
  guard view.symbol.view().result_type is Some(source_type) else {
    return fail_transform(
      InvariantFailure,
      @identity.EliminateAlgebraicIfPoly,
      "data constructor has no result type",
    )
  }
  let completed : Array[@logic.LSymbol] = []
  for index, projection in view.projections {
    match projection {
      Some(projection) => completed.push(projection)
      None => {
        let name = view.symbol.view().name +
          b"_proj_" +
          nonnegative_decimal_bytes(index + 1)
        let projection = @logic.LSymbol::new_projection(
          state.context,
          name,
          algebraic_generated_origin(name, view.symbol.view().origin),
          source_type,
          view.symbol.view().argument_types[index],
          None,
        ) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              @identity.EliminateAlgebraicIfPoly,
              "cannot complete an algebraic projection",
            )
        }
        completed.push(projection)
      }
    }
  }
  completed
}

///|
fn add_projections(
  state : AlgebraicState,
  ty : @logic.Ty,
  constructors : ArrayView[@logic.DataConstructor],
  output : Array[@theory.TheoryItem],
) -> Unit raise TransformError {
  for data_constructor in constructors {
    let constructor = data_constructor.view().symbol
    let projections = complete_constructor_projections(state, data_constructor)
    let encoded_projections : Array[@logic.LSymbol] = []
    for index, projection in projections {
      // Why3 closes each projection axiom independently. Reopening those
      // closures for SMT printing therefore yields distinct binder
      // identifiers even though the source `vl` is shared by the OCaml loop.
      // Give each MoonBit axiom its own binders to preserve that observable
      // provenance identity.
      let variables : Array[@logic.VSymbol] = []
      for argument_type in constructor.view().argument_types {
        variables.push(algebraic_fresh_variable(state, b"u", argument_type))
      }
      let terms = variables.map(@logic.Term::variable)
      let head = algebraic_constructor_term(state, constructor, terms, ty)
      let (encoded, fresh) = match state.projections.get(projection) {
        Some(encoded) => (encoded, false)
        None => {
          let encoded = ordinary_clone(state, projection)
          state.projections[projection] = encoded
          (encoded, true)
        }
      }
      if fresh {
        output.push(algebraic_parameter_item(state, encoded))
      }
      let projected = algebraic_apply(encoded, [head], terms[index].ty())
      let body = algebraic_equality(state, projected, terms[index])
      let name = encoded.view().name + b"'def"
      output.push(
        algebraic_proposition_item(
          state,
          name,
          encoded.view().origin,
          algebraic_raw_forall(variables, [], body),
        ),
      )
      output.push(
        TheoryMeta(
          @theory.Meta::new(b"model_projection", [MetaLogicSymbol(encoded)]),
        ),
      )
      encoded_projections.push(encoded)
    }
    state.constructor_projections[constructor] = encoded_projections
  }
}

///|
fn add_inversion(
  state : AlgebraicState,
  type_symbol : @logic.TypeSymbol,
  ty : @logic.Ty,
  constructors : ArrayView[@logic.DataConstructor],
  output : Array[@theory.TheoryItem],
) -> Unit raise TransformError {
  if state.options.no_inversion {
    return
  }
  let variable = algebraic_fresh_variable(state, b"u", ty)
  let value = @logic.Term::variable(variable)
  let alternatives : Array[@logic.Term] = []
  for data_constructor in constructors {
    let constructor = data_constructor.view().symbol
    guard state.constructor_projections.get(constructor) is Some(projections) else {
      return fail_transform(
        InvariantFailure,
        @identity.EliminateAlgebraicIfPoly,
        "constructor has no completed projections",
      )
    }
    let arguments = projections.map(projection => {
      algebraic_projection_term(projection, value)
    })
    alternatives.push(
      algebraic_equality(
        state,
        value,
        algebraic_constructor_term(state, constructor, arguments, ty),
      ),
    )
  }
  guard !alternatives.is_empty() else {
    return fail_transform(
      InvariantFailure,
      @identity.EliminateAlgebraicIfPoly,
      "cannot invert an empty algebraic type",
    )
  }
  let mut body = alternatives[0]
  for index = 1; index < alternatives.length(); index = index + 1 {
    body = @logic.Term::binary(Or, body, alternatives[index], None) catch {
      _ =>
        return fail_transform(
          InvariantFailure,
          @identity.EliminateAlgebraicIfPoly,
          "cannot build an algebraic inversion",
        )
    }
  }
  output.push(
    algebraic_proposition_item(
      state,
      type_symbol.name().to_owned() + b"_inversion",
      type_symbol.origin(),
      algebraic_raw_forall([variable], [], body),
    ),
  )
}

///|
fn algebraic_record_without_recursion(data : @logic.DataDeclaration) -> Bool {
  let view = data.view()
  guard view.constructors is [constructor] &&
    !constructor.view().symbol.view().argument_types.is_empty() else {
    return false
  }
  let recursive : Map[@logic.TypeSymbol, Unit] = Map([(view.type_symbol, ())])
  constructor.view().symbol.view().argument_types.all(field => {
    !type_contains_one_of(field, recursive)
  })
}

///|
fn algebraic_kept_without_cases(
  state : AlgebraicState,
  data : @logic.DataDeclaration,
) -> Bool {
  let view = data.view()
  if state.options.keep_records && algebraic_record_without_recursion(data) {
    return true
  }
  state.options.keep_enums &&
  view.type_symbol.arity() == 0 &&
  view.constructors.all(constructor => {
    constructor.view().symbol.view().argument_types.is_empty()
  }) &&
  !state.kept.contains(view.type_symbol)
}

///|
fn add_kept_primitive_operations(
  state : AlgebraicState,
  data : @logic.DataDeclaration,
  output : Array[@theory.TheoryItem],
) -> Unit raise TransformError {
  let view = data.view()
  let ty = generic_data_type(view.type_symbol)
  for data_constructor in view.constructors {
    let constructor_view = data_constructor.view()
    state.constructors[constructor_view.symbol] = constructor_view.symbol
    let projections : Array[@logic.LSymbol] = []
    for projection in complete_constructor_projections(state, data_constructor) {
      state.projections[projection] = projection
      projections.push(projection)
    }
    state.constructor_projections[constructor_view.symbol] = projections
  }
  add_selector(state, view.type_symbol, ty, view.constructors, output)
}

///|
fn add_algebraic_axioms(
  state : AlgebraicState,
  data : @logic.DataDeclaration,
  output : Array[@theory.TheoryItem],
) -> Unit raise TransformError {
  let view = data.view()
  let ty = generic_data_type(view.type_symbol)
  if algebraic_kept_without_cases(state, data) {
    add_kept_primitive_operations(state, data, output)
    return
  }
  if view.type_symbol.arity() == 0 && state.kept.contains(view.type_symbol) {
    return
  }
  add_abstract_constructors(state, view.constructors, output)
  add_selector(state, view.type_symbol, ty, view.constructors, output)
  add_indexer(state, view.type_symbol, ty, view.constructors, output)
  add_projections(state, ty, view.constructors, output)
  add_inversion(state, view.type_symbol, ty, view.constructors, output)
}

///|
fn algebraic_group_data(
  declarations : ArrayView[@logic.DataDeclaration],
  symbol : @logic.TypeSymbol,
) -> @logic.DataDeclaration? {
  for data in declarations {
    if data.view().type_symbol == symbol {
      return Some(data)
    }
  }
  None
}

///|
fn algebraic_collect_material_type(
  state : AlgebraicState,
  declarations : ArrayView[@logic.DataDeclaration],
  ty : @logic.Ty,
  visiting : Map[@logic.TypeSymbol, Unit],
  variables : Map[@logic.TyVarSymbol, Unit],
) -> Bool {
  match ty.view() {
    TyVar(variable) => {
      variables[variable] = ()
      false
    }
    TyApp(symbol, arguments) => {
      if visiting.contains(symbol) {
        return true
      }
      let material = match state.material.get(symbol) {
        Some(material) => material
        None => {
          let (_, material, infinite) = algebraic_compute_material_arguments(
            state, declarations, symbol, visiting,
          )
          if infinite {
            return true
          }
          material
        }
      }
      for index, argument in arguments {
        if index < material.length() &&
          material[index] &&
          algebraic_collect_material_type(
            state, declarations, argument, visiting, variables,
          ) {
          return true
        }
      }
      false
    }
  }
}

///|
fn algebraic_compute_material_arguments(
  state : AlgebraicState,
  declarations : ArrayView[@logic.DataDeclaration],
  symbol : @logic.TypeSymbol,
  visiting : Map[@logic.TypeSymbol, Unit],
) -> (@logic.TypeSymbol, Array[Bool], Bool) {
  let nested = visiting.copy()
  nested[symbol] = ()
  let variables : Map[@logic.TyVarSymbol, Unit] = Map([])
  guard algebraic_group_data(declarations, symbol) is Some(data) else {
    return (symbol, [ for _ in symbol.view().parameters => false ], false)
  }
  for constructor in data.view().constructors {
    for field in constructor.view().symbol.view().argument_types {
      if algebraic_collect_material_type(
          state, declarations, field, nested, variables,
        ) {
        return (symbol, [ for _ in symbol.view().parameters => false ], true)
      }
    }
  }
  (
    symbol,
    symbol.view().parameters.map(variable => variables.contains(variable)),
    false,
  )
}

///|
fn add_algebraic_cardinality_tags(
  state : AlgebraicState,
  declarations : ArrayView[@logic.DataDeclaration],
  data : @logic.DataDeclaration,
  output : Array[@theory.TheoryItem],
) -> Unit raise TransformError {
  let symbol = data.view().type_symbol
  let (_, material, infinite) = algebraic_compute_material_arguments(
    state,
    declarations,
    symbol,
    state.infinite,
  )
  if infinite {
    state.infinite[symbol] = ()
    output.push(
      TheoryMeta(@theory.Meta::new(b"infinite_type", [MetaTypeSymbol(symbol)])),
    )
  } else {
    state.material[symbol] = material
    for index, is_material in material {
      if is_material {
        output.push(
          TheoryMeta(
            @theory.Meta::new(b"material_type_arg", [
              MetaTypeSymbol(symbol),
              MetaInteger(index.to_int64()),
            ]),
          ),
        )
      }
    }
  }
}

///|
fn process_algebraic_data(
  state : AlgebraicState,
  declaration : @logic.Decl,
  declarations : ArrayView[@logic.DataDeclaration],
  output : Array[@theory.TheoryItem],
) -> Unit raise TransformError {
  for data in declarations {
    let view = data.view()
    if view.type_symbol.arity() == 0 &&
      state.options.keep_monomorphic &&
      !algebraic_kept_without_cases(state, data) {
      add_kept_type(state, generic_data_type(view.type_symbol))
    }
  }
  let abstract : Array[@logic.DataDeclaration] = []
  let concrete : Array[@logic.DataDeclaration] = []
  for data in declarations {
    let view = data.view()
    if state.kept.contains(view.type_symbol) ||
      algebraic_kept_without_cases(state, data) {
      concrete.push(data)
    } else {
      abstract.push(data)
    }
  }
  for data in abstract {
    output.push(algebraic_type_item(state, data.view().type_symbol))
  }
  if !concrete.is_empty() {
    output.push(
      TheoryDecl(
        @logic.Decl::data(state.context, declaration.origin(), concrete, None) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              @identity.EliminateAlgebraicIfPoly,
              "cannot retain an algebraic data declaration",
            )
        },
      ),
    )
  }
  for data in declarations {
    add_algebraic_axioms(state, data, output)
    add_algebraic_cardinality_tags(state, declarations, data, output)
  }
}

///|
fn rewrite_algebraic_declaration(
  state : AlgebraicState,
  declaration : @logic.Decl,
) -> @logic.Decl raise TransformError {
  match declaration.view() {
    Dtype(_) | Dparam(_) => declaration
    Dlogic(definitions) => {
      let mapped : Array[@logic.LogicDefinition] = []
      for definition in definitions {
        let view = definition.view()
        mapped.push(
          @logic.LogicDefinition::new(
            state.context,
            view.symbol,
            view.parameters,
            algebraic_rewrite_any(state, view.body),
            None,
          ) catch {
            _ =>
              return fail_transform(
                InvariantFailure,
                @identity.EliminateAlgebraicIfPoly,
                "cannot rewrite an algebraic logic definition",
              )
          },
        )
      }
      @logic.Decl::logic(state.context, declaration.origin(), mapped, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.EliminateAlgebraicIfPoly,
            "cannot rebuild an algebraic logic declaration",
          )
      }
    }
    Dprop(kind, proposition, formula) => {
      let mapped = algebraic_rewrite_formula(state, Map([]), true, formula)
      // Why3 hash-conses non-goal declarations with strict term equality.
      // Returning the existing declaration here models the common no-op hit
      // without confusing alpha-equivalent terms that differ in locations or
      // attributes.
      if kind != Pgoal && mapped.strict_alpha_equivalent(formula) {
        return declaration
      }
      @logic.Decl::proposition(
        state.context,
        declaration.origin(),
        kind,
        proposition,
        mapped,
        None,
      ) catch {
        @logic.TypeError(diagnostic) =>
          fail_transform(
            InvariantFailure,
            @identity.EliminateAlgebraicIfPoly,
            "cannot rebuild an algebraic proposition: " + diagnostic.message,
          )
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.EliminateAlgebraicIfPoly,
            "cannot rebuild an algebraic proposition",
          )
      }
    }
    Ddata(_) =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateAlgebraicIfPoly,
        "data declaration reached the ordinary rewrite",
      )
    Dind(_, _) =>
      fail_transform(
        UnsupportedStructure,
        @identity.EliminateAlgebraicIfPoly,
        "inductive declaration survived eliminate_inductive",
      )
  }
}

///|
fn tuple_theory_key(key : @theory.TheoryKey) -> Bool {
  let view = key.view()
  view.path.length() >= 1 &&
  view.path[0] == b"why3" &&
  bytes_have_prefix(view.name, b"Tuple")
}

///|
fn algebraic_tuple_symbol(
  declarations : ArrayView[@logic.DataDeclaration],
) -> @logic.TypeSymbol? {
  guard declarations is [data] else { return None }
  let symbol = data.view().type_symbol
  if symbol
    .origin()
    .attributes()
    .any(attribute => attribute == b"why3:builtin:tuple-type") {
    Some(symbol)
  } else {
    None
  }
}

///|
fn algebraic_tuple_theory_name(arity : Int) -> Bytes {
  let output = @buffer.Buffer()
  output.write_bytes(b"Tuple")
  output.write_string_utf8(arity.to_string())
  output.to_bytes()
}

///|
fn algebraic_tuple_use_key(
  items : ArrayView[@theory.TheoryItem],
  symbol : @logic.TypeSymbol,
) -> @theory.TheoryKey raise TransformError {
  let name = algebraic_tuple_theory_name(symbol.arity())
  for item in items {
    if item is TheoryUse(key) &&
      tuple_theory_key(key) &&
      key.view().name == name {
      return key
    }
  }
  @theory.TheoryKey::new([b"why3", name], name) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateAlgebraicIfPoly,
        "cannot reconstruct a tuple theory key",
      )
  }
}

///|
fn deferred_tuple_declarations(
  items : ArrayView[@theory.TheoryItem],
) -> Array[DeferredTupleDeclaration] raise TransformError {
  let result : Array[DeferredTupleDeclaration] = []
  for item in items {
    guard item is TheoryDecl(declaration) &&
      declaration.view() is Ddata(declarations) &&
      algebraic_tuple_symbol(declarations) is Some(symbol) else {
      continue
    }
    result.push({
      symbol,
      declaration,
      data: declarations.to_owned(),
      use_key: algebraic_tuple_use_key(items, symbol),
    })
  }
  result.sort_by((left, right) => {
    left.symbol
    .semantic_id()
    .local_id()
    .compare(right.symbol.semantic_id().local_id())
  })
  result
}

///|
fn flush_used_tuple_declarations(
  state : AlgebraicState,
  deferred : ArrayView[DeferredTupleDeclaration],
  emitted : Map[@logic.TypeSymbol, Unit],
  declaration : @logic.Decl,
  output : Array[@theory.TheoryItem],
) -> Unit raise TransformError {
  for tuple in deferred {
    if emitted.contains(tuple.symbol) ||
      !declaration
      .dependencies()
      .any(dependency => dependency == @logic.TypeDependency(tuple.symbol)) {
      continue
    }
    process_algebraic_data(state, tuple.declaration, tuple.data, output)
    output.push(TheoryUse(tuple.use_key))
    emitted[tuple.symbol] = ()
  }
}

///|
fn rewrite_algebraic_meta_argument(
  state : AlgebraicState,
  argument : @theory.MetaArgument,
) -> @theory.MetaArgument {
  match argument {
    MetaLogicSymbol(symbol) =>
      match symbol.view().role {
        Constructor(_) =>
          match symbol.view().result_type {
            Some(ty) =>
              match ty.view() {
                TyApp(type_symbol, _) =>
                  if state.kept.contains(type_symbol) {
                    argument
                  } else {
                    match state.constructors.get(symbol) {
                      Some(replacement) => MetaLogicSymbol(replacement)
                      None => argument
                    }
                  }
                _ => argument
              }
            None => argument
          }
        Projection =>
          if symbol.view().argument_types.is_empty() {
            argument
          } else {
            match symbol.view().argument_types[0].view() {
              TyApp(type_symbol, _) =>
                if state.kept.contains(type_symbol) {
                  argument
                } else {
                  match state.projections.get(symbol) {
                    Some(replacement) => MetaLogicSymbol(replacement)
                    None => argument
                  }
                }
              _ => argument
            }
          }
        Ordinary => argument
      }
    _ => argument
  }
}

///|
fn rewrite_algebraic_meta(
  state : AlgebraicState,
  meta : @theory.Meta,
) -> @theory.Meta {
  let view = meta.view()
  let arguments = view.arguments.map(argument => {
    rewrite_algebraic_meta_argument(state, argument)
  })
  if view.exclusive {
    @theory.Meta::exclusive(view.name, arguments)
  } else {
    @theory.Meta::new(view.name, arguments)
  }
}

///|
fn existing_encoding_kept(
  items : ArrayView[@theory.TheoryItem],
) -> Array[@logic.Ty] {
  let result : Array[@logic.Ty] = []
  for item in items {
    guard item is TheoryMeta(meta) &&
      meta.view().name == b"encoding:kept" &&
      meta.view().arguments is [MetaType(ty)] else {
      continue
    }
    if !result.contains(ty) {
      result.push(ty)
    }
  }
  result
}

///|
fn find_task_equality(
  task : @theory.Task,
) -> (@logic.LSymbol, @theory.TheoryItem)? {
  for item in task.view().items {
    if item is TheoryDecl(declaration) &&
      declaration.view() is Dparam(symbol) &&
      is_builtin_equality(symbol) {
      return Some((symbol, item))
    }
  }
  None
}

///|
fn algebraic_known_map(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @logic.KnownMap raise TransformError {
  let mut known = @logic.KnownMap::new(context)
  for item in task.view().items {
    guard item is TheoryDecl(declaration) else { continue }
    known = known.add(declaration, None) catch {
      _ =>
        return fail_transform(
          InvalidTask,
          @identity.EliminateAlgebraicIfPoly,
          "cannot reconstruct the task known map",
        )
    }
  }
  known
}

///|
fn eliminate_algebraic_full(
  context : @identity.CompilationContext,
  task : @theory.Task,
  integer_symbol : @logic.TypeSymbol,
  real_symbol : @logic.TypeSymbol,
  string_symbol : @logic.TypeSymbol,
) -> @theory.Task raise TransformError {
  let stage = @identity.EliminateAlgebraicIfPoly
  let task = compile_match_task(context, task)
  let known = algebraic_known_map(context, task)
  guard find_task_equality(task) is Some((equality, equality_item)) else {
    return fail_transform(
      InvariantFailure,
      stage,
      "task has no builtin equality parameter",
    )
  }
  let integer_type = @logic.Ty::app(integer_symbol, [], None) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot construct the integer encoding type",
      )
  }
  let infinite = algebraic_infinite_types(task)
  infinite[integer_symbol] = ()
  infinite[real_symbol] = ()
  infinite[string_symbol] = ()
  let state : AlgebraicState = {
    context,
    known,
    equality,
    integer_type,
    options: algebraic_options(task),
    selectors: Map([]),
    constructors: Map([]),
    constructor_projections: Map([]),
    projections: Map([]),
    kept: Map([]),
    kept_order: [],
    infinite,
    material: algebraic_material_arguments(task),
  }
  for ty in tagged_algebraic_types(task) {
    add_kept_type(state, ty)
  }
  let input = task.view().items
  let deferred_tuples = deferred_tuple_declarations(input)
  let emitted_tuples : Map[@logic.TypeSymbol, Unit] = Map([])
  guard !input.is_empty() &&
    input[input.length() - 1] is TheoryDecl(goal) &&
    goal.view() is Dprop(Pgoal, _, _) else {
    return fail_transform(InvalidTask, stage, "task has no final goal")
  }
  let output : Array[@theory.TheoryItem] = [
    TheoryMeta(
      @theory.Meta::new(b"infinite_type", [MetaTypeSymbol(integer_symbol)]),
    ),
    TheoryMeta(
      @theory.Meta::new(b"infinite_type", [MetaTypeSymbol(real_symbol)]),
    ),
    TheoryMeta(
      @theory.Meta::new(b"infinite_type", [MetaTypeSymbol(string_symbol)]),
    ),
    equality_item,
  ]
  for index, item in input {
    if index + 1 == input.length() {
      continue
    }
    match item {
      TheoryDecl(declaration) =>
        match declaration.view() {
          Ddata(declarations) if algebraic_tuple_symbol(declarations) is Some(_) =>
            ()
          _ => {
            flush_used_tuple_declarations(
              state, deferred_tuples, emitted_tuples, declaration, output,
            )
            match declaration.view() {
              Dparam(symbol) if symbol == equality => ()
              Ddata(declarations) =>
                process_algebraic_data(state, declaration, declarations, output)
              _ =>
                output.push(
                  TheoryDecl(rewrite_algebraic_declaration(state, declaration)),
                )
            }
          }
        }
      TheoryUse(key) => if !tuple_theory_key(key) { output.push(item) }
      TheoryClone(_) => output.push(item)
      TheoryMeta(_) => output.push(item)
    }
  }
  flush_used_tuple_declarations(
    state, deferred_tuples, emitted_tuples, goal, output,
  )
  for index, item in output {
    if item is TheoryMeta(meta) {
      output[index] = TheoryMeta(rewrite_algebraic_meta(state, meta))
    }
  }
  let ordered_kept = ordered_algebraic_kept_types(state)
  for reverse_index = 0
      reverse_index < ordered_kept.length()
      reverse_index = reverse_index + 1 {
    let ty = ordered_kept[ordered_kept.length() - reverse_index - 1]
    let already_kept = output.any(item => {
      item is TheoryMeta(meta) &&
      meta.view()
      is { name: b"encoding:kept", arguments: [MetaType(existing)], .. } &&
      existing == ty
    })
    if !already_kept {
      mark_dynamic_encoding_kept(ty)
    }
    output.push(TheoryMeta(@theory.Meta::new(b"encoding:kept", [MetaType(ty)])))
  }
  output.push(TheoryDecl(rewrite_algebraic_declaration(state, goal)))
  checked_task(task, output, stage)
}

///|
pub fn eliminate_algebraic_if_poly(
  context : @identity.CompilationContext,
  task : @theory.Task,
  integer_type : @logic.TypeSymbol?,
  real_type : @logic.TypeSymbol?,
  string_type : @logic.TypeSymbol?,
) -> @theory.Task raise TransformError {
  let stage = @identity.EliminateAlgebraicIfPoly
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return eliminate_projections_sums(
      context,
      compile_match_task(context, task),
    )
  }
  eliminate_algebraic_full(
    context,
    task,
    required_builtin_type(integer_type, BuiltinInteger, stage),
    required_builtin_type(real_type, BuiltinReal, stage),
    required_builtin_type(string_type, BuiltinString, stage),
  )
}
