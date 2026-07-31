// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-29.

///|
priv enum EpsilonCanonical {
  EpsilonIdentity(@logic.Ty)
  EpsilonEta(@logic.Term)
  EpsilonPartial(@logic.LSymbol, Array[@logic.Term])
  EpsilonNotCanonical
}

///|
priv struct EpsilonBuiltins {
  equality : @logic.LSymbol?
  application : @logic.LSymbol?
  boolean_true : @logic.LSymbol?
  function_type : @logic.TypeSymbol?
}

///|
priv struct EpsilonState {
  context : @identity.CompilationContext
  builtins : EpsilonBuiltins
}

///|
priv struct EpsilonAccumulator {
  abstractions : Array[@logic.Decl]
  axioms : Array[@logic.Decl]
}

///|
priv struct EpsilonCanonicalEntry {
  parameter : @logic.Decl
  axiom : @logic.Decl
  symbol : @logic.LSymbol
}

///|
fn epsilon_fresh_origin(name : BytesView) -> @identity.Origin {
  @identity.Origin::generated(@identity.EliminateEpsilon, name, None, [])
}

///|
fn epsilon_derived_origin(
  name : BytesView,
  parent : @identity.Origin,
) -> @identity.Origin {
  derived_generated_origin(
    @identity.EliminateEpsilon,
    name,
    parent,
    derived_generated_attributes(parent),
  )
}

///|
fn is_highord_application(symbol : @logic.LSymbol) -> Bool {
  symbol.view().origin
  .attributes()
  .any(attribute => attribute == b"why3:builtin:function-application")
}

///|
fn is_boolean_true_symbol(symbol : @logic.LSymbol) -> Bool {
  symbol.view().origin
  .attributes()
  .any(attribute => attribute == b"why3:builtin:boolean:true")
}

///|
fn is_function_type_symbol(symbol : @logic.TypeSymbol) -> Bool {
  symbol
  .origin()
  .attributes()
  .any(attribute => attribute == b"why3:builtin:function-type")
}

///|
fn epsilon_record_builtin_symbol(
  symbol : @logic.LSymbol,
  equality : Ref[@logic.LSymbol?],
  application : Ref[@logic.LSymbol?],
  boolean_true : Ref[@logic.LSymbol?],
  function_type : Ref[@logic.TypeSymbol?],
) -> Unit {
  if equality.val is None && is_builtin_equality(symbol) {
    equality.val = Some(symbol)
  }
  if application.val is None && is_highord_application(symbol) {
    application.val = Some(symbol)
  }
  if boolean_true.val is None && is_boolean_true_symbol(symbol) {
    boolean_true.val = Some(symbol)
  }
  if function_type.val is None {
    for ty in symbol.view().argument_types {
      if ty.view() is TyApp(candidate, _) && is_function_type_symbol(candidate) {
        function_type.val = Some(candidate)
        break
      }
    }
    if symbol.view().result_type is Some(ty) &&
      ty.view() is TyApp(candidate, _) &&
      is_function_type_symbol(candidate) {
      function_type.val = Some(candidate)
    }
  }
}

///|
fn epsilon_builtins(task : @theory.Task) -> EpsilonBuiltins {
  let equality : Ref[@logic.LSymbol?] = Ref(None)
  let application : Ref[@logic.LSymbol?] = Ref(None)
  let boolean_true : Ref[@logic.LSymbol?] = Ref(None)
  let function_type : Ref[@logic.TypeSymbol?] = Ref(None)
  for item in task.view().items {
    guard item is TheoryDecl(declaration) else { continue }
    for dependency in declaration.dependencies() {
      if dependency is LogicDependency(symbol) {
        epsilon_record_builtin_symbol(
          symbol, equality, application, boolean_true, function_type,
        )
      }
    }
    for introduced in declaration.introduced_symbols() {
      if introduced is LogicDependency(symbol) {
        epsilon_record_builtin_symbol(
          symbol, equality, application, boolean_true, function_type,
        )
      }
    }
  }
  {
    equality: equality.val,
    application: application.val,
    boolean_true: boolean_true.val,
    function_type: function_type.val,
  }
}

///|
fn epsilon_required_equality(
  state : EpsilonState,
) -> @logic.LSymbol raise TransformError {
  match state.builtins.equality {
    Some(symbol) => symbol
    None =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateEpsilon,
        "task has no builtin equality symbol",
      )
  }
}

///|
fn epsilon_required_application(
  state : EpsilonState,
) -> @logic.LSymbol raise TransformError {
  match state.builtins.application {
    Some(symbol) => symbol
    None =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateEpsilon,
        "task has no builtin function-application symbol",
      )
  }
}

///|
fn epsilon_required_function_type(
  state : EpsilonState,
) -> @logic.TypeSymbol raise TransformError {
  match state.builtins.function_type {
    Some(symbol) => symbol
    None =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateEpsilon,
        "task has no builtin function type",
      )
  }
}

///|
fn epsilon_boolean_true(
  state : EpsilonState,
) -> @logic.Term raise TransformError {
  guard state.builtins.boolean_true is Some(symbol) else {
    return fail_transform(
      InvariantFailure,
      @identity.EliminateEpsilon,
      "task has no builtin boolean true symbol",
    )
  }
  @logic.Term::elaborated_apply(symbol, [], symbol.view().result_type, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateEpsilon,
        "cannot apply builtin boolean true",
      )
  }
}

///|
fn epsilon_function_type(
  state : EpsilonState,
  parameter : @logic.Ty,
  result : @logic.Ty,
) -> @logic.Ty raise TransformError {
  @logic.Ty::app(
    epsilon_required_function_type(state),
    [parameter, result],
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateEpsilon,
        "cannot construct a function type",
      )
  }
}

///|
fn epsilon_apply(
  symbol : @logic.LSymbol,
  arguments : ArrayView[@logic.Term],
  result : @logic.Ty?,
) -> @logic.Term raise TransformError {
  @logic.Term::elaborated_apply(symbol, arguments, result, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateEpsilon,
        "cannot apply a logic symbol",
      )
  }
}

///|
fn epsilon_equality(
  state : EpsilonState,
  left : @logic.Term,
  right : @logic.Term,
) -> @logic.Term raise TransformError {
  epsilon_apply(epsilon_required_equality(state), [left, right], None)
}

///|
fn epsilon_function_apply(
  state : EpsilonState,
  function_ : @logic.Term,
  argument : @logic.Term,
) -> @logic.Term raise TransformError {
  guard function_.ty() is Some(function_ty) &&
    function_ty.view() is TyApp(symbol, types) &&
    is_function_type_symbol(symbol) &&
    types.length() == 2 &&
    argument.ty() == Some(types[0]) else {
    return fail_transform(
      InvariantFailure,
      @identity.EliminateEpsilon,
      "invalid higher-order application",
    )
  }
  epsilon_apply(
    epsilon_required_application(state),
    [function_, argument],
    Some(types[1]),
  )
}

///|
fn epsilon_fresh_variable(
  state : EpsilonState,
  name : BytesView,
  ty : @logic.Ty,
) -> @logic.VSymbol raise TransformError {
  @logic.VSymbol::new(state.context, name, epsilon_fresh_origin(name), ty, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateEpsilon,
        "cannot create an epsilon axiom binder",
      )
  }
}

///|
fn epsilon_parameter(
  state : EpsilonState,
  symbol : @logic.LSymbol,
) -> @logic.Decl raise TransformError {
  @logic.Decl::parameter(state.context, symbol.view().origin, symbol, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateEpsilon,
        "cannot declare an epsilon abstraction",
      )
  }
}

///|
fn epsilon_axiom(
  state : EpsilonState,
  name : BytesView,
  origin : @identity.Origin,
  formula : @logic.Term,
) -> @logic.Decl raise TransformError {
  let proposition = @logic.PrSymbol::new(state.context, name, origin)
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
        @identity.EliminateEpsilon,
        "cannot declare an epsilon axiom",
      )
  }
}

///|
fn disjoint_from_binders(
  term : @logic.Term,
  binders : ArrayView[@logic.VSymbol],
) -> Bool {
  let forbidden : Map[@logic.VSymbol, Unit] = Map([])
  for binder in binders {
    forbidden[binder] = ()
  }
  term.free_variables().all(variable => !forbidden.contains(variable))
}

///|
fn epsilon_match_expression(
  term : @logic.Term,
  index : Int,
  reversed : ArrayView[@logic.VSymbol],
) -> EpsilonCanonical {
  if index == reversed.length() {
    return if disjoint_from_binders(term, reversed) {
      EpsilonEta(term)
    } else {
      EpsilonNotCanonical
    }
  }
  if index + 1 == reversed.length() &&
    term.view() is Tvar(found) &&
    found == reversed[index] {
    return EpsilonIdentity(found.view().ty)
  }
  match term.view() {
    Tapp(symbol, _, arguments) if is_highord_application(symbol) &&
      arguments.length() == 2 &&
      arguments[1].view() is Tvar(found) &&
      found == reversed[index] =>
      epsilon_match_expression(arguments[0], index + 1, reversed)
    Tapp(symbol, _, arguments) => {
      let remaining = reversed.length() - index
      if arguments.length() < remaining {
        return EpsilonNotCanonical
      }
      for offset = 0; offset < remaining; offset = offset + 1 {
        let argument = arguments[arguments.length() - offset - 1]
        if !(argument.view() is Tvar(found) && found == reversed[index + offset]) {
          return EpsilonNotCanonical
        }
      }
      let retained = arguments.length() - remaining
      for offset = 0; offset < retained; offset = offset + 1 {
        if !disjoint_from_binders(arguments[offset], reversed) {
          return EpsilonNotCanonical
        }
      }
      let reversed_arguments : Array[@logic.Term] = []
      for offset = 0; offset < retained; offset = offset + 1 {
        reversed_arguments.push(arguments[retained - offset - 1])
      }
      EpsilonPartial(symbol, reversed_arguments)
    }
    _ => EpsilonNotCanonical
  }
}

///|
fn epsilon_head_matches(
  term : @logic.Term,
  index : Int,
  reversed : ArrayView[@logic.VSymbol],
  variable : @logic.VSymbol,
) -> Bool {
  if index == reversed.length() {
    return term.view() is Tvar(found) && found == variable
  }
  match term.view() {
    Tapp(symbol, _, arguments) if is_highord_application(symbol) &&
      arguments.length() == 2 &&
      arguments[1].view() is Tvar(found) &&
      found == reversed[index] =>
      epsilon_head_matches(arguments[0], index + 1, reversed, variable)
    _ => false
  }
}

///|
fn canonicalize_epsilon(
  variable : @logic.VSymbol,
  formula : @logic.Term,
) -> EpsilonCanonical {
  let (binders, formula) = match formula.view() {
    Tquant(ForallQuantifier, binders, _, body) => (binders, body)
    _ => ([][:], formula)
  }
  let (head, expression) = match formula.view() {
    Tapp(symbol, _, arguments) if is_builtin_equality(symbol) &&
      arguments.length() == 2 => (arguments[0], arguments[1])
    Tbinop(Iff, left, right) => {
      guard left.view() is Tapp(symbol, _, arguments) &&
        is_builtin_equality(symbol) &&
        arguments.length() == 2 &&
        is_boolean_true_symbol_from_term(arguments[1]) else {
        return EpsilonNotCanonical
      }
      let expression = match right.view() {
        Tapp(right_symbol, _, right_arguments) if is_builtin_equality(
            right_symbol,
          ) &&
          right_arguments.length() == 2 &&
          is_boolean_true_symbol_from_term(right_arguments[1]) =>
          right_arguments[0]
        _ => right
      }
      (arguments[0], expression)
    }
    _ => return EpsilonNotCanonical
  }
  let reversed = [
    for index = 0; index < binders.length(); index = index + 1 => {
      binders[binders.length() - index - 1]
    }
  ]
  let canonical = epsilon_match_expression(expression, 0, reversed)
  if canonical is EpsilonNotCanonical ||
    !epsilon_head_matches(head, 0, reversed, variable) {
    EpsilonNotCanonical
  } else {
    canonical
  }
}

///|
fn is_boolean_true_symbol_from_term(term : @logic.Term) -> Bool {
  term.view() is Tapp(symbol, _, arguments) &&
  arguments.is_empty() &&
  is_boolean_true_symbol(symbol)
}

///|
fn open_epsilon_binder(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  body : @logic.Term,
) -> (@logic.VSymbol, @logic.Term) raise TransformError {
  let stage = @identity.EliminateEpsilon
  let opened = variable.clone_identifier(context, None) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot open epsilon binder",
      )
  }
  let values : Map[@logic.VSymbol, @logic.Term] = Map([])
  values[variable] = @logic.Term::variable(opened)
  let body = instantiate_term(
    context,
    @logic.TySubstitution::new(),
    values,
    body,
    stage,
    None,
  )
  (opened, body)
}

///|
fn open_epsilon_binders(
  context : @identity.CompilationContext,
  binders : ArrayView[@logic.VSymbol],
  triggers : ArrayView[Array[@logic.Term]],
  body : @logic.Term,
) -> (Array[@logic.VSymbol], Array[Array[@logic.Term]], @logic.Term) raise TransformError {
  let stage = @identity.EliminateEpsilon
  let opened : Array[@logic.VSymbol] = []
  let values : Map[@logic.VSymbol, @logic.Term] = Map([])
  for binder in binders {
    let replacement = binder.clone_identifier(context, None) catch {
      _ =>
        return fail_transform(
          InvariantFailure,
          stage,
          "cannot open quantified binder",
        )
    }
    opened.push(replacement)
    values[binder] = @logic.Term::variable(replacement)
  }
  let substitution = @logic.TySubstitution::new()
  let opened_triggers = [
    for group in triggers => {
      [
        for trigger in group => {
          instantiate_term(context, substitution, values, trigger, stage, None)
        }
      ]
    }
  ]
  let opened_body = instantiate_term(
    context,
    substitution,
    values,
    body,
    stage,
    None,
  )
  (opened, opened_triggers, opened_body)
}

///|
fn open_epsilon_pattern(
  context : @identity.CompilationContext,
  pattern : @logic.Pattern,
  body : @logic.Term,
) -> (@logic.Pattern, @logic.Term) raise TransformError {
  let stage = @identity.EliminateEpsilon
  let values : Map[@logic.VSymbol, @logic.Term] = Map([])
  for variable in pattern.bound_variables() {
    let replacement = variable.clone_identifier(context, None) catch {
      _ =>
        return fail_transform(
          InvariantFailure,
          stage,
          "cannot open case-pattern binder",
        )
    }
    values[variable] = @logic.Term::variable(replacement)
  }
  let substitution = @logic.TySubstitution::new()
  (
    instantiate_pattern(substitution, values, pattern, stage),
    instantiate_term(context, substitution, values, body, stage, None),
  )
}

///|
fn epsilon_substitute_one(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  replacement : @logic.Term,
  body : @logic.Term,
) -> @logic.Term raise TransformError {
  let values : Map[@logic.VSymbol, @logic.Term] = Map([])
  values[variable] = replacement
  instantiate_term(
    context,
    @logic.TySubstitution::new(),
    values,
    body,
    @identity.EliminateEpsilon,
    None,
  )
}

///|
fn epsilon_let_simplified(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  value : @logic.Term,
  body : @logic.Term,
) -> @logic.Term raise TransformError {
  let stage = @identity.EliminateEpsilon
  let occurrences = variable_occurrences(body, variable)
  if occurrences == 0 {
    return body
  }
  if occurrences == 1 || small_term(value) {
    return epsilon_substitute_one(context, variable, value, body)
  }
  @logic.Term::let_in(variable, value, body, None) catch {
    _ => fail_transform(InvariantFailure, stage, "invalid epsilon let")
  }
}

///|
fn epsilon_forall_close_merge(
  state : EpsilonState,
  prefix : ArrayView[@logic.VSymbol],
  formula : @logic.Term,
) -> @logic.Term raise TransformError {
  let stage = @identity.EliminateEpsilon
  match formula.view() {
    Tquant(ForallQuantifier, binders, triggers, body) => {
      let (opened, triggers, body) = open_epsilon_binders(
        state.context,
        binders,
        triggers,
        body,
      )
      let all = prefix.to_owned()
      all.push_iter(opened.iter())
      @logic.Term::quantify(ForallQuantifier, all, triggers, body, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot merge universal quantifiers",
          )
      }
    }
    _ =>
      @logic.Term::quantify(ForallQuantifier, prefix, [], formula, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot close an epsilon axiom",
          )
      }
  }
}

///|
let epsilon_closure_cache : Ref[Map[@logic.LSymbol, EpsilonCanonicalEntry]] = Ref(
  Map([]),
)

///|
let epsilon_identity_cache : Ref[Map[@logic.Ty, EpsilonCanonicalEntry]] = Ref(
  Map([]),
)

///|
let epsilon_polymorphic_identity_cache : Ref[
  Map[@logic.TypeSymbol, EpsilonCanonicalEntry],
] = Ref(Map([]))

///|
fn create_epsilon_identity(
  state : EpsilonState,
  ty : @logic.Ty,
) -> EpsilonCanonicalEntry raise TransformError {
  let stage = @identity.EliminateEpsilon
  let function_ty = epsilon_function_type(state, ty, ty)
  let symbol_origin = epsilon_fresh_origin(b"identity")
  let symbol = @logic.LSymbol::new_function(
    state.context,
    b"identity",
    symbol_origin,
    [],
    function_ty,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot create identity closure",
      )
  }
  let variable = epsilon_fresh_variable(state, b"y", ty)
  let identity = epsilon_apply(symbol, [], Some(function_ty))
  let applied = epsilon_function_apply(
    state,
    identity,
    @logic.Term::variable(variable),
  )
  let formula = epsilon_equality(
    state,
    applied,
    @logic.Term::variable(variable),
  )
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    [variable],
    [],
    formula,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot close identity axiom",
      )
  }
  let axiom_origin = epsilon_fresh_origin(b"identity_def")
  {
    parameter: epsilon_parameter(state, symbol),
    axiom: epsilon_axiom(state, b"identity_def", axiom_origin, formula),
    symbol,
  }
}

///|
fn epsilon_identity_entry(
  state : EpsilonState,
  ty : @logic.Ty,
) -> EpsilonCanonicalEntry raise TransformError {
  if ty.is_closed() {
    let cache = epsilon_identity_cache.val
    match cache.get(ty) {
      Some(entry) => entry
      None => {
        let entry = create_epsilon_identity(state, ty)
        cache[ty] = entry
        epsilon_identity_cache.val = cache
        entry
      }
    }
  } else {
    let function_type = epsilon_required_function_type(state)
    let cache = epsilon_polymorphic_identity_cache.val
    match cache.get(function_type) {
      Some(entry) => entry
      None => {
        let variable = @logic.TyVarSymbol::new(
          state.context,
          b"a",
          epsilon_fresh_origin(b"a"),
        )
        let entry = create_epsilon_identity(
          state,
          @logic.Ty::variable(variable),
        )
        cache[function_type] = entry
        epsilon_polymorphic_identity_cache.val = cache
        entry
      }
    }
  }
}

///|
fn create_epsilon_closure(
  state : EpsilonState,
  source : @logic.LSymbol,
) -> EpsilonCanonicalEntry raise TransformError {
  let stage = @identity.EliminateEpsilon
  let view = source.view()
  let result = match view.result_type {
    Some(result) => result
    None => {
      guard epsilon_boolean_true(state).ty() is Some(result) else {
        return fail_transform(
          InvariantFailure,
          stage,
          "builtin boolean true has no value type",
        )
      }
      result
    }
  }
  let mut closure_ty = result
  let mut index = view.argument_types.length()
  while index > 0 {
    index = index - 1
    closure_ty = epsilon_function_type(
      state,
      view.argument_types[index],
      closure_ty,
    )
  }
  let closure_name = view.name + b"_closure"
  let closure_origin = epsilon_derived_origin(closure_name, view.origin)
  let closure = @logic.LSymbol::new_function(
    state.context,
    closure_name,
    closure_origin,
    [],
    closure_ty,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot create a canonical closure",
      )
  }
  let variables : Array[@logic.VSymbol] = []
  for ty in view.argument_types {
    variables.push(epsilon_fresh_variable(state, b"y", ty))
  }
  let arguments = [
    for variable in variables => @logic.Term::variable(variable)
  ]
  let mut applied = epsilon_apply(closure, [], Some(closure_ty))
  for argument in arguments {
    applied = epsilon_function_apply(state, applied, argument)
  }
  let source_term = epsilon_apply(source, arguments, view.result_type)
  let relation = match view.result_type {
    Some(_) => epsilon_equality(state, applied, source_term)
    None => {
      let equality = epsilon_equality(
        state,
        applied,
        epsilon_boolean_true(state),
      )
      @logic.Term::binary(Iff, equality, source_term, None) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot create predicate closure axiom",
          )
      }
    }
  }
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    variables,
    [],
    relation,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot close canonical closure axiom",
      )
  }
  let axiom_name = view.name + b"_closure_def"
  let axiom_origin = epsilon_derived_origin(axiom_name, view.origin)
  {
    parameter: epsilon_parameter(state, closure),
    axiom: epsilon_axiom(state, axiom_name, axiom_origin, formula),
    symbol: closure,
  }
}

///|
fn epsilon_closure_entry(
  state : EpsilonState,
  symbol : @logic.LSymbol,
) -> EpsilonCanonicalEntry raise TransformError {
  let cache = epsilon_closure_cache.val
  match cache.get(symbol) {
    Some(entry) => entry
    None => {
      let entry = create_epsilon_closure(state, symbol)
      cache[symbol] = entry
      epsilon_closure_cache.val = cache
      entry
    }
  }
}

///|
fn append_epsilon_canonical_entry(
  accumulator : EpsilonAccumulator,
  entry : EpsilonCanonicalEntry,
) -> Unit {
  accumulator.abstractions.push(entry.parameter)
  accumulator.axioms.push(entry.axiom)
}

///|
fn ordered_epsilon_free_variables(term : @logic.Term) -> Array[@logic.VSymbol] {
  let variables = term.free_variables()
  variables.sort_by((left, right) => {
    left.semantic_id().local_id().compare(right.semantic_id().local_id())
  })
  variables
}

///|
fn eliminate_epsilon_equality_side(
  state : EpsilonState,
  accumulator : EpsilonAccumulator,
  source : @logic.Term,
  other : @logic.Term,
  epsilon : @logic.Term,
) -> (@logic.Term, Bool)? raise TransformError {
  guard epsilon.view() is Teps(variable, formula) else { return None }
  let (variable, formula) = open_epsilon_binder(
    state.context,
    variable,
    formula,
  )
  match canonicalize_epsilon(variable, formula) {
    EpsilonNotCanonical => {
      let substituted = epsilon_let_simplified(
        state.context,
        variable,
        other,
        formula,
      )
      let decorated = copy_term_decoration(source, substituted)
      let (result, _) = eliminate_epsilon_term_changed(
        state, accumulator, decorated,
      )
      Some((result, true))
    }
    _ => {
      guard other.view() is Teps(other_variable, other_formula) else {
        return None
      }
      let (other_variable, other_formula) = open_epsilon_binder(
        state.context,
        other_variable,
        other_formula,
      )
      match canonicalize_epsilon(other_variable, other_formula) {
        EpsilonNotCanonical => {
          let substituted = epsilon_let_simplified(
            state.context,
            other_variable,
            epsilon,
            other_formula,
          )
          let decorated = copy_term_decoration(source, substituted)
          let (result, _) = eliminate_epsilon_term_changed(
            state, accumulator, decorated,
          )
          Some((result, true))
        }
        _ => None
      }
    }
  }
}

///|
fn eliminate_epsilon_standalone(
  state : EpsilonState,
  accumulator : EpsilonAccumulator,
  source : @logic.Term,
  original_variable : @logic.VSymbol,
  original_formula : @logic.Term,
) -> (@logic.Term, Bool) raise TransformError {
  let stage = @identity.EliminateEpsilon
  let free_variables = ordered_epsilon_free_variables(source)
  let (variable, formula) = open_epsilon_binder(
    state.context,
    original_variable,
    original_formula,
  )
  match canonicalize_epsilon(variable, formula) {
    EpsilonIdentity(ty) => {
      let entry = epsilon_identity_entry(state, ty)
      append_epsilon_canonical_entry(accumulator, entry)
      let replacement = epsilon_apply(
        entry.symbol,
        [],
        Some(variable.view().ty),
      )
      (copy_term_decoration(source, replacement), true)
    }
    EpsilonEta(term) => {
      let (replacement, _) = eliminate_epsilon_term_changed(
        state, accumulator, term,
      )
      (copy_term_decoration(source, replacement), true)
    }
    EpsilonPartial(symbol, reversed_arguments) => {
      let entry = epsilon_closure_entry(state, symbol)
      let mapped_reversed : Array[@logic.Term] = []
      let mut closure_ty = variable.view().ty
      for argument in reversed_arguments {
        let (argument, _) = eliminate_epsilon_term_changed(
          state, accumulator, argument,
        )
        guard argument.ty() is Some(argument_ty) else {
          return fail_transform(
            InvariantFailure,
            stage,
            "partial closure argument is a formula",
          )
        }
        mapped_reversed.push(argument)
        closure_ty = epsilon_function_type(state, argument_ty, closure_ty)
      }
      append_epsilon_canonical_entry(accumulator, entry)
      let mut replacement = epsilon_apply(entry.symbol, [], Some(closure_ty))
      let mut index = mapped_reversed.length()
      while index > 0 {
        index = index - 1
        replacement = epsilon_function_apply(
          state,
          replacement,
          mapped_reversed[index],
        )
      }
      (copy_term_decoration(source, replacement), true)
    }
    EpsilonNotCanonical => {
      let (formula, _) = eliminate_epsilon_term_changed(
        state, accumulator, formula,
      )
      let view = variable.view()
      let argument_types = [ for free in free_variables => free.view().ty ]
      let origin = epsilon_derived_origin(view.name, view.origin)
      let symbol = @logic.LSymbol::new_function(
        state.context,
        view.name,
        origin,
        argument_types,
        view.ty,
        None,
      ) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot create an epsilon witness",
          )
      }
      let arguments = [
        for free in free_variables => @logic.Term::variable(free)
      ]
      let witness = epsilon_apply(symbol, arguments, Some(view.ty))
      let substituted = epsilon_substitute_one(
        state.context,
        variable,
        witness,
        formula,
      )
      let axiom_formula = epsilon_forall_close_merge(
        state, free_variables, substituted,
      )
      let axiom_name = view.name + b"'def"
      let axiom_origin = epsilon_derived_origin(axiom_name, view.origin)
      accumulator.abstractions.push(epsilon_parameter(state, symbol))
      accumulator.axioms.push(
        epsilon_axiom(state, axiom_name, axiom_origin, axiom_formula),
      )
      (copy_term_decoration(source, witness), true)
    }
  }
}

///|
fn eliminate_epsilon_term_changed(
  state : EpsilonState,
  accumulator : EpsilonAccumulator,
  term : @logic.Term,
) -> (@logic.Term, Bool) raise TransformError {
  let stage = @identity.EliminateEpsilon
  match term.view() {
    Tapp(symbol, _, arguments) if is_builtin_equality(symbol) &&
      arguments.length() == 2 =>
      match
        eliminate_epsilon_equality_side(
          state,
          accumulator,
          term,
          arguments[0],
          arguments[1],
        ) {
        Some(result) => result
        None =>
          match
            eliminate_epsilon_equality_side(
              state,
              accumulator,
              term,
              arguments[1],
              arguments[0],
            ) {
            Some(result) => result
            None => {
              let mapped : Array[@logic.Term] = []
              let mut changed = false
              for argument in arguments {
                let (argument, argument_changed) = eliminate_epsilon_term_changed(
                  state, accumulator, argument,
                )
                mapped.push(argument)
                changed = changed || argument_changed
              }
              if !changed {
                (term, false)
              } else {
                let replacement = epsilon_apply(symbol, mapped, term.ty())
                (copy_term_decoration(term, replacement), true)
              }
            }
          }
      }
    Teps(variable, formula) =>
      eliminate_epsilon_standalone(state, accumulator, term, variable, formula)
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => (term, false)
    Tapp(symbol, _, arguments) => {
      let mapped : Array[@logic.Term] = []
      let mut changed = false
      for argument in arguments {
        let (argument, argument_changed) = eliminate_epsilon_term_changed(
          state, accumulator, argument,
        )
        mapped.push(argument)
        changed = changed || argument_changed
      }
      if !changed {
        (term, false)
      } else {
        let replacement = epsilon_apply(symbol, mapped, term.ty())
        (copy_term_decoration(term, replacement), true)
      }
    }
    Tif(condition, then_branch, else_branch) => {
      let (condition, condition_changed) = eliminate_epsilon_term_changed(
        state, accumulator, condition,
      )
      let (then_branch, then_changed) = eliminate_epsilon_term_changed(
        state, accumulator, then_branch,
      )
      let (else_branch, else_changed) = eliminate_epsilon_term_changed(
        state, accumulator, else_branch,
      )
      if !(condition_changed || then_changed || else_changed) {
        (term, false)
      } else {
        let replacement = @logic.Term::if_then_else(
          condition,
          then_branch,
          else_branch,
          None,
        ) catch {
          _ => fail_transform(InvariantFailure, stage, "invalid mapped if")
        }
        (copy_term_decoration(term, replacement), true)
      }
    }
    Tlet(variable, value, body) => {
      let (value, value_changed) = eliminate_epsilon_term_changed(
        state, accumulator, value,
      )
      let (opened_variable, opened_body) = open_epsilon_binder(
        state.context,
        variable,
        body,
      )
      let (body, body_changed) = eliminate_epsilon_term_changed(
        state, accumulator, opened_body,
      )
      if !(value_changed || body_changed) {
        (term, false)
      } else {
        let replacement = if body_changed {
          @logic.Term::let_in(opened_variable, value, body, None) catch {
            _ => fail_transform(InvariantFailure, stage, "invalid mapped let")
          }
        } else {
          @logic.Term::let_in(variable, value, body, None) catch {
            _ =>
              fail_transform(
                InvariantFailure,
                stage,
                "invalid mapped let value",
              )
          }
        }
        (copy_term_decoration(term, replacement), true)
      }
    }
    Tcase(scrutinee, branches) => {
      let (scrutinee, scrutinee_changed) = eliminate_epsilon_term_changed(
        state, accumulator, scrutinee,
      )
      let mapped : Array[(@logic.Pattern, @logic.Term)] = []
      let mut branch_changed = false
      for branch in branches {
        let view = branch.view()
        let (opened_pattern, opened_body) = open_epsilon_pattern(
          state.context,
          view.pattern,
          view.body,
        )
        let (body, changed) = eliminate_epsilon_term_changed(
          state, accumulator, opened_body,
        )
        if changed {
          mapped.push((opened_pattern, body))
          branch_changed = true
        } else {
          mapped.push((view.pattern, view.body))
        }
      }
      if !(scrutinee_changed || branch_changed) {
        (term, false)
      } else {
        let replacement = @logic.Term::case(scrutinee, mapped, None) catch {
          _ => fail_transform(InvariantFailure, stage, "invalid mapped case")
        }
        (copy_term_decoration(term, replacement), true)
      }
    }
    Tquant(quantifier, binders, triggers, body) => {
      let (opened_binders, opened_triggers, opened_body) = open_epsilon_binders(
        state.context,
        binders,
        triggers,
        body,
      )
      let mapped_triggers : Array[Array[@logic.Term]] = []
      let mut changed = false
      for group in opened_triggers {
        let mapped_group : Array[@logic.Term] = []
        for trigger in group {
          let (trigger, trigger_changed) = eliminate_epsilon_term_changed(
            state, accumulator, trigger,
          )
          mapped_group.push(trigger)
          changed = changed || trigger_changed
        }
        mapped_triggers.push(mapped_group)
      }
      let (body, body_changed) = eliminate_epsilon_term_changed(
        state, accumulator, opened_body,
      )
      changed = changed || body_changed
      if !changed {
        (term, false)
      } else {
        let replacement = @logic.Term::quantify(
          quantifier,
          opened_binders,
          mapped_triggers,
          body,
          None,
        ) catch {
          _ =>
            fail_transform(InvariantFailure, stage, "invalid mapped quantifier")
        }
        (copy_term_decoration(term, replacement), true)
      }
    }
    Tbinop(operator, left, right) => {
      let (left, left_changed) = eliminate_epsilon_term_changed(
        state, accumulator, left,
      )
      let (right, right_changed) = eliminate_epsilon_term_changed(
        state, accumulator, right,
      )
      if !(left_changed || right_changed) {
        (term, false)
      } else {
        let replacement = @logic.Term::binary(operator, left, right, None) catch {
          _ =>
            fail_transform(
              InvariantFailure,
              stage,
              "invalid mapped binary term",
            )
        }
        (copy_term_decoration(term, replacement), true)
      }
    }
    Tnot(inner) => {
      let (inner, changed) = eliminate_epsilon_term_changed(
        state, accumulator, inner,
      )
      if !changed {
        (term, false)
      } else {
        let replacement = @logic.Term::not(inner, None) catch {
          _ =>
            fail_transform(InvariantFailure, stage, "invalid mapped negation")
        }
        (copy_term_decoration(term, replacement), true)
      }
    }
  }
}

///|
fn epsilon_definition_head(
  state : EpsilonState,
  symbol : @logic.LSymbol,
  parameters : ArrayView[@logic.VSymbol],
  result : @logic.Ty?,
) -> @logic.Term raise TransformError {
  epsilon_apply(
    symbol,
    [
      for parameter in parameters => @logic.Term::variable(parameter)
    ],
    result,
  )
}

///|
fn eliminate_epsilon_definition(
  state : EpsilonState,
  accumulator : EpsilonAccumulator,
  definition : @logic.LogicDefinition,
) -> (@logic.LogicDefinition?, Bool) raise TransformError {
  let stage = @identity.EliminateEpsilon
  let view = definition.view()
  let (parameters, _, opened_body) = open_epsilon_binders(
    state.context,
    view.parameters,
    [],
    view.body,
  )
  match opened_body.view() {
    Teps(variable, formula) => {
      let (variable, formula) = open_epsilon_binder(
        state.context,
        variable,
        formula,
      )
      let (formula, _) = eliminate_epsilon_term_changed(
        state, accumulator, formula,
      )
      let head = epsilon_definition_head(
        state,
        view.symbol,
        parameters,
        opened_body.ty(),
      )
      let formula = epsilon_substitute_one(
        state.context,
        variable,
        head,
        formula,
      )
      let formula = epsilon_forall_close_merge(state, parameters, formula)
      let symbol_view = view.symbol.view()
      let name = symbol_view.name + b"'def"
      let origin = epsilon_derived_origin(name, symbol_view.origin)
      accumulator.abstractions.push(epsilon_parameter(state, view.symbol))
      accumulator.axioms.push(epsilon_axiom(state, name, origin, formula))
      (None, true)
    }
    _ => {
      let (body, changed) = eliminate_epsilon_term_changed(
        state, accumulator, opened_body,
      )
      if !changed {
        (Some(definition), false)
      } else {
        (
          Some(
            @logic.LogicDefinition::new(
              state.context,
              view.symbol,
              parameters,
              body,
              None,
            ) catch {
              _ =>
                fail_transform(
                  InvariantFailure,
                  stage,
                  "invalid epsilon definition",
                )
            },
          ),
          true,
        )
      }
    }
  }
}

///|
fn epsilon_axiom_depends_on_definitions(
  axiom : @logic.Decl,
  definitions : ArrayView[@logic.LogicDefinition],
) -> Bool {
  let symbols : Map[@identity.SemanticId, Unit] = Map([])
  for definition in definitions {
    symbols[definition.view().symbol.semantic_id()] = ()
  }
  axiom
  .dependencies()
  .any(dependency => symbols.contains(dependency.semantic_id()))
}

///|
fn eliminate_epsilon_logic_declaration(
  state : EpsilonState,
  declaration : @logic.Decl,
  definitions : ArrayView[@logic.LogicDefinition],
) -> Array[@theory.TheoryItem] raise TransformError {
  let stage = @identity.EliminateEpsilon
  let accumulator = { abstractions: [], axioms: [] }
  let retained : Array[@logic.LogicDefinition] = []
  let mut changed = false
  for definition in definitions {
    let (mapped, definition_changed) = eliminate_epsilon_definition(
      state, accumulator, definition,
    )
    changed = changed || definition_changed
    if mapped is Some(mapped) {
      retained.push(mapped)
    }
  }
  if !changed {
    return [TheoryDecl(declaration)]
  }
  let result : Array[@theory.TheoryItem] = []
  for abstraction in accumulator.abstractions {
    result.push(TheoryDecl(abstraction))
  }
  if retained.is_empty() {
    for axiom in accumulator.axioms {
      result.push(TheoryDecl(axiom))
    }
    return result
  }
  let independent : Array[@logic.Decl] = []
  let dependent : Array[@logic.Decl] = []
  for axiom in accumulator.axioms {
    if epsilon_axiom_depends_on_definitions(axiom, retained) {
      dependent.push(axiom)
    } else {
      independent.push(axiom)
    }
  }
  for axiom in independent {
    result.push(TheoryDecl(axiom))
  }
  result.push(
    TheoryDecl(
      @logic.Decl::logic(state.context, declaration.origin(), retained, None) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "invalid epsilon logic group")
      },
    ),
  )
  for axiom in dependent {
    result.push(TheoryDecl(axiom))
  }
  result
}

///|
fn eliminate_epsilon_plain_declaration(
  state : EpsilonState,
  declaration : @logic.Decl,
) -> Array[@theory.TheoryItem] raise TransformError {
  let stage = @identity.EliminateEpsilon
  let accumulator = { abstractions: [], axioms: [] }
  let (transformed, changed) = match declaration.view() {
    Dtype(_) | Ddata(_) | Dparam(_) => (declaration, false)
    Dind(_, _) =>
      return fail_transform(
        UnsupportedStructure,
        stage,
        "inductive declaration survived its slot",
      )
    Dlogic(_) =>
      return fail_transform(
        InvariantFailure,
        stage,
        "logic declaration used the plain epsilon path",
      )
    Dprop(kind, proposition, formula) => {
      let (formula, changed) = eliminate_epsilon_term_changed(
        state, accumulator, formula,
      )
      if !changed {
        (declaration, false)
      } else {
        (
          @logic.Decl::proposition(
            state.context,
            declaration.origin(),
            kind,
            proposition,
            formula,
            None,
          ) catch {
            _ =>
              fail_transform(
                InvariantFailure,
                stage,
                "invalid epsilon proposition",
              )
          },
          true,
        )
      }
    }
  }
  if accumulator.abstractions.is_empty() &&
    accumulator.axioms.is_empty() &&
    !changed {
    return [TheoryDecl(declaration)]
  }
  let result : Array[@theory.TheoryItem] = []
  for abstraction in accumulator.abstractions {
    result.push(TheoryDecl(abstraction))
  }
  for axiom in accumulator.axioms {
    result.push(TheoryDecl(axiom))
  }
  result.push(TheoryDecl(transformed))
  result
}

///|
priv struct EliminateEpsilonCacheEntry {
  output : Array[@theory.TheoryItem]
  generation : Int64
  persistent : Bool
}

///|
let eliminate_epsilon_cache : Ref[
  Map[@identity.DeclarationId, EliminateEpsilonCacheEntry],
] = Ref(Map([]))

///|
fn eliminate_epsilon_declaration_uncached(
  state : EpsilonState,
  declaration : @logic.Decl,
) -> Array[@theory.TheoryItem] raise TransformError {
  match declaration.view() {
    Dlogic(definitions) =>
      eliminate_epsilon_logic_declaration(state, declaration, definitions)
    _ => eliminate_epsilon_plain_declaration(state, declaration)
  }
}

///|
fn eliminate_epsilon_declaration(
  state : EpsilonState,
  declaration : @logic.Decl,
) -> Array[@theory.TheoryItem] raise TransformError {
  if declaration.view() is Dprop(Pgoal, _, _) {
    return eliminate_epsilon_declaration_uncached(state, declaration)
  }
  let generation = current_declaration_cache_generation()
  let persistent = declaration_cache_is_persistent(declaration)
  let cache = eliminate_epsilon_cache.val
  match cache.get(declaration.declaration_id()) {
    Some(entry) =>
      if (entry.persistent && persistent) ||
        (!entry.persistent && !persistent && entry.generation == generation) {
        return entry.output
      }
    None => ()
  }
  let output = eliminate_epsilon_declaration_uncached(state, declaration)
  if persistent {
    for item in output {
      if item is TheoryDecl(output_declaration) {
        declaration_cache_retain(output_declaration)
      }
    }
  }
  cache[declaration.declaration_id()] = { output, generation, persistent }
  eliminate_epsilon_cache.val = cache
  output
}

///|
pub fn eliminate_epsilon(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.EliminateEpsilon
  require_task_context(context, task, stage)
  let state = { context, builtins: epsilon_builtins(task) }
  let items : Array[@theory.TheoryItem] = []
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) =>
        for mapped in eliminate_epsilon_declaration(state, declaration) {
          items.push(mapped)
        }
      TheoryUse(_) | TheoryClone(_) | TheoryMeta(_) => items.push(item)
    }
  }
  checked_task(task, items, stage)
}
