// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
let monomorphised_goal_type_cache : Ref[
  Map[@logic.TyVarSymbol, @logic.TypeSymbol],
] = Ref(Map([]))

///|
let monomorphised_goal_type_sources : Ref[
  Map[@logic.TypeSymbol, @logic.TyVarSymbol],
] = Ref(Map([]))

///|
fn monomorphised_goal_type_source(
  symbol : @logic.TypeSymbol,
) -> @logic.TyVarSymbol? {
  monomorphised_goal_type_sources.val.get(symbol)
}

///|
fn monomorphised_goal_type(
  context : @identity.CompilationContext,
  variable : @logic.TyVarSymbol,
) -> (@logic.TypeSymbol, @logic.Ty) raise TransformError {
  let stage = @identity.DiscriminateMonomorphiseGoal
  match monomorphised_goal_type_cache.val.get(variable) {
    Some(symbol) => {
      let ty = @logic.Ty::app(symbol, [], None) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot apply a cached goal type constant",
          )
      }
      return (symbol, ty)
    }
    None => ()
  }
  let name = variable.name()
  let origin = @identity.Origin::generated(
    stage,
    name,
    None,
    variable.origin().attributes(),
  )
  let symbol = @logic.TypeSymbol::new_abstract(context, name, origin, [], None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot create a goal type constant",
      )
  }
  let ty = @logic.Ty::app(symbol, [], None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot apply a goal type constant",
      )
  }
  monomorphised_goal_type_cache.val[variable] = symbol
  monomorphised_goal_type_sources.val[symbol] = variable
  (symbol, ty)
}

///|
fn monomorphised_goal_type_item(
  context : @identity.CompilationContext,
  symbol : @logic.TypeSymbol,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.DiscriminateMonomorphiseGoal
  let origin = symbol.origin()
  let declaration = @logic.Decl::type_declaration(
    context,
    origin,
    [symbol],
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot declare a goal type constant",
      )
  }
  TheoryDecl(declaration)
}

///|
/// Direct port of `Libencoding.monomorphise_goal`: freely standing type
/// variables in the final goal become fresh, nullary abstract type symbols.
pub fn discriminate_monomorphise_goal(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.DiscriminateMonomorphiseGoal
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return task
  }
  let task = compile_match_task(context, task)
  let items = task.view().items
  guard !items.is_empty() &&
    items[items.length() - 1] is TheoryDecl(goal) &&
    goal.view() is Dprop(Pgoal, proposition, formula) else {
    return fail_transform(InvalidTask, stage, "task has no final goal")
  }
  let variables = formula.free_type_variables()
  if variables.is_empty() {
    return task
  }
  // Why3 collects these variables in `Stv`, whose fold order follows the
  // identifiers' allocation tags rather than formula traversal order.
  variables.sort_by((left, right) => {
    guard_compare_semantic_ids(left.semantic_id(), right.semantic_id())
  })
  let mut substitution = @logic.TySubstitution::new()
  let generated : Array[@logic.TypeSymbol] = []
  for variable in variables {
    let (symbol, replacement) = monomorphised_goal_type(context, variable)
    generated.push(symbol)
    substitution = substitution.bind(variable, replacement, None) catch {
      _ =>
        fail_transform(
          InvariantFailure,
          stage,
          "cannot bind a goal type variable",
        )
    }
  }
  let formula = instantiate_term(
    context,
    substitution,
    Map([]),
    formula,
    stage,
    None,
  )
  let goal = @logic.Decl::proposition(
    context,
    goal.origin(),
    Pgoal,
    proposition,
    formula,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot rebuild the monomorphic goal",
      )
  }
  let result = items[0:items.length() - 1].to_owned()
  for symbol in generated {
    result.push(monomorphised_goal_type_item(context, symbol))
  }
  result.push(TheoryDecl(goal))
  checked_task(task, result, stage)
}

///|
priv struct DiscriminatedInstance {
  original : @logic.LSymbol
  generated : @logic.LSymbol
  argument_types : Array[@logic.Ty]
  result_type : @logic.Ty?
}

///|
priv enum DiscriminationSelectionScope {
  SelectionNone
  SelectionGoal
  SelectionLocal
  SelectionAll
}

///|
fn discrimination_selection_scope(
  items : ArrayView[@theory.TheoryItem],
  name : BytesView,
  default_name : BytesView,
) -> DiscriminationSelectionScope raise TransformError {
  let mut selected : Bytes? = None
  let mut fallback : Bytes? = None
  for item in items {
    guard item is TheoryMeta(meta) &&
      meta.view().arguments is [MetaString(value)] else {
      continue
    }
    if meta.view().name[:] == name {
      selected = Some(value)
    } else if meta.view().name[:] == default_name {
      fallback = Some(value)
    }
  }
  let value : BytesView = match selected {
    Some(value) => value
    None =>
      match fallback {
        Some(value) => value
        None => b"none"
      }
  }
  match value {
    b"none" => SelectionNone
    b"goal" => SelectionGoal
    b"local" => SelectionLocal
    b"all" => SelectionAll
    _ =>
      fail_transform(
        UnsupportedStructure,
        @identity.DiscriminateIfPoly,
        "unknown discriminate selection scope",
      )
  }
}

///|
fn discrimination_is_local_declaration(declaration : @logic.Decl) -> Bool {
  match declaration.view() {
    Dprop(Pgoal, _, _) => true
    Dprop(Paxiom, proposition, _) =>
      proposition.view().origin
      .attributes()
      .any(attribute => attribute == b"introduced")
    Dparam(symbol) =>
      symbol.view().argument_types.is_empty() &&
      symbol.view().result_type is Some(_) &&
      symbol.view().origin
      .attributes()
      .any(attribute => attribute == b"introduced")
    Dlogic([definition]) => {
      let symbol = definition.view().symbol
      symbol.view().argument_types.is_empty() &&
      symbol.view().result_type is Some(_) &&
      symbol.view().origin
      .attributes()
      .any(attribute => attribute == b"introduced")
    }
    Dtype(_) | Ddata(_) | Dlogic(_) | Dind(_, _) | Dprop(Plemma, _, _) => false
  }
}

///|
fn discrimination_scope_includes(
  scope : DiscriminationSelectionScope,
  declaration : @logic.Decl,
) -> Bool {
  match scope {
    SelectionNone => false
    SelectionGoal => declaration.view() is Dprop(Pgoal, _, _)
    SelectionLocal => discrimination_is_local_declaration(declaration)
    SelectionAll => true
  }
}

///|
fn compare_semantic_local_id(
  left : @identity.SemanticId,
  right : @identity.SemanticId,
) -> Int {
  let left = left.local_id()
  let right = right.local_id()
  if left < right {
    -1
  } else if left > right {
    1
  } else {
    0
  }
}

///|
fn symbol_rank(
  symbols : ArrayView[@logic.TypeSymbol],
  symbol : @logic.TypeSymbol,
) -> Int {
  for index, candidate in symbols {
    if candidate == symbol {
      return index
    }
  }
  symbols.length()
}

///|
fn compare_discriminated_type(
  left : @logic.Ty,
  right : @logic.Ty,
  type_symbol_order : ArrayView[@logic.TypeSymbol],
) -> Int {
  match (left.view(), right.view()) {
    (TyVar(left), TyVar(right)) =>
      compare_semantic_local_id(left.semantic_id(), right.semantic_id())
    (TyVar(_), TyApp(_, _)) => -1
    (TyApp(_, _), TyVar(_)) => 1
    (TyApp(left_symbol, left_arguments), TyApp(right_symbol, right_arguments)) => {
      let left_rank = symbol_rank(type_symbol_order, left_symbol)
      let right_rank = symbol_rank(type_symbol_order, right_symbol)
      let symbol_order = if left_rank < right_rank {
        -1
      } else if left_rank > right_rank {
        1
      } else {
        compare_semantic_local_id(
          left_symbol.semantic_id(),
          right_symbol.semantic_id(),
        )
      }
      if symbol_order != 0 {
        return symbol_order
      }
      let shared = if left_arguments.length() < right_arguments.length() {
        left_arguments.length()
      } else {
        right_arguments.length()
      }
      for index = 0; index < shared; index = index + 1 {
        let argument_order = compare_discriminated_type(
          left_arguments[index],
          right_arguments[index],
          type_symbol_order,
        )
        if argument_order != 0 {
          return argument_order
        }
      }
      if left_arguments.length() < right_arguments.length() {
        -1
      } else if left_arguments.length() > right_arguments.length() {
        1
      } else {
        0
      }
    }
  }
}

///|
fn compare_upstream_type_order(left : @logic.Ty, right : @logic.Ty) -> Int {
  let builtin_rank = fn(ty : @logic.Ty) -> Int? {
    guard ty.view() is TyApp(symbol, arguments) && arguments.is_empty() else {
      return None
    }
    match symbol.builtin_kind() {
      Some(BuiltinInteger) => Some(0)
      Some(BuiltinReal) => Some(1)
      Some(BuiltinString) => Some(2)
      Some(BuiltinBoolean) => Some(3)
      None => None
    }
  }
  match (builtin_rank(left), builtin_rank(right)) {
    (Some(left), Some(right)) => left.compare(right)
    (Some(_), None) => -1
    (None, Some(_)) => 1
    (None, None) => left.allocation_order().compare(right.allocation_order())
  }
}

///|
fn discrimination_goal_type_depth(ty : @logic.Ty) -> Int? {
  match ty.view() {
    TyVar(_) => None
    TyApp(symbol, arguments) => {
      if symbol.view().origin.view()
        is GeneratedOrigin(DiscriminateMonomorphiseGoal, _, _, _) {
        return Some(0)
      }
      let mut depth : Int? = None
      for argument in arguments {
        guard discrimination_goal_type_depth(argument) is Some(argument_depth) else {
          continue
        }
        let candidate = argument_depth + 1
        if depth is None || (depth is Some(current) && candidate > current) {
          depth = Some(candidate)
        }
      }
      depth
    }
  }
}

///|
fn compare_discrimination_kept_type(left : @logic.Ty, right : @logic.Ty) -> Int {
  compare_discrimination_kept_type_with_discovery(left, right, None)
}

///|
fn compare_discrimination_kept_type_with_discovery(
  left : @logic.Ty,
  right : @logic.Ty,
  discovery_order : ArrayView[@logic.Ty]?,
) -> Int {
  let builtin_rank = fn(ty : @logic.Ty) -> Int? {
    guard ty.view() is TyApp(symbol, arguments) && arguments.is_empty() else {
      return None
    }
    match symbol.builtin_kind() {
      Some(BuiltinInteger) => Some(0)
      Some(BuiltinReal) => Some(1)
      Some(BuiltinString) => Some(2)
      Some(BuiltinBoolean) => Some(3)
      None => None
    }
  }
  match (builtin_rank(left), builtin_rank(right)) {
    (Some(left), Some(right)) => left.compare(right)
    (Some(_), None) => -1
    (None, Some(_)) => 1
    (None, None) => {
      if discrimination_goal_type_depth(left) is Some(left_depth) &&
        discrimination_goal_type_depth(right) is Some(right_depth) {
        let is_function_type = fn(ty : @logic.Ty) -> Bool {
          guard ty.view() is TyApp(symbol, _) else { return false }
          symbol.view().origin
          .attributes()
          .any(attribute => attribute == b"why3:builtin:function-type")
        }
        let left_function = is_function_type(left)
        let right_function = is_function_type(right)
        if !left_function && right_function {
          return -1
        }
        if left_function && !right_function {
          return 1
        }
        if left_depth != right_depth {
          return left_depth.compare(right_depth)
        }
        if left_depth > 0 && discovery_order is Some(discovery_order) {
          let left_rank = discovery_order
            .search(left)
            .unwrap_or(discovery_order.length())
          let right_rank = discovery_order
            .search(right)
            .unwrap_or(discovery_order.length())
          if left_rank != right_rank {
            return left_rank.compare(right_rank)
          }
        }
      }
      compare_upstream_type_order(left, right)
    }
  }
}

///|
fn discrimination_type_contains(outer : @logic.Ty, inner : @logic.Ty) -> Bool {
  guard outer.view() is TyApp(_, arguments) else { return false }
  arguments.any(argument => {
    argument == inner || discrimination_type_contains(argument, inner)
  })
}

///|
fn compare_discriminated_type_lists(
  left : ArrayView[@logic.Ty],
  right : ArrayView[@logic.Ty],
) -> Int {
  let shared = if left.length() < right.length() {
    left.length()
  } else {
    right.length()
  }
  for index = 0; index < shared; index = index + 1 {
    let order = compare_upstream_type_order(left[index], right[index])
    if order != 0 {
      return order
    }
  }
  if left.length() < right.length() {
    -1
  } else if left.length() > right.length() {
    1
  } else {
    0
  }
}

///|
fn compare_discriminated_algebraic_types(
  left : @logic.Ty,
  right : @logic.Ty,
) -> Int {
  match (left.view(), right.view()) {
    (TyApp(left_symbol, left_arguments), TyApp(right_symbol, right_arguments)) => {
      let symbol_order = compare_semantic_local_id(
        left_symbol.semantic_id(),
        right_symbol.semantic_id(),
      )
      if symbol_order != 0 {
        symbol_order
      } else {
        // Why3's Mts -> Styl nesting orders the outer symbol by identifier
        // tag and each concrete argument list by the types' hash-cons tags.
        compare_discriminated_type_lists(left_arguments, right_arguments)
      }
    }
    (TyVar(_), TyApp(_, _)) => -1
    (TyApp(_, _), TyVar(_)) => 1
    (TyVar(left), TyVar(right)) =>
      compare_semantic_local_id(left.semantic_id(), right.semantic_id())
  }
}

///|
fn discriminated_signature(
  instance : DiscriminatedInstance,
) -> Array[@logic.Ty] {
  let signature : Array[@logic.Ty] = []
  if instance.result_type is Some(result_type) {
    signature.push(result_type)
  }
  signature.append(instance.argument_types)
  signature
}

///|
fn compare_discriminated_instances(
  left : DiscriminatedInstance,
  right : DiscriminatedInstance,
) -> Int {
  let symbol_order = compare_semantic_local_id(
    left.original.semantic_id(),
    right.original.semantic_id(),
  )
  if symbol_order != 0 {
    return symbol_order
  }
  compare_discriminated_type_lists(
    discriminated_signature(left),
    discriminated_signature(right),
  )
}

///|
fn application_signature(
  arguments : ArrayView[@logic.Term],
  result_type : @logic.Ty?,
  stage : @identity.GeneratedStage,
) -> (Array[@logic.Ty], @logic.Ty?) raise TransformError {
  let argument_types : Array[@logic.Ty] = []
  for argument in arguments {
    guard argument.ty() is Some(ty) else {
      return fail_transform(
        InvariantFailure,
        stage,
        "logic application has a formula argument",
      )
    }
    argument_types.push(ty)
  }
  (argument_types, result_type)
}

///|
fn same_signature(
  instance : DiscriminatedInstance,
  argument_types : ArrayView[@logic.Ty],
  result_type : @logic.Ty?,
) -> Bool {
  instance.argument_types[:] == argument_types &&
  instance.result_type == result_type
}

///|
fn find_instance(
  instances : ArrayView[DiscriminatedInstance],
  original : @logic.LSymbol,
  argument_types : ArrayView[@logic.Ty],
  result_type : @logic.Ty?,
) -> @logic.LSymbol? {
  for instance in instances {
    if instance.original == original &&
      same_signature(instance, argument_types, result_type) {
      return Some(instance.generated)
    }
  }
  None
}

///|
priv struct DiscriminatedSymbolCacheEntry {
  argument_types : Array[@logic.Ty]
  result_type : @logic.Ty?
  generated : @logic.LSymbol
}

///|
let discriminated_symbol_cache : Ref[
  Map[@logic.LSymbol, Array[DiscriminatedSymbolCacheEntry]],
] = Ref(Map([]))

///|
fn make_discriminated_symbol(
  context : @identity.CompilationContext,
  original : @logic.LSymbol,
  argument_types : ArrayView[@logic.Ty],
  result_type : @logic.Ty?,
) -> @logic.LSymbol raise TransformError {
  let cache = discriminated_symbol_cache.val
  match cache.get(original) {
    Some(entries) =>
      for entry in entries {
        if entry.argument_types[:] == argument_types &&
          entry.result_type == result_type {
          return entry.generated
        }
      }
    None => ()
  }
  let stage = @identity.DiscriminateIfPoly
  let view = original.view()
  let origin = derived_generated_origin(
    stage,
    view.name,
    view.origin,
    derived_generated_attributes(view.origin),
  )
  let generated = match result_type {
    Some(result_type) =>
      @logic.LSymbol::new_function(
        context,
        view.name,
        origin,
        argument_types,
        result_type,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot create a function instance",
          )
      }
    None =>
      @logic.LSymbol::new_predicate(
        context,
        view.name,
        origin,
        argument_types,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot create a predicate instance",
          )
      }
  }
  let entries = match cache.get(original) {
    Some(entries) => entries.copy()
    None => []
  }
  entries.push({
    argument_types: argument_types.to_owned(),
    result_type,
    generated,
  })
  cache[original] = entries
  discriminated_symbol_cache.val = cache
  generated
}

///|
fn tagged_discrimination_types(
  items : ArrayView[@theory.TheoryItem],
  name : BytesView,
) -> Array[@logic.Ty] {
  let result : Array[@logic.Ty] = []
  for item in items {
    guard item is TheoryMeta(meta) &&
      meta.view().name[:] == name &&
      meta.view().arguments is [MetaType(ty)] else {
      continue
    }
    push_discrimination_type_once(result, ty)
  }
  result
}

///|
fn tagged_discrimination_logic_symbols(
  items : ArrayView[@theory.TheoryItem],
  name : BytesView,
) -> Array[@logic.LSymbol] {
  let result : Array[@logic.LSymbol] = []
  for item in items {
    guard item is TheoryMeta(meta) &&
      meta.view().name[:] == name &&
      meta.view().arguments is [MetaLogicSymbol(symbol)] else {
      continue
    }
    if !result.contains(symbol) {
      result.push(symbol)
    }
  }
  result
}

///|
fn tagged_discrimination_propositions(
  items : ArrayView[@theory.TheoryItem],
  name : BytesView,
) -> Array[@logic.PrSymbol] {
  let result : Array[@logic.PrSymbol] = []
  for item in items {
    guard item is TheoryMeta(meta) &&
      meta.view().name[:] == name &&
      meta.view().arguments is [MetaPropositionSymbol(proposition)] else {
      continue
    }
    if !result.contains(proposition) {
      result.push(proposition)
    }
  }
  result
}

///|
fn discrimination_symbol_signature(symbol : @logic.LSymbol) -> Array[@logic.Ty] {
  let signature : Array[@logic.Ty] = []
  if symbol.view().result_type is Some(result_type) {
    signature.push(result_type)
  }
  signature.append(symbol.view().argument_types)
  signature
}

///|
fn discrimination_completion_substitutions(
  symbol : @logic.LSymbol,
  types : ArrayView[@logic.Ty],
) -> Array[@logic.TySubstitution] {
  let substitutions = [@logic.TySubstitution::new()]
  for pattern in discrimination_symbol_signature(symbol) {
    let next : Array[@logic.TySubstitution] = []
    for substitution in substitutions {
      for actual in types {
        let matched = substitution.match_type(pattern, actual, None) catch {
          _ => continue
        }
        push_substitution_once(next, matched)
      }
    }
    substitutions.clear()
    substitutions.push_iter(next.iter())
    if substitutions.is_empty() {
      return []
    }
  }
  substitutions
}

///|
fn complete_discriminated_logic_instances(
  context : @identity.CompilationContext,
  symbols : ArrayView[@logic.LSymbol],
  types : ArrayView[@logic.Ty],
  instances : Array[DiscriminatedInstance],
) -> Unit raise TransformError {
  for symbol in symbols {
    let view = symbol.view()
    if !(view.role is Ordinary) {
      continue
    }
    for substitution in discrimination_completion_substitutions(symbol, types) {
      let argument_types : Array[@logic.Ty] = []
      let mut closed = true
      for argument in view.argument_types {
        let argument = substitution.apply(argument, None) catch {
          _ => {
            closed = false
            break
          }
        }
        if !argument.is_closed() {
          closed = false
          break
        }
        argument_types.push(argument)
      }
      if !closed {
        continue
      }
      let mut result_type : @logic.Ty? = None
      if view.result_type is Some(original_result) {
        let result = substitution.apply(original_result, None) catch {
          _ => {
            closed = false
            original_result
          }
        }
        if closed {
          result_type = Some(result)
        }
      }
      if !closed ||
        (result_type is Some(result_type) && !result_type.is_closed()) ||
        find_instance(instances, symbol, argument_types, result_type) is Some(_) {
        continue
      }
      instances.push({
        original: symbol,
        generated: make_discriminated_symbol(
          context, symbol, argument_types, result_type,
        ),
        argument_types,
        result_type,
      })
    }
  }
}

///|
priv struct CompileMatchRow {
  patterns : Array[@logic.Pattern]
  body : @logic.Term
}

///|
priv struct CompileMatchGroup {
  symbol : @logic.LSymbol
  argument_patterns : Array[@logic.Pattern]
  rows : Array[CompileMatchRow]
}

///|
fn prepend_compile_match_patterns(
  prefix : ArrayView[@logic.Pattern],
  suffix : ArrayView[@logic.Pattern],
) -> Array[@logic.Pattern] {
  let result : Array[@logic.Pattern] = []
  for reverse_index = 0
      reverse_index < prefix.length()
      reverse_index = reverse_index + 1 {
    result.push(prefix[prefix.length() - reverse_index - 1])
  }
  result.append(suffix)
  result
}

///|
fn prepend_compile_match_terms(
  prefix : ArrayView[@logic.Term],
  suffix : ArrayView[@logic.Term],
) -> Array[@logic.Term] {
  let result : Array[@logic.Term] = []
  for reverse_index = 0
      reverse_index < prefix.length()
      reverse_index = reverse_index + 1 {
    result.push(prefix[prefix.length() - reverse_index - 1])
  }
  result.append(suffix)
  result
}

///|
fn drop_first_compile_match_pattern(
  patterns : ArrayView[@logic.Pattern],
) -> Array[@logic.Pattern] {
  if patterns.is_empty() {
    []
  } else {
    patterns[1:].to_owned()
  }
}

///|
fn drop_first_compile_match_term(
  terms : ArrayView[@logic.Term],
) -> Array[@logic.Term] {
  if terms.is_empty() {
    []
  } else {
    terms[1:].to_owned()
  }
}

///|
fn compile_match_group_index(
  groups : ArrayView[CompileMatchGroup],
  symbol : @logic.LSymbol,
) -> Int? {
  for index, group in groups {
    if group.symbol == symbol {
      return Some(index)
    }
  }
  None
}

///|
fn populate_compile_match_groups(
  pattern : @logic.Pattern,
  groups : Array[CompileMatchGroup],
) -> Unit raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  match pattern.view() {
    Pwild(_) | Pvar(_) => ()
    Pas(inner, _, _) => populate_compile_match_groups(inner, groups)
    Por(left, right, _) => {
      populate_compile_match_groups(left, groups)
      populate_compile_match_groups(right, groups)
    }
    Papp(symbol, arguments, _) =>
      match symbol.view().role {
        Constructor(_) =>
          if compile_match_group_index(groups, symbol) is None {
            groups.push({
              symbol,
              argument_patterns: arguments.to_owned(),
              rows: [],
            })
          }
        Ordinary | Projection =>
          fail_transform(
            UnsupportedStructure,
            stage,
            "compile_match pattern head is not a constructor",
          )
      }
  }
}

///|
fn append_compile_match_wild_row(
  groups : Array[CompileMatchGroup],
  remaining : ArrayView[@logic.Pattern],
  body : @logic.Term,
) -> Unit {
  for group in groups {
    let patterns = [
      for pattern in group.argument_patterns => {
        @logic.Pattern::wild(pattern.ty())
      }
    ]
    patterns.append(remaining)
    group.rows.push({ patterns, body })
  }
}

///|
fn dispatch_compile_match_pattern(
  context : @identity.CompilationContext,
  scrutinee : @logic.Term,
  pattern : @logic.Pattern,
  remaining : ArrayView[@logic.Pattern],
  body : @logic.Term,
  groups : Array[CompileMatchGroup],
  wilds : Array[CompileMatchRow],
) -> Unit raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  match pattern.view() {
    Papp(symbol, arguments, _) => {
      guard compile_match_group_index(groups, symbol) is Some(index) else {
        return fail_transform(
          InvariantFailure,
          stage,
          "compile_match constructor is absent from its dispatch table",
        )
      }
      groups[index].rows.push({
        patterns: prepend_compile_match_patterns(arguments, remaining),
        body,
      })
    }
    Por(left, right, _) => {
      dispatch_compile_match_pattern(
        context, scrutinee, left, remaining, body, groups, wilds,
      )
      dispatch_compile_match_pattern(
        context, scrutinee, right, remaining, body, groups, wilds,
      )
    }
    Pas(inner, variable, _) => {
      let body = let_simplified(
        context, variable, scrutinee, body, false, stage,
      )
      dispatch_compile_match_pattern(
        context, scrutinee, inner, remaining, body, groups, wilds,
      )
    }
    Pvar(variable) => {
      let body = let_simplified(
        context, variable, scrutinee, body, false, stage,
      )
      append_compile_match_wild_row(groups, remaining, body)
      wilds.push({ patterns: remaining.to_owned(), body })
    }
    Pwild(_) => {
      append_compile_match_wild_row(groups, remaining, body)
      wilds.push({ patterns: remaining.to_owned(), body })
    }
  }
}

///|
fn compile_match_rows(
  context : @identity.CompilationContext,
  terms : ArrayView[@logic.Term],
  rows : ArrayView[CompileMatchRow],
) -> @logic.Term raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  guard !rows.is_empty() else {
    return fail_transform(
      UnsupportedStructure,
      stage,
      "compile_match encountered a non-exhaustive pattern matrix",
    )
  }
  if terms.is_empty() {
    return rows[0].body
  }
  let scrutinee = terms[0]
  guard scrutinee.ty() is Some(scrutinee_type) else {
    return fail_transform(
      InvariantFailure,
      stage,
      "compile_match scrutinee is a formula",
    )
  }
  let remaining_terms = drop_first_compile_match_term(terms)
  let groups : Array[CompileMatchGroup] = []
  for row in rows {
    guard !row.patterns.is_empty() else {
      return fail_transform(
        InvariantFailure,
        stage,
        "compile_match row has fewer patterns than scrutinees",
      )
    }
    populate_compile_match_groups(row.patterns[0], groups)
  }
  let wilds : Array[CompileMatchRow] = []
  for row in rows {
    dispatch_compile_match_pattern(
      context,
      scrutinee,
      row.patterns[0],
      drop_first_compile_match_pattern(row.patterns),
      row.body,
      groups,
      wilds,
    )
  }
  if groups.is_empty() {
    return compile_match_rows(context, remaining_terms, wilds)
  }
  match scrutinee.view() {
    Tapp(symbol, _, arguments) =>
      match symbol.view().role {
        Constructor(_) =>
          match compile_match_group_index(groups, symbol) {
            Some(index) =>
              return compile_match_rows(
                context,
                prepend_compile_match_terms(arguments, remaining_terms),
                groups[index].rows,
              )
            None => return compile_match_rows(context, remaining_terms, wilds)
          }
        Ordinary | Projection => ()
      }
    _ => ()
  }
  let branches : Array[(@logic.Pattern, @logic.Term)] = []
  for group in groups {
    let variables : Array[@logic.VSymbol] = []
    for pattern in group.argument_patterns {
      let origin = @identity.Origin::generated(
        @identity.DiscriminateMonomorphiseGoal,
        b"x",
        None,
        [],
      )
      variables.push(
        @logic.VSymbol::new(context, b"x", origin, pattern.ty(), None) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              stage,
              "compile_match cannot create a constructor binder",
            )
        },
      )
    }
    let pattern = @logic.Pattern::app(
      group.symbol,
      variables.map(@logic.Pattern::variable),
      scrutinee_type,
      None,
    ) catch {
      _ =>
        return fail_transform(
          InvariantFailure,
          stage,
          "compile_match cannot rebuild a constructor pattern",
        )
    }
    let body = compile_match_rows(
      context,
      prepend_compile_match_terms(
        variables.map(@logic.Term::variable),
        remaining_terms,
      ),
      group.rows,
    )
    branches.push((pattern, body))
  }
  let complete = match groups[0].symbol.view().role {
    Constructor(count) => groups.length() == count
    Ordinary | Projection => false
  }
  if !complete {
    branches.push(
      (
        @logic.Pattern::wild(scrutinee_type),
        compile_match_rows(context, remaining_terms, wilds),
      ),
    )
  }
  @logic.Term::case(scrutinee, branches, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "compile_match cannot rebuild a primitive case",
      )
  }
}

///|
fn substitute_opened_compile_match_binders(
  term : @logic.Term,
  substitution : Map[@logic.VSymbol, @logic.VSymbol],
) -> @logic.Term raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  let recurse = fn(child) -> @logic.Term raise TransformError {
    substitute_opened_compile_match_binders(child, substitution)
  }
  match term.view() {
    Tvar(variable) =>
      match substitution.get(variable) {
        Some(replacement) =>
          copy_term_decoration(term, @logic.Term::variable(replacement))
        None => term
      }
    _ => map_plain(term, recurse, stage)
  }
}

///|
fn compile_match_term(
  context : @identity.CompilationContext,
  term : @logic.Term,
  open_quantifiers : Bool,
) -> @logic.Term raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  let recurse = fn(child) -> @logic.Term raise TransformError {
    compile_match_term(context, child, open_quantifiers)
  }
  match term.view() {
    Tcase(scrutinee, branches) => {
      let rows = [
        for branch in branches => {
          let view = branch.view()
          CompileMatchRow::{
            patterns: [view.pattern],
            body: recurse(view.body),
          }
        }
      ]
      let replacement = compile_match_rows(context, [recurse(scrutinee)], rows)
      copy_term_decoration(term, replacement)
    }
    Tquant(quantifier, binders, triggers, body) => {
      if !open_quantifiers {
        return map_plain(term, recurse, stage)
      }
      let replacements : Array[@logic.VSymbol] = []
      let substitution : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
      for binder in binders {
        let replacement = binder.clone_identifier(context, None) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              stage,
              "compile_match cannot open a quantified binder",
            )
        }
        replacements.push(replacement)
        substitution[binder] = replacement
      }
      let opened_triggers : Array[Array[@logic.Term]] = []
      let mapped_triggers : Array[Array[@logic.Term]] = []
      for group in triggers {
        let opened_group : Array[@logic.Term] = []
        let mapped : Array[@logic.Term] = []
        for trigger in group {
          let opened = substitute_opened_compile_match_binders(
            trigger, substitution,
          )
          opened_group.push(opened)
          mapped.push(recurse(opened))
        }
        opened_triggers.push(opened_group)
        mapped_triggers.push(mapped)
      }
      let opened_body = substitute_opened_compile_match_binders(
        body, substitution,
      )
      let mapped_body = recurse(opened_body)
      if mapped_body == opened_body && mapped_triggers == opened_triggers {
        return term
      }
      let replacement = @logic.Term::quantify(
        quantifier,
        replacements,
        mapped_triggers,
        mapped_body,
        None,
      ) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "compile_match cannot rebuild a quantified term",
          )
      }
      copy_term_decoration(term, replacement)
    }
    _ => map_plain(term, recurse, stage)
  }
}

///|
fn compile_match_declaration_uncached(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
) -> @logic.Decl raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  match declaration.view() {
    Dtype(_) | Ddata(_) | Dparam(_) => declaration
    Dlogic(definitions) => {
      let rewritten : Array[@logic.LogicDefinition] = []
      let mut changed = false
      for definition in definitions {
        let view = definition.view()
        let replacements : Array[@logic.VSymbol] = []
        let substitution : Map[@logic.VSymbol, @logic.VSymbol] = Map([])
        for parameter in view.parameters {
          let replacement = parameter.clone_identifier(context, None) catch {
            _ =>
              return fail_transform(
                InvariantFailure,
                stage,
                "compile_match cannot open a logic definition",
              )
          }
          replacements.push(replacement)
          substitution[parameter] = replacement
        }
        let opened_body = substitute_opened_compile_match_binders(
          view.body,
          substitution,
        )
        let mapped_body = compile_match_term(context, opened_body, true)
        if mapped_body == opened_body {
          rewritten.push(definition)
        } else {
          changed = true
          rewritten.push(
            @logic.LogicDefinition::new(
              context,
              view.symbol,
              replacements,
              mapped_body,
              None,
            ) catch {
              _ =>
                return fail_transform(
                  InvariantFailure,
                  stage,
                  "compile_match cannot rebuild a logic definition",
                )
            },
          )
        }
      }
      if !changed {
        return declaration
      }
      @logic.Decl::logic(context, declaration.origin(), rewritten, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "compile_match cannot rebuild a logic declaration",
          )
      }
    }
    Dind(sign, declarations) => {
      let rewritten : Array[@logic.InductiveDeclaration] = []
      for inductive in declarations {
        let view = inductive.view()
        let cases : Array[@logic.InductiveCase] = []
        for case_ in view.cases {
          let case_view = case_.view()
          cases.push(
            @logic.InductiveCase::new(
              context,
              case_view.proposition,
              compile_match_term(context, case_view.formula, true),
              None,
            ) catch {
              _ =>
                return fail_transform(
                  InvariantFailure,
                  stage,
                  "compile_match cannot rebuild an inductive case",
                )
            },
          )
        }
        rewritten.push(
          @logic.InductiveDeclaration::new(view.predicate, cases, None) catch {
            _ =>
              return fail_transform(
                InvariantFailure,
                stage,
                "compile_match cannot rebuild an inductive declaration",
              )
          },
        )
      }
      @logic.Decl::inductive(
        context,
        declaration.origin(),
        sign,
        rewritten,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "compile_match cannot rebuild an inductive group",
          )
      }
    }
    Dprop(kind, proposition, formula) =>
      @logic.Decl::proposition(
        context,
        declaration.origin(),
        kind,
        proposition,
        compile_match_term(context, formula, kind != Pgoal),
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "compile_match cannot rebuild a proposition",
          )
      }
  }
}

///|
priv struct CompileMatchCacheEntry {
  input : @logic.Decl
  output : @logic.Decl
  generation : Int64
  persistent : Bool
}

///|
let compile_match_declaration_cache : Ref[
  Map[@identity.SemanticId, Array[CompileMatchCacheEntry]],
] = Ref(Map([]))

///|
fn compile_match_cache_key(declaration : @logic.Decl) -> @identity.SemanticId? {
  match declaration.view() {
    Dlogic(definitions) =>
      if definitions.is_empty() {
        None
      } else {
        Some(definitions[0].view().symbol.semantic_id())
      }
    Dind(_, declarations) =>
      if declarations.is_empty() {
        None
      } else {
        Some(declarations[0].view().predicate.semantic_id())
      }
    Dprop(Pgoal, _, _) => None
    Dprop(Paxiom, proposition, _) | Dprop(Plemma, proposition, _) =>
      Some(proposition.semantic_id())
    Dtype(_) | Ddata(_) | Dparam(_) => None
  }
}

///|
fn compile_match_definition_equal(
  left : @logic.LogicDefinition,
  right : @logic.LogicDefinition,
) -> Bool {
  let left = left.view()
  let right = right.view()
  left.symbol == right.symbol &&
  left.parameters == right.parameters &&
  left.decreasing_parameters == right.decreasing_parameters &&
  left.body == right.body
}

///|
fn compile_match_inductive_equal(
  left : @logic.InductiveDeclaration,
  right : @logic.InductiveDeclaration,
) -> Bool {
  let left = left.view()
  let right = right.view()
  if left.predicate != right.predicate ||
    left.cases.length() != right.cases.length() {
    return false
  }
  for index, left_case in left.cases {
    let left_case = left_case.view()
    let right_case = right.cases[index].view()
    if left_case.proposition != right_case.proposition ||
      left_case.formula != right_case.formula {
      return false
    }
  }
  true
}

///|
fn compile_match_declaration_equal(
  left : @logic.Decl,
  right : @logic.Decl,
) -> Bool {
  if left.origin() != right.origin() {
    return false
  }
  match (left.view(), right.view()) {
    (Dlogic(left), Dlogic(right)) => {
      if left.length() != right.length() {
        return false
      }
      for index, definition in left {
        if !compile_match_definition_equal(definition, right[index]) {
          return false
        }
      }
      true
    }
    (Dind(left_sign, left), Dind(right_sign, right)) => {
      if left_sign != right_sign || left.length() != right.length() {
        return false
      }
      for index, declaration in left {
        if !compile_match_inductive_equal(declaration, right[index]) {
          return false
        }
      }
      true
    }
    (
      Dprop(left_kind, left_proposition, left_formula),
      Dprop(right_kind, right_proposition, right_formula),
    ) =>
      left_kind == right_kind &&
      left_proposition == right_proposition &&
      left_formula == right_formula
    _ => false
  }
}

///|
fn compile_match_declaration(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
) -> @logic.Decl raise TransformError {
  guard compile_match_cache_key(declaration) is Some(key) else {
    return compile_match_declaration_uncached(context, declaration)
  }
  let generation = current_declaration_cache_generation()
  let persistent = declaration_cache_is_persistent(declaration)
  let cache = compile_match_declaration_cache.val
  match cache.get(key) {
    Some(entries) =>
      for entry in entries {
        if entry.persistent && persistent {
          return entry.output
        }
        if !entry.persistent &&
          !persistent &&
          entry.generation == generation &&
          (
            compile_match_declaration_equal(declaration, entry.input) ||
            compile_match_declaration_equal(declaration, entry.output)
          ) {
          return entry.output
        }
      }
    None => ()
  }
  let output = compile_match_declaration_uncached(context, declaration)
  if persistent {
    declaration_cache_retain(output)
  }
  let entries = match cache.get(key) {
    Some(entries) => entries.copy()
    None => []
  }
  entries.push({ input: declaration, output, generation, persistent })
  cache[key] = entries
  compile_match_declaration_cache.val = cache
  output
}

///|
fn compile_match_task(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  let items : Array[@theory.TheoryItem] = []
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) =>
        items.push(TheoryDecl(compile_match_declaration(context, declaration)))
      TheoryUse(_) | TheoryClone(_) | TheoryMeta(_) => items.push(item)
    }
  }
  checked_task(task, items, stage)
}

///|
fn collect_discriminated_instances(
  context : @identity.CompilationContext,
  term : @logic.Term,
  instances : Array[DiscriminatedInstance],
) -> Unit raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  let visit = fn(child) -> Unit raise TransformError {
    collect_discriminated_instances(context, child, instances)
  }
  match term.view() {
    Tapp(symbol, _, arguments) => {
      let view = symbol.view()
      let (argument_types, result_type) = application_signature(
        arguments,
        term.ty(),
        stage,
      )
      let closed = argument_types.all(ty => ty.is_closed()) &&
        (result_type is None || (result_type is Some(ty) && ty.is_closed()))
      if !view.type_parameters.is_empty() &&
        view.role is Ordinary &&
        !is_builtin_equality(symbol) &&
        closed &&
        find_instance(instances, symbol, argument_types, result_type) is None {
        instances.push({
          original: symbol,
          generated: make_discriminated_symbol(
            context, symbol, argument_types, result_type,
          ),
          argument_types,
          result_type,
        })
      }
      for argument in arguments {
        visit(argument)
      }
    }
    Tif(condition, then_branch, else_branch) => {
      visit(condition)
      visit(then_branch)
      visit(else_branch)
    }
    Tlet(_, value, body) => {
      visit(value)
      visit(body)
    }
    Tcase(scrutinee, branches) => {
      visit(scrutinee)
      for branch in branches {
        visit(branch.view().body)
      }
    }
    Teps(_, body) => visit(body)
    Tquant(_, _, triggers, body) => {
      for group in triggers {
        for trigger in group {
          visit(trigger)
        }
      }
      visit(body)
    }
    Tbinop(_, left, right) => {
      visit(left)
      visit(right)
    }
    Tnot(inner) => visit(inner)
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => ()
  }
}

///|
fn collect_discriminated_declaration_instances(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  instances : Array[DiscriminatedInstance],
) -> Unit raise TransformError {
  match declaration.view() {
    Dlogic(definitions) =>
      for definition in definitions {
        collect_discriminated_instances(
          context,
          definition.view().body,
          instances,
        )
      }
    Dind(_, declarations) =>
      for inductive in declarations {
        for case_ in inductive.view().cases {
          collect_discriminated_instances(
            context,
            case_.view().formula,
            instances,
          )
        }
      }
    Dprop(_, _, formula) =>
      collect_discriminated_instances(context, formula, instances)
    Dtype(_) | Ddata(_) | Dparam(_) => ()
  }
}

///|
fn push_discrimination_type_once(
  types : Array[@logic.Ty],
  ty : @logic.Ty,
) -> Unit {
  if !types.contains(ty) {
    types.push(ty)
  }
}

///|
fn collect_discrimination_instance_types(
  term : @logic.Term,
  types : Array[@logic.Ty],
) -> Unit {
  let visit = fn(child) { collect_discrimination_instance_types(child, types) }
  match term.view() {
    Tapp(_, _, arguments) =>
      for argument in arguments {
        if argument.ty() is Some(ty) && ty.is_closed() {
          push_discrimination_type_once(types, ty)
        }
        visit(argument)
      }
    Tif(condition, then_branch, else_branch) => {
      visit(condition)
      visit(then_branch)
      visit(else_branch)
    }
    Tlet(_, value, body) => {
      visit(value)
      visit(body)
    }
    Tcase(scrutinee, branches) => {
      if scrutinee.ty() is Some(ty) && ty.is_closed() {
        push_discrimination_type_once(types, ty)
      }
      visit(scrutinee)
      for branch in branches {
        visit(branch.view().body)
      }
    }
    Teps(_, body) => visit(body)
    Tquant(_, _, triggers, body) => {
      for group in triggers {
        for trigger in group {
          visit(trigger)
        }
      }
      visit(body)
    }
    Tbinop(_, left, right) => {
      visit(left)
      visit(right)
    }
    Tnot(inner) => visit(inner)
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => ()
  }
}

///|
fn collect_discrimination_declaration_instance_types(
  declaration : @logic.Decl,
  types : Array[@logic.Ty],
) -> Unit {
  match declaration.view() {
    Dlogic(definitions) =>
      for definition in definitions {
        collect_discrimination_instance_types(definition.view().body, types)
      }
    Dind(_, declarations) =>
      for inductive in declarations {
        for case_ in inductive.view().cases {
          collect_discrimination_instance_types(case_.view().formula, types)
        }
      }
    Dprop(_, _, formula) =>
      collect_discrimination_instance_types(formula, types)
    Dtype(_) | Ddata(_) | Dparam(_) => ()
  }
}

///|
fn discrimination_type_contains_symbol(
  ty : @logic.Ty,
  symbols : Map[@logic.TypeSymbol, Unit],
) -> Bool {
  match ty.view() {
    TyVar(_) => false
    TyApp(symbol, arguments) =>
      symbols.contains(symbol) ||
      arguments.any(argument => {
        discrimination_type_contains_symbol(argument, symbols)
      })
  }
}

///|
fn discrimination_data_group_symbols(
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
fn complete_discrimination_instance_type(
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
    complete_discrimination_instance_type(known, argument, completed)
  }
  let constructors = known.find_constructors(symbol, None) catch { _ => return }
  if constructors.is_empty() {
    return
  }
  let formal = @logic.Ty::app(
    symbol,
    symbol.view().parameters.map(@logic.Ty::variable),
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        @identity.DiscriminateIfPoly,
        "cannot construct an instance-completion template",
      )
  }
  let substitution = @logic.TySubstitution::new().match_type(formal, ty, None) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        @identity.DiscriminateIfPoly,
        "cannot instantiate an instance-completion template",
      )
  }
  let recursive = discrimination_data_group_symbols(known, symbol)
  for data_constructor in constructors {
    for field in data_constructor.view().symbol.view().argument_types {
      if discrimination_type_contains_symbol(field, recursive) {
        continue
      }
      let field = substitution.apply(field, None) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            @identity.DiscriminateIfPoly,
            "cannot instantiate an instance-completion field",
          )
      }
      complete_discrimination_instance_type(known, field, completed)
    }
  }
}

///|
fn completed_discrimination_instance_types(
  context : @identity.CompilationContext,
  task : @theory.Task,
  selected : ArrayView[@logic.Ty],
) -> Array[@logic.Ty] raise TransformError {
  let known = match task.known() {
    Some(known) => known
    None => {
      let mut known = @logic.KnownMap::new(context)
      for item in task.view().items {
        if item is TheoryDecl(declaration) {
          known = known.add(declaration, None) catch {
            _ =>
              return fail_transform(
                InvalidTask,
                @identity.DiscriminateIfPoly,
                "cannot reconstruct the instance-completion known map",
              )
          }
        }
      }
      known
    }
  }
  let completed : Array[@logic.Ty] = []
  for ty in selected {
    complete_discrimination_instance_type(known, ty, completed)
  }
  completed
}

///|
fn substitution_equal(
  left : @logic.TySubstitution,
  right : @logic.TySubstitution,
) -> Bool {
  let left_bindings = left.bindings()
  let right_bindings = right.bindings()
  if left_bindings.length() != right_bindings.length() {
    return false
  }
  left_bindings.all(entry => right.get(entry.0) == Some(entry.1))
}

///|
fn push_substitution_once(
  substitutions : Array[@logic.TySubstitution],
  substitution : @logic.TySubstitution,
) -> Unit {
  if !substitutions.any(existing => substitution_equal(existing, substitution)) {
    substitutions.push(substitution)
  }
}

///|
fn compare_instance_substitutions(
  left : @logic.TySubstitution,
  right : @logic.TySubstitution,
) -> Int {
  let left_bindings = left.bindings()
  let right_bindings = right.bindings()
  left_bindings.sort_by((left, right) => {
    compare_semantic_local_id(left.0.semantic_id(), right.0.semantic_id())
  })
  right_bindings.sort_by((left, right) => {
    compare_semantic_local_id(left.0.semantic_id(), right.0.semantic_id())
  })
  let shared = if left_bindings.length() < right_bindings.length() {
    left_bindings.length()
  } else {
    right_bindings.length()
  }
  for index = 0; index < shared; index = index + 1 {
    let variable_order = compare_semantic_local_id(
      left_bindings[index].0.semantic_id(),
      right_bindings[index].0.semantic_id(),
    )
    if variable_order != 0 {
      return variable_order
    }
    let type_order = compare_upstream_type_order(
      left_bindings[index].1,
      right_bindings[index].1,
    )
    if type_order != 0 {
      return type_order
    }
  }
  left_bindings.length().compare(right_bindings.length())
}

///|
fn match_instance_signature(
  substitution : @logic.TySubstitution,
  actual_arguments : ArrayView[@logic.Ty],
  actual_result : @logic.Ty?,
  instance : DiscriminatedInstance,
) -> @logic.TySubstitution? {
  if actual_arguments.length() != instance.argument_types.length() {
    return None
  }
  let mut result = substitution
  for index, actual in actual_arguments {
    result = result.match_type(actual, instance.argument_types[index], None) catch {
      _ => return None
    }
  }
  match (actual_result, instance.result_type) {
    (None, None) => Some(result)
    (Some(actual), Some(expected)) =>
      Some(result.match_type(actual, expected, None)) catch {
        _ => None
      }
    _ => None
  }
}

///|
fn collect_instance_substitutions(
  term : @logic.Term,
  instances : ArrayView[DiscriminatedInstance],
  algebraic_types : ArrayView[@logic.Ty],
  substitutions : Array[@logic.TySubstitution],
) -> Unit raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  let visit = fn(child) -> Unit raise TransformError {
    collect_instance_substitutions(
      child, instances, algebraic_types, substitutions,
    )
  }
  let collect_algebraic = fn(actual : @logic.Ty) {
    let basis = substitutions.copy()
    for instance in algebraic_types {
      for substitution in basis {
        let matched = substitution.match_type(actual, instance, None) catch {
          _ => continue
        }
        push_substitution_once(substitutions, matched)
      }
    }
  }
  match term.view() {
    Tapp(symbol, _, arguments) => {
      let (argument_types, result_type) = application_signature(
        arguments,
        term.ty(),
        stage,
      )
      let basis = substitutions.copy()
      for instance in instances {
        if instance.original != symbol {
          continue
        }
        for substitution in basis {
          if match_instance_signature(
              substitution, argument_types, result_type, instance,
            )
            is Some(matched) {
            push_substitution_once(substitutions, matched)
          }
        }
      }
      match symbol.view().role {
        Constructor(_) => if term.ty() is Some(ty) { collect_algebraic(ty) }
        Projection =>
          if !arguments.is_empty() && arguments[0].ty() is Some(ty) {
            collect_algebraic(ty)
          }
        Ordinary => ()
      }
      for argument in arguments {
        visit(argument)
      }
    }
    Tif(condition, then_branch, else_branch) => {
      visit(condition)
      visit(then_branch)
      visit(else_branch)
    }
    Tlet(_, value, body) => {
      visit(value)
      visit(body)
    }
    Tcase(scrutinee, branches) => {
      if scrutinee.ty() is Some(ty) {
        collect_algebraic(ty)
      }
      visit(scrutinee)
      for branch in branches {
        visit(branch.view().body)
      }
    }
    Teps(_, body) => visit(body)
    Tquant(_, _, triggers, body) => {
      for group in triggers {
        for trigger in group {
          visit(trigger)
        }
      }
      visit(body)
    }
    Tbinop(_, left, right) => {
      visit(left)
      visit(right)
    }
    Tnot(inner) => visit(inner)
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => ()
  }
}

///|
fn ordered_instance_substitutions(
  formula : @logic.Term,
  instances : ArrayView[DiscriminatedInstance],
  algebraic_types : ArrayView[@logic.Ty],
) -> Array[@logic.TySubstitution] raise TransformError {
  let substitutions = [@logic.TySubstitution::new()]
  collect_instance_substitutions(
    formula, instances, algebraic_types, substitutions,
  )
  if substitutions.length() <= 1 {
    return substitutions
  }
  substitutions.sort_by(compare_instance_substitutions)
  substitutions.rev_in_place()
  substitutions
}

///|
fn rewrite_discriminated_term(
  term : @logic.Term,
  instances : ArrayView[DiscriminatedInstance],
) -> @logic.Term raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  let recurse = fn(child) -> @logic.Term raise TransformError {
    rewrite_discriminated_term(child, instances)
  }
  match term.view() {
    Tapp(symbol, _, arguments) => {
      let mapped = [ for argument in arguments => recurse(argument) ]
      let (argument_types, result_type) = application_signature(
        mapped,
        term.ty(),
        stage,
      )
      let replacement_symbol = match
        find_instance(instances, symbol, argument_types, result_type) {
        Some(instance) => instance
        None => symbol
      }
      let replacement = @logic.Term::elaborated_apply(
        replacement_symbol,
        mapped,
        result_type,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot rewrite a logic instance",
          )
      }
      copy_term_decoration(term, replacement)
    }
    _ => map_plain(term, recurse, stage)
  }
}

///|
fn cloned_proposition(
  context : @identity.CompilationContext,
  proposition : @logic.PrSymbol,
) -> (@logic.PrSymbol, @identity.Origin) {
  let stage = @identity.DiscriminateIfPoly
  let view = proposition.view()
  let origin = derived_generated_origin(
    stage,
    view.name,
    view.origin,
    derived_generated_attributes(view.origin),
  )
  (@logic.PrSymbol::new(context, view.name, origin), origin)
}

///|
fn translate_discriminated_proposition(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  kind : @logic.PropositionKind,
  proposition : @logic.PrSymbol,
  formula : @logic.Term,
  instances : ArrayView[DiscriminatedInstance],
  algebraic_types : ArrayView[@logic.Ty],
) -> Array[@theory.TheoryItem] raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  let substitutions = ordered_instance_substitutions(
    formula, instances, algebraic_types,
  )
  let result : Array[@theory.TheoryItem] = []
  for substitution in substitutions {
    let instantiated = instantiate_term(
      context,
      substitution,
      Map([]),
      formula,
      stage,
      None,
    )
    let rewritten = rewrite_discriminated_term(instantiated, instances)
    let (output_proposition, origin) = if substitutions.length() == 1 {
      (proposition, declaration.origin())
    } else {
      cloned_proposition(context, proposition)
    }
    let output = @logic.Decl::proposition(
      context,
      origin,
      kind,
      output_proposition,
      rewritten,
      None,
    ) catch {
      _ =>
        fail_transform(
          InvariantFailure,
          stage,
          "cannot rebuild a distinguished proposition",
        )
    }
    result.push(TheoryDecl(output))
  }
  result
}

///|
fn generated_parameter_item(
  context : @identity.CompilationContext,
  symbol : @logic.LSymbol,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  let declaration = @logic.Decl::parameter(
    context,
    symbol.view().origin,
    symbol,
    None,
  ) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "cannot declare a logic instance")
  }
  TheoryDecl(declaration)
}

///|
fn translate_discriminated_declaration(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  instances : ArrayView[DiscriminatedInstance],
  algebraic_types : ArrayView[@logic.Ty],
) -> Array[@theory.TheoryItem] raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  match declaration.view() {
    Dparam(symbol) => {
      let result : Array[@theory.TheoryItem] = [TheoryDecl(declaration)]
      for instance in instances {
        if instance.original == symbol {
          result.push(generated_parameter_item(context, instance.generated))
        }
      }
      result
    }
    Dprop(kind, proposition, formula) =>
      translate_discriminated_proposition(
        context, declaration, kind, proposition, formula, instances, algebraic_types,
      )
    Dlogic(_) =>
      fail_transform(
        UnsupportedStructure,
        stage,
        "logic definitions require the full distinction translation",
      )
    Dind(_, _) =>
      fail_transform(
        UnsupportedStructure,
        stage,
        "inductive declaration survived elimination",
      )
    Dtype(_) | Ddata(_) => [TheoryDecl(declaration)]
  }
}

///|
priv struct DiscriminationDeclarationCacheEntry {
  generation : Int64
  instances : Array[DiscriminatedInstance]
  algebraic_types : Array[@logic.Ty]
  output : Array[@theory.TheoryItem]
}

///|
let discrimination_declaration_cache : Ref[
  Map[@identity.DeclarationId, Array[DiscriminationDeclarationCacheEntry]],
] = Ref(Map([]))

///|
fn discrimination_instances_equal(
  left : ArrayView[DiscriminatedInstance],
  right : ArrayView[DiscriminatedInstance],
) -> Bool {
  if left.length() != right.length() {
    return false
  }
  for index, instance in left {
    let other = right[index]
    if instance.original != other.original ||
      instance.generated != other.generated ||
      instance.argument_types != other.argument_types ||
      instance.result_type != other.result_type {
      return false
    }
  }
  true
}

///|
fn translate_discriminated_declaration_cached(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  instances : ArrayView[DiscriminatedInstance],
  algebraic_types : ArrayView[@logic.Ty],
) -> Array[@theory.TheoryItem] raise TransformError {
  if declaration.view() is Dprop(Pgoal, _, _) {
    return translate_discriminated_declaration(
      context, declaration, instances, algebraic_types,
    )
  }
  let generation = current_declaration_cache_generation()
  let cache = discrimination_declaration_cache.val
  match cache.get(declaration.declaration_id()) {
    Some(entries) =>
      for entry in entries {
        if entry.generation == generation &&
          entry.algebraic_types[:] == algebraic_types &&
          discrimination_instances_equal(entry.instances, instances) {
          return entry.output
        }
      }
    None => ()
  }
  let output = translate_discriminated_declaration(
    context, declaration, instances, algebraic_types,
  )
  let entries = match cache.get(declaration.declaration_id()) {
    Some(entries) => entries.copy()
    None => []
  }
  entries.push({
    generation,
    instances: instances.to_owned(),
    algebraic_types: algebraic_types.to_owned(),
    output,
  })
  cache[declaration.declaration_id()] = entries
  discrimination_declaration_cache.val = cache
  output
}

///|
fn append_discrimination_metas(
  items : Array[@theory.TheoryItem],
  instances : ArrayView[DiscriminatedInstance],
  algebraic_types : ArrayView[@logic.Ty],
  _type_symbol_order : ArrayView[@logic.TypeSymbol],
  source_items : ArrayView[@theory.TheoryItem],
) -> Unit {
  upstream_current_algebraic_kept_types.val = algebraic_types.to_owned()
  let kept : Array[@logic.Ty] = []
  for instance in instances {
    // Why3 stores one instance under `oty_cons arguments result`, which puts
    // the result before the arguments in the ordered type-list key.
    if instance.result_type is Some(ty) && !kept.contains(ty) {
      kept.push(ty)
    }
    for ty in instance.argument_types {
      if !kept.contains(ty) {
        kept.push(ty)
      }
    }
  }
  // Algebraic metas and the later select-kept stage must see the retention
  // frontier from the preceding goal, before this goal adds its own instances.
  let previously_retained = upstream_newly_retained_kept_types.val.copy()
  upstream_prior_retained_kept_types.val = previously_retained
  let ordered_kept = order_upstream_kept_types(kept)
  let ordered_algebraic_kept = order_upstream_algebraic_kept_types(
    algebraic_types, previously_retained,
  )
  retain_upstream_kept_types(ordered_kept)
  let sorted_algebraic = algebraic_types.to_owned()
  sorted_algebraic.sort_by((left, right) => {
    compare_discriminated_algebraic_types(left, right)
  })
  for ty in ordered_algebraic_kept.rev() {
    items.push(TheoryMeta(@theory.Meta::new(b"algebraic:kept", [MetaType(ty)])))
  }
  let existing_encoding_kept : Map[@logic.Ty, Unit] = Map([])
  for item in source_items {
    if item is TheoryMeta(meta) &&
      meta.view() is { name: b"encoding:kept", arguments: [MetaType(ty)], .. } {
      existing_encoding_kept[ty] = ()
    }
  }
  for ty in ordered_kept.rev() {
    if !existing_encoding_kept.contains(ty) {
      mark_dynamic_encoding_kept(ty)
    }
    items.push(TheoryMeta(@theory.Meta::new(b"encoding:kept", [MetaType(ty)])))
  }
  for ty in sorted_algebraic.rev() {
    guard ty.view() is TyApp(type_symbol, arguments) && !arguments.is_empty() else {
      continue
    }
    let mut declaration : @logic.DataDeclaration? = None
    for item in source_items {
      guard item is TheoryDecl(source_declaration) &&
        source_declaration.view() is Ddata(data_declarations) else {
        continue
      }
      for candidate in data_declarations {
        if candidate.view().type_symbol == type_symbol {
          declaration = Some(candidate)
        }
      }
    }
    guard declaration is Some(declaration) else { continue }
    let constructors = declaration.view().constructors
    if !constructors.is_empty() {
      for projection in constructors[0].view().projections.to_owned().rev() {
        if projection is Some(projection) {
          items.push(
            TheoryMeta(
              @theory.Meta::new(b"encoding:lsinst_proj", [
                MetaLogicSymbol(projection),
                MetaType(ty),
              ]),
            ),
          )
        }
      }
    }
    for data_constructor in constructors.to_owned().rev() {
      items.push(
        TheoryMeta(
          @theory.Meta::new(b"encoding:lsinst_contr", [
            MetaLogicSymbol(data_constructor.view().symbol),
            MetaType(ty),
          ]),
        ),
      )
    }
    items.push(
      TheoryMeta(@theory.Meta::new(b"encoding:alginst", [MetaType(ty)])),
    )
  }
  for instance in instances.to_owned().rev() {
    items.push(
      TheoryMeta(
        @theory.Meta::new(b"encoding:lsinst", [
          MetaLogicSymbol(instance.original),
          MetaLogicSymbol(instance.generated),
        ]),
      ),
    )
  }
}

///|
fn discrimination_declaration_order(
  items : ArrayView[@theory.TheoryItem],
) -> (Array[@logic.TypeSymbol], Array[@logic.LSymbol]) {
  let type_symbols : Array[@logic.TypeSymbol] = []
  let logic_symbols : Array[@logic.LSymbol] = []
  for item in items {
    guard item is TheoryDecl(declaration) else { continue }
    match declaration.view() {
      Dtype(symbols) =>
        for symbol in symbols {
          if !type_symbols.contains(symbol) {
            type_symbols.push(symbol)
          }
        }
      Ddata(declarations) =>
        for data in declarations {
          let view = data.view()
          if !type_symbols.contains(view.type_symbol) {
            type_symbols.push(view.type_symbol)
          }
          for data_constructor in view.constructors {
            let data_constructor = data_constructor.view()
            if !logic_symbols.contains(data_constructor.symbol) {
              logic_symbols.push(data_constructor.symbol)
            }
            for projection in data_constructor.projections {
              if projection is Some(projection) &&
                !logic_symbols.contains(projection) {
                logic_symbols.push(projection)
              }
            }
          }
        }
      Dparam(symbol) =>
        if !logic_symbols.contains(symbol) {
          logic_symbols.push(symbol)
        }
      Dlogic(definitions) =>
        for definition in definitions {
          let symbol = definition.view().symbol
          if !logic_symbols.contains(symbol) {
            logic_symbols.push(symbol)
          }
        }
      Dind(_, declarations) =>
        for inductive in declarations {
          let symbol = inductive.view().predicate
          if !logic_symbols.contains(symbol) {
            logic_symbols.push(symbol)
          }
        }
      Dprop(_, _, _) => ()
    }
  }
  (type_symbols, logic_symbols)
}

///|
fn discrimination_algebraic_symbols(
  items : ArrayView[@theory.TheoryItem],
) -> Array[@logic.TypeSymbol] {
  let symbols : Array[@logic.TypeSymbol] = []
  for item in items {
    guard item is TheoryDecl(declaration) &&
      declaration.view() is Ddata(declarations) else {
      continue
    }
    for data in declarations {
      let symbol = data.view().type_symbol
      if !symbols.contains(symbol) {
        symbols.push(symbol)
      }
    }
  }
  symbols
}

///|
fn collect_discriminated_algebraic_types(
  term : @logic.Term,
  algebraic_symbols : ArrayView[@logic.TypeSymbol],
  types : Array[@logic.Ty],
) -> Unit {
  let visit = fn(child) {
    collect_discriminated_algebraic_types(child, algebraic_symbols, types)
  }
  let collect = fn(ty : @logic.Ty, include_nullary : Bool) {
    if ty.is_closed() &&
      ty.view() is TyApp(symbol, arguments) &&
      algebraic_symbols.contains(symbol) &&
      (include_nullary || !arguments.is_empty()) &&
      !types.contains(ty) {
      types.push(ty)
    }
  }
  match term.view() {
    Tapp(symbol, _, arguments) => {
      match symbol.view().role {
        Constructor(_) => if term.ty() is Some(ty) { collect(ty, true) }
        Projection =>
          if !arguments.is_empty() && arguments[0].ty() is Some(ty) {
            collect(ty, true)
          }
        Ordinary => ()
      }
      for argument in arguments {
        visit(argument)
      }
    }
    Tif(condition, then_branch, else_branch) => {
      visit(condition)
      visit(then_branch)
      visit(else_branch)
    }
    Tlet(_, value, body) => {
      visit(value)
      visit(body)
    }
    Tcase(scrutinee, branches) => {
      if scrutinee.ty() is Some(ty) {
        collect(ty, false)
      }
      visit(scrutinee)
      for branch in branches {
        visit(branch.view().body)
      }
    }
    Teps(_, body) => visit(body)
    Tquant(_, _, triggers, body) => {
      for group in triggers {
        for trigger in group {
          visit(trigger)
        }
      }
      visit(body)
    }
    Tbinop(_, left, right) => {
      visit(left)
      visit(right)
    }
    Tnot(inner) => visit(inner)
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => ()
  }
}

///|
fn collect_discriminated_declaration_algebraic_types(
  declaration : @logic.Decl,
  algebraic_symbols : ArrayView[@logic.TypeSymbol],
  types : Array[@logic.Ty],
) -> Unit {
  match declaration.view() {
    Dlogic(definitions) =>
      for definition in definitions {
        collect_discriminated_algebraic_types(
          definition.view().body,
          algebraic_symbols,
          types,
        )
      }
    Dind(_, declarations) =>
      for inductive in declarations {
        for case_ in inductive.view().cases {
          collect_discriminated_algebraic_types(
            case_.view().formula,
            algebraic_symbols,
            types,
          )
        }
      }
    Dprop(_, _, formula) =>
      collect_discriminated_algebraic_types(formula, algebraic_symbols, types)
    Dtype(_) | Ddata(_) | Dparam(_) => ()
  }
}

///|
pub fn discriminate_if_poly(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return task
  }
  let input = task.view().items
  guard !input.is_empty() &&
    input[input.length() - 1] is TheoryDecl(goal) &&
    goal.view() is Dprop(Pgoal, _, _) else {
    return fail_transform(InvalidTask, stage, "task has no final goal")
  }
  for item in input {
    if item is TheoryMeta(meta) &&
      (
        meta.view().name == b"encoding:lsinst" ||
        meta.view().name == b"encoding:alginst" ||
        meta.view().name == b"encoding:lsinst_proj" ||
        meta.view().name == b"encoding:lsinst_contr"
      ) {
      return fail_transform(
        UnsupportedStructure,
        stage,
        "explicit discriminate instances are outside the frozen profile",
      )
    }
  }
  let instances : Array[DiscriminatedInstance] = []
  let lsinst_scope = discrimination_selection_scope(
    input, b"select_lsinst", b"select_lsinst_default",
  )
  for item in input {
    if item is TheoryDecl(declaration) &&
      discrimination_scope_includes(lsinst_scope, declaration) {
      collect_discriminated_declaration_instances(
        context, declaration, instances,
      )
    }
  }
  let (type_symbol_order, logic_symbol_order) = discrimination_declaration_order(
    input,
  )
  let algebraic_symbols = discrimination_algebraic_symbols(input)
  let selected_types = tagged_discrimination_types(input, b"encoding:inst")
  let inst_scope = discrimination_selection_scope(
    input, b"select_inst", b"select_inst_default",
  )
  for item in input {
    if item is TheoryDecl(declaration) &&
      discrimination_scope_includes(inst_scope, declaration) {
      collect_discrimination_declaration_instance_types(
        declaration, selected_types,
      )
    }
  }
  let completed_types = completed_discrimination_instance_types(
    context, task, selected_types,
  )
  completed_types.sort_by((left, right) => {
    compare_discriminated_type(left, right, type_symbol_order)
  })
  let kept_symbols = tagged_discrimination_logic_symbols(
    input, b"encoding:lskept",
  )
  kept_symbols.sort_by((left, right) => {
    let left_rank = logic_symbol_order
      .search(left)
      .unwrap_or(logic_symbol_order.length())
    let right_rank = logic_symbol_order
      .search(right)
      .unwrap_or(logic_symbol_order.length())
    if left_rank != right_rank {
      left_rank.compare(right_rank)
    } else {
      compare_semantic_local_id(left.semantic_id(), right.semantic_id())
    }
  })
  complete_discriminated_logic_instances(
    context, kept_symbols, completed_types, instances,
  )
  instances.sort_by((left, right) => {
    compare_discriminated_instances(left, right)
  })
  let algebraic_types : Array[@logic.Ty] = []
  let alginst_scope = discrimination_selection_scope(
    input, b"select_alginst", b"select_alginst_default",
  )
  for item in input {
    if item is TheoryDecl(declaration) &&
      discrimination_scope_includes(alginst_scope, declaration) {
      collect_discriminated_declaration_algebraic_types(
        declaration, algebraic_symbols, algebraic_types,
      )
    }
  }
  let type_items : Array[@theory.TheoryItem] = []
  let other_items : Array[@theory.TheoryItem] = []
  let rewrite_propositions = tagged_discrimination_propositions(
    input, b"rewrite",
  )
  for index, item in input {
    if index + 1 == input.length() {
      continue
    }
    if item is TheoryDecl(declaration) &&
      (declaration.view() is Dtype(_) || declaration.view() is Ddata(_)) {
      type_items.push(item)
    } else if item is TheoryDecl(declaration) {
      let output = translate_discriminated_declaration_cached(
        context, declaration, instances, algebraic_types,
      )
      for translated in output {
        other_items.push(translated)
      }
      if output.length() > 1 &&
        declaration.view() is Dprop(_, proposition, _) &&
        rewrite_propositions.contains(proposition) {
        for translated in output {
          guard translated is TheoryDecl(translated_declaration) &&
            translated_declaration.view() is Dprop(_, translated_proposition, _) else {
            continue
          }
          other_items.push(
            TheoryMeta(
              @theory.Meta::new(b"rewrite", [
                MetaPropositionSymbol(translated_proposition),
              ]),
            ),
          )
        }
      }
    } else {
      other_items.push(item)
    }
  }
  append_discrimination_metas(
    other_items, instances, algebraic_types, type_symbol_order, input,
  )
  let translated_goal = translate_discriminated_declaration_cached(
    context, goal, instances, algebraic_types,
  )
  if translated_goal.length() != 1 {
    return fail_transform(
      InvariantFailure,
      stage,
      "monomorphised goal split unexpectedly",
    )
  }
  let result = type_items
  for item in other_items {
    result.push(item)
  }
  result.push(translated_goal[0])
  checked_task(task, result, stage)
}
