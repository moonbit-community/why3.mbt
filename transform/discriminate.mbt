// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn monomorphised_goal_type(
  context : @identity.CompilationContext,
  variable : @logic.TyVarSymbol,
) -> (@logic.TypeSymbol, @logic.Ty) raise TransformError {
  let stage = @identity.DiscriminateMonomorphiseGoal
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
  let formula = instantiate_term(context, substitution, Map([]), formula, stage)
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
  checked_task(task.context_anchor(), result, stage)
}

///|
priv struct DiscriminatedInstance {
  original : @logic.LSymbol
  generated : @logic.LSymbol
  argument_types : Array[@logic.Ty]
  result_type : @logic.Ty?
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
fn compare_discriminated_type_lists(
  left : ArrayView[@logic.Ty],
  right : ArrayView[@logic.Ty],
  type_symbol_order : ArrayView[@logic.TypeSymbol],
) -> Int {
  let shared = if left.length() < right.length() {
    left.length()
  } else {
    right.length()
  }
  for index = 0; index < shared; index = index + 1 {
    let order = compare_discriminated_type(
      left[index],
      right[index],
      type_symbol_order,
    )
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
  logic_symbol_order : ArrayView[@logic.LSymbol],
  type_symbol_order : ArrayView[@logic.TypeSymbol],
) -> Int {
  let left_rank = logic_symbol_order
    .search(left.original)
    .unwrap_or(logic_symbol_order.length())
  let right_rank = logic_symbol_order
    .search(right.original)
    .unwrap_or(logic_symbol_order.length())
  let symbol_order = if left_rank < right_rank {
    -1
  } else if left_rank > right_rank {
    1
  } else {
    compare_semantic_local_id(
      left.original.semantic_id(),
      right.original.semantic_id(),
    )
  }
  if symbol_order != 0 {
    return symbol_order
  }
  compare_discriminated_type_lists(
    discriminated_signature(left),
    discriminated_signature(right),
    type_symbol_order,
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
fn make_discriminated_symbol(
  context : @identity.CompilationContext,
  original : @logic.LSymbol,
  argument_types : ArrayView[@logic.Ty],
  result_type : @logic.Ty?,
) -> @logic.LSymbol raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  let view = original.view()
  let origin = @identity.Origin::generated(
    stage,
    view.name,
    derived_generated_span(view.origin),
    view.origin.attributes(),
  )
  match result_type {
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
    Tcase(_, _) =>
      fail_transform(
        UnsupportedStructure,
        stage,
        "compile_match input requires the full discriminate implementation",
      )
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
  substitutions : Array[@logic.TySubstitution],
) -> Unit raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  let visit = fn(child) -> Unit raise TransformError {
    collect_instance_substitutions(child, instances, substitutions)
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
    Tcase(_, _) =>
      fail_transform(
        UnsupportedStructure,
        stage,
        "case survived discriminate compile_match",
      )
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
) -> Array[@logic.TySubstitution] raise TransformError {
  let substitutions = [@logic.TySubstitution::new()]
  collect_instance_substitutions(formula, instances, substitutions)
  if substitutions.length() <= 1 {
    return substitutions
  }
  let nonempty : Array[@logic.TySubstitution] = []
  for substitution in substitutions {
    if !substitution.is_empty() {
      nonempty.push(substitution)
    }
  }
  nonempty.rev_in_place()
  for substitution in substitutions {
    if substitution.is_empty() {
      nonempty.push(substitution)
    }
  }
  nonempty
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
  let origin = @identity.Origin::generated(
    stage,
    view.name,
    derived_generated_span(view.origin),
    view.origin.attributes(),
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
) -> Array[@theory.TheoryItem] raise TransformError {
  let stage = @identity.DiscriminateIfPoly
  let substitutions = ordered_instance_substitutions(formula, instances)
  let result : Array[@theory.TheoryItem] = []
  for substitution in substitutions {
    let instantiated = instantiate_term(
      context,
      substitution,
      Map([]),
      formula,
      stage,
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
        context, declaration, kind, proposition, formula, instances,
      )
    Dlogic(_) =>
      fail_transform(
        UnsupportedStructure,
        stage,
        "logic definitions require the full distinction translation",
      )
    Dind(_) =>
      fail_transform(
        UnsupportedStructure,
        stage,
        "inductive declaration survived elimination",
      )
    Dtype(_) | Ddata(_) => [TheoryDecl(declaration)]
  }
}

///|
fn append_discrimination_metas(
  items : Array[@theory.TheoryItem],
  instances : ArrayView[DiscriminatedInstance],
  algebraic_types : ArrayView[@logic.Ty],
  type_symbol_order : ArrayView[@logic.TypeSymbol],
) -> Unit {
  let kept : Array[@logic.Ty] = []
  for instance in instances {
    for ty in instance.argument_types {
      if !kept.contains(ty) {
        kept.push(ty)
      }
    }
  }
  kept.sort_by((left, right) => {
    compare_discriminated_type(left, right, type_symbol_order)
  })
  let sorted_algebraic = algebraic_types.to_owned()
  sorted_algebraic.sort_by((left, right) => {
    compare_discriminated_type(left, right, type_symbol_order)
  })
  for ty in sorted_algebraic.rev() {
    items.push(TheoryMeta(@theory.Meta::new(b"algebraic:kept", [MetaType(ty)])))
  }
  for ty in kept.rev() {
    items.push(TheoryMeta(@theory.Meta::new(b"encoding:kept", [MetaType(ty)])))
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
      Dind(declarations) =>
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
fn collect_discriminated_algebraic_types(
  term : @logic.Term,
  types : Array[@logic.Ty],
) -> Unit {
  let visit = fn(child) { collect_discriminated_algebraic_types(child, types) }
  match term.view() {
    Tapp(symbol, _, arguments) => {
      match symbol.view().role {
        Constructor(_) =>
          if term.ty() is Some(ty) && ty.is_closed() && !types.contains(ty) {
            types.push(ty)
          }
        Projection =>
          if !arguments.is_empty() &&
            arguments[0].ty() is Some(ty) &&
            ty.is_closed() &&
            !types.contains(ty) {
            types.push(ty)
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
      if scrutinee.ty() is Some(ty) && ty.is_closed() && !types.contains(ty) {
        types.push(ty)
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
    goal.view() is Dprop(Pgoal, _, goal_formula) else {
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
  collect_discriminated_instances(context, goal_formula, instances)
  if instances.is_empty() {
    return fail_transform(
      UnsupportedStructure,
      stage,
      "polymorphic task produced no closed goal instance",
    )
  }
  let (type_symbol_order, logic_symbol_order) = discrimination_declaration_order(
    input,
  )
  instances.sort_by((left, right) => {
    compare_discriminated_instances(
      left, right, logic_symbol_order, type_symbol_order,
    )
  })
  let algebraic_types : Array[@logic.Ty] = []
  collect_discriminated_algebraic_types(goal_formula, algebraic_types)
  let type_items : Array[@theory.TheoryItem] = []
  let other_items : Array[@theory.TheoryItem] = []
  for index, item in input {
    if index + 1 == input.length() {
      continue
    }
    if item is TheoryDecl(declaration) &&
      (declaration.view() is Dtype(_) || declaration.view() is Ddata(_)) {
      type_items.push(item)
    } else if item is TheoryDecl(declaration) {
      for
        output in translate_discriminated_declaration(
          context, declaration, instances,
        ) {
        other_items.push(output)
      }
    } else {
      other_items.push(item)
    }
  }
  append_discrimination_metas(
    other_items, instances, algebraic_types, type_symbol_order,
  )
  let translated_goal = translate_discriminated_declaration(
    context, goal, instances,
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
  checked_task(task.context_anchor(), result, stage)
}
