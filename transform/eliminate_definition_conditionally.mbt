// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn task_has_meta(task : @theory.Task, name : BytesView) -> Bool {
  task.view().items.any(item => {
    item is TheoryMeta(meta) && meta.view().name[:] == name
  })
}

///|
fn rewrite_definition_symbols(task : @theory.Task) -> Map[@logic.LSymbol, Unit] {
  let result : Map[@logic.LSymbol, Unit] = Map([])
  for item in task.view().items {
    if item is TheoryMeta(meta) &&
      meta.view()
      is { name: b"rewrite_def", arguments: [MetaLogicSymbol(symbol)], .. } {
      result[symbol] = ()
    }
  }
  result
}

///|
fn task_equality_symbol(task : @theory.Task) -> @logic.LSymbol? {
  for item in task.view().items {
    guard item is TheoryDecl(declaration) else { continue }
    for dependency in declaration.introduced_symbols() {
      if dependency is LogicDependency(symbol) && is_builtin_equality(symbol) {
        return Some(symbol)
      }
    }
  }
  None
}

///|
fn open_definition_pattern(
  context : @identity.CompilationContext,
  pattern : @logic.Pattern,
  body : @logic.Term,
) -> (@logic.Pattern, @logic.Term) raise TransformError {
  let stage = @identity.EliminateDefinitionConditionally
  let values : Map[@logic.VSymbol, @logic.Term] = Map([])
  for variable in pattern.bound_variables() {
    let replacement = open_definition_binder(
      context, variable, "cannot open case-pattern binder",
    )
    values[variable] = @logic.Term::variable(replacement)
  }
  let substitution = @logic.TySubstitution::new()
  (
    instantiate_pattern(substitution, values, pattern, stage),
    instantiate_term(context, substitution, values, body, stage, None),
  )
}

///|
fn open_definition_binder(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  failure_message : String,
) -> @logic.VSymbol raise TransformError {
  let stage = @identity.EliminateDefinitionConditionally
  let view = variable.view()
  let origin = derived_generated_origin(
    stage,
    view.name,
    view.origin,
    derived_generated_attributes(view.origin),
  )
  variable.clone_identifier_with_origin(context, origin, None) catch {
    _ => fail_transform(InvariantFailure, stage, failure_message)
  }
}

///|
fn definition_relation(
  context : @identity.CompilationContext,
  head : @logic.Term,
  body : @logic.Term,
  equality : @logic.LSymbol?,
) -> @logic.Term raise TransformError {
  let stage = @identity.EliminateDefinitionConditionally
  let recurse = fn(child) -> @logic.Term raise TransformError {
    definition_relation(context, head, child, equality)
  }
  match body.view() {
    Tif(condition, then_branch, else_branch) =>
      @logic.Term::if_then_else(
        condition,
        recurse(then_branch),
        recurse(else_branch),
        None,
      ) catch {
        _ => fail_transform(InvariantFailure, stage, "invalid definition if")
      }
    Tlet(variable, value, inner) => {
      let opened = open_definition_binder(
        context, variable, "cannot open definition let binder",
      )
      let values : Map[@logic.VSymbol, @logic.Term] = Map([])
      values[variable] = @logic.Term::variable(opened)
      let opened_inner = instantiate_term(
        context,
        @logic.TySubstitution::new(),
        values,
        inner,
        stage,
        None,
      )
      @logic.Term::let_in(opened, value, recurse(opened_inner), None) catch {
        _ => fail_transform(InvariantFailure, stage, "invalid definition let")
      }
    }
    Tcase(scrutinee, branches) => {
      let mapped = [
        for branch in branches => {
          let view = branch.view()
          let (pattern, branch_body) = open_definition_pattern(
            context,
            view.pattern,
            view.body,
          )
          (pattern, recurse(branch_body))
        }
      ]
      @logic.Term::case(scrutinee, mapped, None) catch {
        _ => fail_transform(InvariantFailure, stage, "invalid definition case")
      }
    }
    _ =>
      if body.is_formula() {
        binary_simplified(Iff, head, body, stage)
      } else {
        guard equality is Some(equality) else {
          return fail_transform(
            InvariantFailure,
            stage,
            "task has no builtin equality symbol",
          )
        }
        match equality_simplified(head, body) {
          Some(result) => result
          None =>
            @logic.Term::elaborated_apply(equality, [head, body], None, None) catch {
              _ =>
                fail_transform(
                  InvariantFailure,
                  stage,
                  "invalid definition equality",
                )
            }
        }
      }
  }
}

///|
fn definition_axiom(
  context : @identity.CompilationContext,
  definition : @logic.LogicDefinition,
  equality : @logic.LSymbol?,
) -> (@logic.PrSymbol, @theory.TheoryItem) raise TransformError {
  let stage = @identity.EliminateDefinitionConditionally
  let view = definition.view()
  let symbol_view = view.symbol.view()
  let parameters : Array[@logic.VSymbol] = []
  let values : Map[@logic.VSymbol, @logic.Term] = Map([])
  for parameter in view.parameters {
    let opened = open_definition_binder(
      context, parameter, "cannot open definition parameters",
    )
    parameters.push(opened)
    values[parameter] = @logic.Term::variable(opened)
  }
  let body = instantiate_term(
    context,
    @logic.TySubstitution::new(),
    values,
    view.body,
    stage,
    None,
  )
  let arguments = [
    for parameter in parameters => @logic.Term::variable(parameter)
  ]
  let head = @logic.Term::elaborated_apply(
    view.symbol,
    arguments,
    view.body.ty(),
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "invalid definition head")
  }
  let relation = definition_relation(context, head, body, equality)
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    parameters,
    [],
    relation,
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "invalid definition axiom")
  }
  let name = symbol_view.name + b"'def"
  let origin = derived_generated_origin(
    stage,
    name,
    symbol_view.origin,
    derived_generated_attributes(symbol_view.origin),
  )
  let proposition = @logic.PrSymbol::new(context, name, origin)
  let declaration = @logic.Decl::proposition(
    context,
    origin,
    Paxiom,
    proposition,
    formula,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "invalid definition axiom declaration",
      )
  }
  (proposition, TheoryDecl(declaration))
}

///|
fn definition_parameter(
  context : @identity.CompilationContext,
  symbol : @logic.LSymbol,
) -> @theory.TheoryItem raise TransformError {
  TheoryDecl(
    @logic.Decl::parameter(context, symbol.view().origin, symbol, None),
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateDefinitionConditionally,
        "invalid abstracted definition parameter",
      )
  }
}

///|
fn retained_definition_group(
  context : @identity.CompilationContext,
  origin : @identity.Origin,
  definitions : ArrayView[@logic.LogicDefinition],
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.EliminateDefinitionConditionally
  let declaration = @logic.Decl::logic(context, origin, definitions, None) catch {
    _ => fail_transform(InvariantFailure, stage, "invalid definition group")
  }
  TheoryDecl(declaration)
}

///|
fn eliminate_definition_group(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  definitions : ArrayView[@logic.LogicDefinition],
  eliminate_all : Bool,
  eliminate_constants : Bool,
  eliminate_recursion : Bool,
  rewrite : Map[@logic.LSymbol, Unit],
  equality : @logic.LSymbol?,
) -> Array[@theory.TheoryItem] raise TransformError {
  let recursive_group = eliminate_recursion &&
    (
      definitions.length() > 1 ||
      (
        definitions.length() == 1 &&
        definitions[0].view().body.contains_logic_symbol(
          definitions[0].view().symbol,
        )
      )
    )
  let abstracted : Array[@logic.LogicDefinition] = []
  let retained : Array[@logic.LogicDefinition] = []
  for definition in definitions {
    if eliminate_all ||
      recursive_group ||
      (
        eliminate_constants &&
        definition.view().symbol.view().argument_types.is_empty()
      ) {
      abstracted.push(definition)
    } else {
      retained.push(definition)
    }
  }
  if abstracted.is_empty() {
    return [TheoryDecl(declaration)]
  }
  let result : Array[@theory.TheoryItem] = []
  for definition in abstracted {
    result.push(definition_parameter(context, definition.view().symbol))
  }
  if !retained.is_empty() {
    result.push(
      retained_definition_group(context, declaration.origin(), retained),
    )
  }
  let rewrites : Array[@theory.TheoryItem] = []
  for definition in abstracted {
    let (proposition, axiom) = definition_axiom(context, definition, equality)
    result.push(axiom)
    if rewrite.contains(definition.view().symbol) {
      rewrites.push(
        TheoryMeta(
          @theory.Meta::new(b"rewrite", [MetaPropositionSymbol(proposition)]),
        ),
      )
    }
  }
  for item in rewrites {
    result.push(item)
  }
  result
}

///|
/// Why3's declaration transformers memoize their result by declaration. The
/// same source declaration is shared by every split goal, so retaining the
/// transformed declaration also retains the exact identifier-clone observer
/// behavior across goals.
priv struct EliminateDefinitionCacheEntry {
  generation : Int64
  persistent : Bool
  eliminate_all : Bool
  eliminate_constants : Bool
  eliminate_recursion : Bool
  rewrite_signature : Array[Bool]
  equality : @logic.LSymbol?
  output : Array[@theory.TheoryItem]
}

///|
let eliminate_definition_cache : Ref[
  Map[@identity.DeclarationId, Array[EliminateDefinitionCacheEntry]],
] = Ref(Map([]))

///|
fn eliminate_definition_rewrite_signature(
  definitions : ArrayView[@logic.LogicDefinition],
  rewrite : Map[@logic.LSymbol, Unit],
) -> Array[Bool] {
  [
    for definition in definitions => rewrite.contains(definition.view().symbol)
  ]
}

///|
fn eliminate_definition_group_cached(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  definitions : ArrayView[@logic.LogicDefinition],
  eliminate_all : Bool,
  eliminate_constants : Bool,
  eliminate_recursion : Bool,
  rewrite : Map[@logic.LSymbol, Unit],
  equality : @logic.LSymbol?,
) -> Array[@theory.TheoryItem] raise TransformError {
  guard !definitions.is_empty() else {
    return eliminate_definition_group(
      context, declaration, definitions, eliminate_all, eliminate_constants, eliminate_recursion,
      rewrite, equality,
    )
  }
  let key = declaration.declaration_id()
  let signature = eliminate_definition_rewrite_signature(definitions, rewrite)
  let generation = current_declaration_cache_generation()
  let persistent = declaration_cache_is_persistent(declaration)
  let cache = eliminate_definition_cache.val
  match cache.get(key) {
    Some(entries) =>
      for entry in entries {
        let live = if entry.persistent {
          persistent
        } else {
          !persistent && entry.generation == generation
        }
        if live &&
          entry.eliminate_all == eliminate_all &&
          entry.eliminate_constants == eliminate_constants &&
          entry.eliminate_recursion == eliminate_recursion &&
          entry.rewrite_signature == signature &&
          entry.equality == equality {
          return entry.output
        }
      }
    None => ()
  }
  let output = eliminate_definition_group(
    context, declaration, definitions, eliminate_all, eliminate_constants, eliminate_recursion,
    rewrite, equality,
  )
  if persistent {
    for item in output {
      if item is TheoryDecl(output_declaration) {
        declaration_cache_retain(output_declaration)
      }
    }
  }
  let entries = match cache.get(key) {
    Some(entries) => entries.copy()
    None => []
  }
  entries.push({
    generation,
    persistent,
    eliminate_all,
    eliminate_constants,
    eliminate_recursion,
    rewrite_signature: signature,
    equality,
    output,
  })
  cache[key] = entries
  eliminate_definition_cache.val = cache
  output
}

///|
pub fn eliminate_definition_conditionally(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.EliminateDefinitionConditionally
  require_task_context(context, task, stage)
  let monomorphic = task_has_meta(task, b"encoding:monomorphic_only")
  let counterexample = task_has_meta(task, b"get_counterexmp")
  let rewrite = rewrite_definition_symbols(task)
  let equality = task_equality_symbol(task)
  let result : Array[@theory.TheoryItem] = []
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) =>
        match declaration.view() {
          Dlogic(definitions) =>
            for
              mapped in eliminate_definition_group_cached(
                context,
                declaration,
                definitions,
                !monomorphic,
                monomorphic && counterexample,
                monomorphic,
                rewrite,
                equality,
              ) {
              result.push(mapped)
            }
          _ => result.push(item)
        }
      TheoryUse(_) | TheoryClone(_) | TheoryMeta(_) => result.push(item)
    }
  }
  checked_task(task, result, stage)
}
