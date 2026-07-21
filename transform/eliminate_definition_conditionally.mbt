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
      is { name: b"rewrite_def", arguments: [MetaLogicSymbol(symbol)] } {
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
fn definition_relation(
  head : @logic.Term,
  body : @logic.Term,
  equality : @logic.LSymbol?,
) -> @logic.Term raise TransformError {
  let stage = @identity.EliminateDefinitionConditionally
  let recurse = fn(child) -> @logic.Term raise TransformError {
    definition_relation(head, child, equality)
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
    Tlet(variable, value, inner) =>
      @logic.Term::let_in(variable, value, recurse(inner), None) catch {
        _ => fail_transform(InvariantFailure, stage, "invalid definition let")
      }
    Tcase(scrutinee, branches) => {
      let mapped = [
        for branch in branches => {
          let view = branch.view()
          (view.pattern, recurse(view.body))
        }
      ]
      @logic.Term::trusted_case(scrutinee, mapped, None) catch {
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
  let arguments = [
    for parameter in view.parameters => @logic.Term::variable(parameter)
  ]
  let head = @logic.Term::elaborated_apply(
    view.symbol,
    arguments,
    view.body.ty(),
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "invalid definition head")
  }
  let relation = definition_relation(head, view.body, equality)
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    view.parameters,
    [],
    relation,
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "invalid definition axiom")
  }
  let name = symbol_view.name + b"'def"
  let origin = @identity.Origin::generated(
    stage,
    name,
    derived_generated_span(symbol_view.origin),
    symbol_view.origin.attributes(),
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
  let declaration = match origin.kind().view() {
    SnapshotKind =>
      @logic.Decl::trusted_logic(context, origin, definitions, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "invalid trusted definition group",
          )
      }
    UserKind | GeneratedKind(_) =>
      @logic.Decl::logic(context, origin, definitions, None) catch {
        _ => fail_transform(InvariantFailure, stage, "invalid definition group")
      }
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
              mapped in eliminate_definition_group(
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
  checked_task(task.context_anchor(), result, stage)
}
