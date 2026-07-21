// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv struct UsedSymbols {
  depends : Map[@logic.PrSymbol, Map[@identity.SemanticId, Unit]]
  closure : Map[@identity.SemanticId, Array[@identity.SemanticId]]
  constants_to_remove : Map[@identity.SemanticId, Unit]
  symbols_to_keep : Map[@identity.SemanticId, Unit]
  used : Map[@identity.SemanticId, Unit]
}

///|
fn semantic_ids(
  dependencies : ArrayView[@logic.DeclDependency],
) -> Array[@identity.SemanticId] {
  [
    for dependency in dependencies => dependency.semantic_id()
  ]
}

///|
fn append_unique_ids(
  destination : Array[@identity.SemanticId],
  seen : Map[@identity.SemanticId, Unit],
  values : ArrayView[@identity.SemanticId],
) -> Unit {
  for value in values {
    if !seen.contains(value) {
      seen[value] = ()
      destination.push(value)
    }
  }
}

///|
fn declaration_ids(declaration : @logic.Decl) -> Array[@identity.SemanticId] {
  let result : Array[@identity.SemanticId] = []
  let seen : Map[@identity.SemanticId, Unit] = Map([])
  append_unique_ids(result, seen, semantic_ids(declaration.dependencies()))
  result
}

///|
fn declaration_ids_with_introduced(
  declaration : @logic.Decl,
) -> Array[@identity.SemanticId] {
  let result : Array[@identity.SemanticId] = []
  let seen : Map[@identity.SemanticId, Unit] = Map([])
  append_unique_ids(result, seen, semantic_ids(declaration.dependencies()))
  append_unique_ids(
    result,
    seen,
    semantic_ids(declaration.introduced_symbols()),
  )
  result
}

///|
fn add_used_ids(
  state : UsedSymbols,
  values : ArrayView[@identity.SemanticId],
) -> Unit {
  let queue = values.to_owned()
  let mut index = 0
  while index < queue.length() {
    let value = queue[index]
    index = index + 1
    if state.used.contains(value) {
      continue
    }
    state.used[value] = ()
    match state.closure.get(value) {
      None => ()
      Some(dependencies) => {
        state.closure.remove(value)
        for dependency in dependencies {
          if !state.used.contains(dependency) {
            queue.push(dependency)
          }
        }
      }
    }
  }
}

///|
fn any_id_used(
  used : Map[@identity.SemanticId, Unit],
  values : Map[@identity.SemanticId, Unit],
) -> Bool {
  values.keys().any(value => used.contains(value))
}

///|
fn any_dependency_used(
  state : UsedSymbols,
  dependencies : ArrayView[@logic.DeclDependency],
) -> Bool {
  dependencies.any(dependency => state.used.contains(dependency.semantic_id()))
}

///|
fn add_dependency_meta(
  state : UsedSymbols,
  proposition : @logic.PrSymbol,
  symbol : @logic.LSymbol,
) -> Unit {
  let dependencies = match state.depends.get(proposition) {
    Some(dependencies) => dependencies
    None => {
      let dependencies : Map[@identity.SemanticId, Unit] = Map([])
      state.depends[proposition] = dependencies
      dependencies
    }
  }
  dependencies[symbol.semantic_id()] = ()
}

///|
fn collect_remove_unused_metas(
  state : UsedSymbols,
  task : @theory.Task,
) -> Unit {
  for item in task.view().items {
    guard item is TheoryMeta(meta) else { continue }
    match meta.view() {
      {
        name: b"remove_unused:dependency",
        arguments: [MetaPropositionSymbol(proposition), MetaLogicSymbol(symbol)],
      } => add_dependency_meta(state, proposition, symbol)
      {
        name: b"remove_unused:remove_constant",
        arguments: [MetaLogicSymbol(symbol)],
      } => state.constants_to_remove[symbol.semantic_id()] = ()
      { name: b"remove_unused:keep", arguments: [MetaLogicSymbol(symbol)] } =>
        state.symbols_to_keep[symbol.semantic_id()] = ()
      _ => ()
    }
  }
}

///|
fn add_builtin_roots(state : UsedSymbols, task : @theory.Task) -> Unit {
  for item in task.view().items {
    guard item is TheoryDecl(declaration) else { continue }
    for dependency in declaration.introduced_symbols() {
      match dependency {
        TypeDependency(symbol) =>
          if symbol.builtin_kind() == Some(BuiltinInteger) {
            add_used_ids(state, [symbol.semantic_id()])
          }
        LogicDependency(symbol) =>
          if is_builtin_equality(symbol) {
            add_used_ids(state, [symbol.semantic_id()])
          }
        PropositionDependency(_) => ()
      }
    }
  }
}

///|
fn keep_logic_symbol(state : UsedSymbols, symbol : @logic.LSymbol) -> Bool {
  let id = symbol.semantic_id()
  state.symbols_to_keep.contains(id) ||
  (
    symbol.view().argument_types.is_empty() &&
    !state.constants_to_remove.contains(id)
  )
}

///|
fn declaration_keeps_constant(
  state : UsedSymbols,
  declaration : @logic.Decl,
) -> Bool {
  match declaration.view() {
    Dparam(symbol) => keep_logic_symbol(state, symbol)
    Dlogic(definitions) =>
      definitions.any(definition => {
        keep_logic_symbol(state, definition.view().symbol)
      })
    Dtype(_) | Ddata(_) | Dind(_) | Dprop(_, _, _) => false
  }
}

///|
fn compute_used_ids(state : UsedSymbols, task : @theory.Task) -> Unit {
  let items = task.view().items
  for reverse_index = 0
      reverse_index < items.length()
      reverse_index = reverse_index + 1 {
    let index = items.length() - reverse_index - 1
    guard items[index] is TheoryDecl(declaration) else { continue }
    match declaration.view() {
      Dprop(_, proposition, _) =>
        match state.depends.get(proposition) {
          Some(dependencies) if !any_id_used(state.used, dependencies) => {
            let ids = declaration_ids(declaration)
            ids.push(proposition.semantic_id())
            for dependency in dependencies.keys() {
              state.closure[dependency] = ids.copy()
            }
          }
          _ => {
            add_used_ids(state, declaration_ids(declaration))
            add_used_ids(state, [proposition.semantic_id()])
          }
        }
      Dtype(_) | Ddata(_) | Dparam(_) | Dlogic(_) | Dind(_) => {
        let needed = declaration_keeps_constant(state, declaration) ||
          any_dependency_used(state, declaration.introduced_symbols())
        if needed {
          add_used_ids(state, declaration_ids_with_introduced(declaration))
        }
      }
    }
  }
}

///|
fn collect_type_symbol_ids(
  ty : @logic.Ty,
  result : Map[@identity.SemanticId, Unit],
) -> Unit {
  match ty.view() {
    TyVar(_) => ()
    TyApp(symbol, arguments) => {
      result[symbol.semantic_id()] = ()
      for argument in arguments {
        collect_type_symbol_ids(argument, result)
      }
    }
  }
}

///|
fn meta_argument_kept(
  used : Map[@identity.SemanticId, Unit],
  at_least_one : Bool,
  argument : @theory.MetaArgument,
) -> Bool {
  match argument {
    MetaPropositionSymbol(symbol) => used.contains(symbol.semantic_id())
    MetaTypeSymbol(symbol) => used.contains(symbol.semantic_id())
    MetaLogicSymbol(symbol) => used.contains(symbol.semantic_id())
    MetaType(ty) => {
      let ids : Map[@identity.SemanticId, Unit] = Map([])
      collect_type_symbol_ids(ty, ids)
      if at_least_one {
        ids.keys().any(id => used.contains(id))
      } else {
        ids.keys().all(id => used.contains(id))
      }
    }
    MetaString(_) | MetaInteger(_) | MetaIdentifier(_) => true
  }
}

///|
fn meta_kept(state : UsedSymbols, meta : @theory.Meta) -> Bool {
  let view = meta.view()
  match view {
    {
      name: b"remove_unused:dependency",
      arguments: [MetaPropositionSymbol(proposition), MetaLogicSymbol(_)],
    } => state.used.contains(proposition.semantic_id())
    _ => {
      let at_least_one = view.name == b"range_type" ||
        view.name == b"float_type"
      if at_least_one {
        view.arguments.any(argument => {
          meta_argument_kept(state.used, true, argument)
        })
      } else {
        view.arguments.all(argument => {
          meta_argument_kept(state.used, false, argument)
        })
      }
    }
  }
}

///|
fn declaration_kept(state : UsedSymbols, declaration : @logic.Decl) -> Bool {
  match declaration.view() {
    Dprop(_, proposition, _) => state.used.contains(proposition.semantic_id())
    Dtype(_) | Ddata(_) | Dparam(_) | Dlogic(_) | Dind(_) =>
      declaration
      .introduced_symbols()
      .any(dependency => state.used.contains(dependency.semantic_id()))
  }
}

///|
pub fn remove_unused_keep_constants(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.RemoveUnusedKeepConstants
  require_task_context(context, task, stage)
  let state : UsedSymbols = {
    depends: Map([]),
    closure: Map([]),
    constants_to_remove: Map([]),
    symbols_to_keep: Map([]),
    used: Map([]),
  }
  add_builtin_roots(state, task)
  collect_remove_unused_metas(state, task)
  compute_used_ids(state, task)
  let result : Array[@theory.TheoryItem] = []
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) =>
        if declaration_kept(state, declaration) {
          result.push(item)
        }
      TheoryMeta(meta) => if meta_kept(state, meta) { result.push(item) }
      TheoryUse(_) | TheoryClone(_) => result.push(item)
    }
  }
  checked_task(task.context_anchor(), result, stage)
}
