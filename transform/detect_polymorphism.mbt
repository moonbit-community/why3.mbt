// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv struct PolymorphismExceptions {
  type_symbols : Map[@logic.TypeSymbol, Unit]
  logic_symbols : Map[@logic.LSymbol, Unit]
  propositions : Map[@logic.PrSymbol, Unit]
}

///|
fn collect_polymorphism_exceptions(
  task : @theory.Task,
) -> PolymorphismExceptions {
  let exceptions : PolymorphismExceptions = {
    type_symbols: Map([]),
    logic_symbols: Map([]),
    propositions: Map([]),
  }
  for item in task.view().items {
    guard item is TheoryMeta(meta) else { continue }
    match meta.view() {
      {
        name: b"encoding:ignore_polymorphism_ts",
        arguments: [MetaTypeSymbol(symbol)],
      } => exceptions.type_symbols[symbol] = ()
      {
        name: b"encoding:ignore_polymorphism_ls",
        arguments: [MetaLogicSymbol(symbol)],
      } => exceptions.logic_symbols[symbol] = ()
      {
        name: b"encoding:ignore_polymorphism_pr",
        arguments: [MetaPropositionSymbol(symbol)],
      } => exceptions.propositions[symbol] = ()
      _ => ()
    }
  }
  exceptions
}

///|
fn polymorphic_type_symbol(
  exceptions : PolymorphismExceptions,
  symbol : @logic.TypeSymbol,
) -> Bool {
  let view = symbol.view()
  !exceptions.type_symbols.contains(symbol) &&
  !view.parameters.is_empty() &&
  view.definition is NoDef
}

///|
fn polymorphic_logic_symbol(
  exceptions : PolymorphismExceptions,
  symbol : @logic.LSymbol,
) -> Bool {
  !exceptions.logic_symbols.contains(symbol) &&
  !symbol.view().type_parameters.is_empty()
}

///|
fn declaration_is_polymorphic(
  exceptions : PolymorphismExceptions,
  declaration : @logic.Decl,
) -> Bool {
  match declaration.view() {
    Dtype(symbols) =>
      symbols.any(symbol => polymorphic_type_symbol(exceptions, symbol))
    Ddata(declarations) =>
      declarations.any(declaration => {
        polymorphic_type_symbol(exceptions, declaration.view().type_symbol)
      })
    Dparam(symbol) => polymorphic_logic_symbol(exceptions, symbol)
    Dlogic(definitions) =>
      definitions.any(definition => {
        polymorphic_logic_symbol(exceptions, definition.view().symbol)
      })
    Dind(declarations) =>
      declarations.any(declaration => {
        polymorphic_logic_symbol(exceptions, declaration.view().predicate)
      })
    Dprop(_, proposition, formula) =>
      !exceptions.propositions.contains(proposition) &&
      !formula.free_type_variables().is_empty()
  }
}

///|
pub fn detect_polymorphism(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.DetectPolymorphism
  require_task_context(context, task, stage)
  let exceptions = collect_polymorphism_exceptions(task)
  if task.view().items.any(item => {
      item is TheoryDecl(declaration) &&
      declaration_is_polymorphic(exceptions, declaration)
    }) {
    return task
  }
  let items = task.view().items.to_owned()
  let monomorphic = @theory.TheoryMeta(
    @theory.Meta::new(b"encoding:monomorphic_only", []),
  )
  guard !items.is_empty() else {
    return checked_task(task.context_anchor(), items, stage)
  }
  items.insert(items.length() - 1, monomorphic)
  checked_task(task.context_anchor(), items, stage)
}
