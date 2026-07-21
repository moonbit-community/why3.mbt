// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv struct BuiltinRemoval {
  abstract_logic : Map[@logic.LSymbol, Unit]
  remove_propositions : Map[@logic.PrSymbol, Unit]
  remove_logic : Map[@logic.LSymbol, Unit]
  remove_definitions : Map[@logic.LSymbol, Unit]
  remove_types : Map[@logic.TypeSymbol, Unit]
}

///|
fn builtin_removal(task : @theory.Task) -> BuiltinRemoval {
  let abstract_logic : Map[@logic.LSymbol, Unit] = Map([])
  let remove_propositions : Map[@logic.PrSymbol, Unit] = Map([])
  let remove_logic : Map[@logic.LSymbol, Unit] = Map([])
  let remove_definitions : Map[@logic.LSymbol, Unit] = Map([])
  let remove_types : Map[@logic.TypeSymbol, Unit] = Map([])
  for item in task.view().items {
    guard item is TheoryMeta(meta) else { continue }
    match meta.view() {
      { name: b"syntax_logic", arguments: [MetaLogicSymbol(symbol), ..] } =>
        abstract_logic[symbol] = ()
      { name: b"remove_prop", arguments: [MetaPropositionSymbol(symbol)] } =>
        remove_propositions[symbol] = ()
      { name: b"remove_logic", arguments: [MetaLogicSymbol(symbol)] } =>
        remove_logic[symbol] = ()
      { name: b"remove_def", arguments: [MetaLogicSymbol(symbol)] } =>
        remove_definitions[symbol] = ()
      { name: b"remove_type", arguments: [MetaTypeSymbol(symbol)] } =>
        remove_types[symbol] = ()
      _ => ()
    }
  }
  {
    abstract_logic,
    remove_propositions,
    remove_logic,
    remove_definitions,
    remove_types,
  }
}

///|
fn parameter_item(
  context : @identity.CompilationContext,
  symbol : @logic.LSymbol,
) -> @theory.TheoryItem raise TransformError {
  TheoryDecl(
    @logic.Decl::parameter(context, symbol.view().origin, symbol, None),
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateBuiltin,
        "cannot abstract a builtin definition",
      )
  }
}

///|
fn logic_item(
  context : @identity.CompilationContext,
  definitions : ArrayView[@logic.LogicDefinition],
) -> @theory.TheoryItem raise TransformError {
  guard !definitions.is_empty() else {
    return fail_transform(
      InvariantFailure,
      @identity.EliminateBuiltin,
      "empty retained logic declaration",
    )
  }
  let origin = definitions[0].view().symbol.view().origin
  let declaration = match origin.kind().view() {
    SnapshotKind =>
      @logic.Decl::trusted_logic(context, origin, definitions, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.EliminateBuiltin,
            "cannot retain trusted logic definitions",
          )
      }
    UserKind | GeneratedKind(_) =>
      @logic.Decl::logic(context, origin, definitions, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.EliminateBuiltin,
            "cannot retain logic definitions",
          )
      }
  }
  TheoryDecl(declaration)
}

///|
fn type_item(
  context : @identity.CompilationContext,
  symbols : ArrayView[@logic.TypeSymbol],
) -> @theory.TheoryItem raise TransformError {
  guard !symbols.is_empty() else {
    return fail_transform(
      InvariantFailure,
      @identity.EliminateBuiltin,
      "empty retained type declaration",
    )
  }
  let origin = symbols[0].view().origin
  let declaration = match origin.kind().view() {
    SnapshotKind =>
      @logic.Decl::trusted_type_declaration(context, origin, symbols, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.EliminateBuiltin,
            "cannot retain trusted type declaration",
          )
      }
    UserKind | GeneratedKind(_) =>
      @logic.Decl::type_declaration(context, origin, symbols, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            @identity.EliminateBuiltin,
            "cannot retain type declaration",
          )
      }
  }
  TheoryDecl(declaration)
}

///|
fn data_item(
  context : @identity.CompilationContext,
  declarations : ArrayView[@logic.DataDeclaration],
) -> @theory.TheoryItem raise TransformError {
  guard !declarations.is_empty() else {
    return fail_transform(
      InvariantFailure,
      @identity.EliminateBuiltin,
      "empty retained data declaration",
    )
  }
  let origin = declarations[0].view().type_symbol.view().origin
  TheoryDecl(@logic.Decl::trusted_data(context, origin, declarations, None)) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateBuiltin,
        "cannot retain trusted data declaration",
      )
  }
}

///|
fn inductive_item(
  context : @identity.CompilationContext,
  declarations : ArrayView[@logic.InductiveDeclaration],
) -> @theory.TheoryItem raise TransformError {
  guard !declarations.is_empty() else {
    return fail_transform(
      InvariantFailure,
      @identity.EliminateBuiltin,
      "empty retained inductive declaration",
    )
  }
  let origin = declarations[0].view().predicate.view().origin
  TheoryDecl(
    @logic.Decl::trusted_inductive(context, origin, declarations, None),
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.EliminateBuiltin,
        "cannot retain trusted inductive declaration",
      )
  }
}

///|
fn eliminate_builtin_declaration(
  context : @identity.CompilationContext,
  removal : BuiltinRemoval,
  declaration : @logic.Decl,
) -> Array[@theory.TheoryItem] raise TransformError {
  match declaration.view() {
    Dlogic(definitions) => {
      let abstracted : Array[@logic.LSymbol] = []
      let retained : Array[@logic.LogicDefinition] = []
      for definition in definitions {
        let symbol = definition.view().symbol
        if removal.remove_logic.contains(symbol) {
          continue
        }
        if removal.abstract_logic.contains(symbol) ||
          removal.remove_definitions.contains(symbol) {
          abstracted.push(symbol)
        } else {
          retained.push(definition)
        }
      }
      let result : Array[@theory.TheoryItem] = []
      for symbol in abstracted {
        result.push(parameter_item(context, symbol))
      }
      if !retained.is_empty() {
        result.push(logic_item(context, retained))
      }
      result
    }
    Dind(declarations) => {
      let abstracted : Array[@logic.LSymbol] = []
      let retained : Array[@logic.InductiveDeclaration] = []
      for declaration in declarations {
        let predicate = declaration.view().predicate
        if removal.remove_logic.contains(predicate) {
          continue
        }
        if removal.abstract_logic.contains(predicate) ||
          removal.remove_definitions.contains(predicate) {
          abstracted.push(predicate)
        } else {
          retained.push(declaration)
        }
      }
      let result : Array[@theory.TheoryItem] = []
      for symbol in abstracted {
        result.push(parameter_item(context, symbol))
      }
      if !retained.is_empty() {
        result.push(inductive_item(context, retained))
      }
      result
    }
    Dprop(Paxiom, proposition, _) if removal.remove_propositions.contains(
        proposition,
      ) => []
    Dtype(symbols) => {
      let retained : Array[@logic.TypeSymbol] = []
      for symbol in symbols {
        if !removal.remove_types.contains(symbol) {
          retained.push(symbol)
        }
      }
      if retained.is_empty() {
        []
      } else {
        [type_item(context, retained)]
      }
    }
    Ddata(declarations) => {
      let retained : Array[@logic.DataDeclaration] = []
      for data in declarations {
        if !removal.remove_types.contains(data.view().type_symbol) {
          retained.push(data)
        }
      }
      if retained.is_empty() {
        []
      } else {
        [data_item(context, retained)]
      }
    }
    Dparam(_) | Dprop(_, _, _) => [TheoryDecl(declaration)]
  }
}

///|
pub fn eliminate_builtin(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.EliminateBuiltin
  require_task_context(context, task, stage)
  let removal = builtin_removal(task)
  let result : Array[@theory.TheoryItem] = []
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) =>
        for
          mapped in eliminate_builtin_declaration(context, removal, declaration) {
          result.push(mapped)
        }
      TheoryUse(_) | TheoryClone(_) | TheoryMeta(_) => result.push(item)
    }
  }
  checked_task(task.context_anchor(), result, stage)
}
