// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv struct SyntaxBinding {
  template : Bytes
  override_state : Int
}

///|
priv struct SyntaxMaps {
  types : Map[@identity.SemanticId, SyntaxBinding]
  logic : Map[@identity.SemanticId, SyntaxBinding]
  literals : Map[@identity.SemanticId, SyntaxBinding]
  removed_propositions : Map[@identity.SemanticId, Unit]
}

///|
fn SyntaxMaps::new() -> SyntaxMaps {
  {
    types: Map([]),
    logic: Map([]),
    literals: Map([]),
    removed_propositions: Map([]),
  }
}

///|
fn add_syntax_binding(
  entries : Map[@identity.SemanticId, SyntaxBinding],
  id : @identity.SemanticId,
  template : Bytes,
  overriding : Int64,
) -> Unit raise PrinterError {
  if overriding != 0L && overriding != 1L {
    fail_printer(InvalidSyntaxMeta, "syntax override flag must be zero or one")
  }
  let incoming = overriding.to_int()
  match entries.get(id) {
    None => entries[id] = { template, override_state: incoming }
    Some(existing) =>
      match (existing.override_state, incoming) {
        (0, 1) => entries[id] = { template, override_state: 2 }
        (1, 0) => entries[id] = { ..existing, override_state: 2 }
        _ =>
          fail_printer(
            InvalidSyntaxMeta,
            "conflicting syntax declarations for one semantic symbol",
          )
      }
  }
}

///|
fn syntax_maps(task : @theory.Task) -> SyntaxMaps raise PrinterError {
  let result = SyntaxMaps::new()
  // This first pass is Why3's Printer.get_syntax_map: collect the complete
  // driver map before interpreting any discriminate instance metadata.
  for item in task.view().items {
    guard item is TheoryMeta(meta) else { continue }
    let view = meta.view()
    match (view.name, view.arguments) {
      (
        b"syntax_type",
        [MetaTypeSymbol(symbol), MetaString(template), MetaInteger(overriding)],
      ) =>
        add_syntax_binding(
          result.types,
          symbol.semantic_id(),
          template,
          overriding,
        )
      (
        b"syntax_logic",
        [MetaLogicSymbol(symbol), MetaString(template), MetaInteger(overriding)],
      ) =>
        add_syntax_binding(
          result.logic,
          symbol.semantic_id(),
          template,
          overriding,
        )
      (
        b"syntax_literal",
        [MetaTypeSymbol(symbol), MetaString(template), MetaInteger(overriding)],
      ) =>
        add_syntax_binding(
          result.literals,
          symbol.semantic_id(),
          template,
          overriding,
        )
      (b"remove_prop", [MetaPropositionSymbol(symbol)]) =>
        result.removed_propositions[symbol.semantic_id()] = ()
      _ => ()
    }
  }
  // The SMT printer uses Discriminate.get_syntax_map rather than the base
  // printer map. Each monomorphic `encoding:lsinst` inherits the syntax of
  // its original polymorphic symbol; the original lookup deliberately uses
  // only the completed base map, matching Why3's `sm_add_ls sm0`.
  let base_logic = result.logic.copy()
  for item in task.view().items {
    guard item is TheoryMeta(meta) else { continue }
    guard meta.view()
      is {
        name: b"encoding:lsinst",
        arguments: [MetaLogicSymbol(original), MetaLogicSymbol(generated)],
      } else {
      continue
    }
    if base_logic.get(original.semantic_id()) is Some(binding) {
      result.logic[generated.semantic_id()] = binding
    }
  }
  result
}

///|
fn SyntaxMaps::type_template(
  self : SyntaxMaps,
  symbol : @logic.TypeSymbol,
) -> Bytes? {
  self.types.get(symbol.semantic_id()).map(binding => binding.template)
}

///|
fn SyntaxMaps::logic_template(
  self : SyntaxMaps,
  symbol : @logic.LSymbol,
) -> Bytes? {
  self.logic.get(symbol.semantic_id()).map(binding => binding.template)
}

///|
fn SyntaxMaps::removes(self : SyntaxMaps, symbol : @logic.PrSymbol) -> Bool {
  self.removed_propositions.contains(symbol.semantic_id())
}
