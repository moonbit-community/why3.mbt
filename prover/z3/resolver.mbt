// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum ResolvedDriverSymbol {
  ResolvedType(@logic.TypeSymbol)
  ResolvedLogic(@logic.LSymbol)
  ResolvedProposition(@logic.PrSymbol)
}

///|
struct DriverSymbolResolver {
  anchor : @identity.SemanticId
  entries : Map[@identity.SourceSymbolKey, ResolvedDriverSymbol]
  ordered_keys : Array[@identity.SourceSymbolKey]
}

///|
fn resolved_semantic_id(symbol : ResolvedDriverSymbol) -> @identity.SemanticId {
  match symbol {
    ResolvedType(value) => value.semantic_id()
    ResolvedLogic(value) => value.semantic_id()
    ResolvedProposition(value) => value.semantic_id()
  }
}

///|
fn resolved_kind(symbol : ResolvedDriverSymbol) -> @identity.SourceSymbolKind {
  match symbol {
    ResolvedType(_) => Type
    ResolvedLogic(_) => Logic
    ResolvedProposition(_) => Proposition
  }
}

///|
fn build_driver_symbol_resolver(
  anchor : @identity.SemanticId,
  entries : ArrayView[(@identity.SourceSymbolKey, ResolvedDriverSymbol)],
) -> DriverSymbolResolver raise BindError {
  let table : Map[@identity.SourceSymbolKey, ResolvedDriverSymbol] = Map([])
  let ordered_keys : Array[@identity.SourceSymbolKey] = []
  for index, entry in entries {
    let (key, symbol) = entry
    let path = "$.resolver[" + index.to_string() + "]"
    if table.contains(key) {
      fail_bind(InvalidProfile, path, "duplicate resolver entry")
    }
    if !anchor.same_context(resolved_semantic_id(symbol)) {
      fail_bind(
        ContextMismatch,
        path,
        "resolver symbol belongs to another context",
      )
    }
    if key.view().symbol_kind != resolved_kind(symbol) {
      fail_bind(
        SymbolKindMismatch,
        path,
        "resolver key kind disagrees with symbol",
      )
    }
    table[key] = symbol
    ordered_keys.push(key)
  }
  { anchor, entries: table, ordered_keys }
}

///|
/// Binds the pinned driver locators to symbols reconstructed from original
/// Why3 source. The caller resolves each entry by its exact
/// theory/item/inner locator; this boundary checks context and symbol kind.
pub fn DriverSymbolResolver::from_source(
  anchor : @identity.SemanticId,
  entries : ArrayView[(@identity.SourceSymbolKey, ResolvedDriverSymbol)],
) -> DriverSymbolResolver raise BindError {
  build_driver_symbol_resolver(anchor, entries)
}

///|
pub fn DriverSymbolResolver::context_anchor(
  self : DriverSymbolResolver,
) -> @identity.SemanticId {
  self.anchor
}

///|
fn same_locator(
  left : @identity.SourceSymbolKey,
  right : @identity.SourceSymbolKey,
) -> Bool {
  let left = left.view()
  let right = right.view()
  left.theory_key == right.theory_key &&
  left.theory_item_ordinal == right.theory_item_ordinal &&
  left.declaration_inner_ordinal == right.declaration_inner_ordinal
}

///|
fn DriverSymbolResolver::resolve(
  self : DriverSymbolResolver,
  key : @identity.SourceSymbolKey,
  path : String,
) -> ResolvedDriverSymbol raise BindError {
  match self.entries.get(key) {
    Some(symbol) => symbol
    None => {
      for expected in self.ordered_keys {
        if same_locator(expected, key) {
          if expected.view().symbol_kind != key.view().symbol_kind {
            fail_bind(SymbolKindMismatch, path, "source symbol kind differs")
          }
          fail_bind(SymbolDigestMismatch, path, "source symbol digest differs")
        }
      }
      fail_bind(MissingSymbol, path, "source symbol is absent from resolver")
    }
  }
}

///|
pub fn DriverSymbolResolver::resolve_type(
  self : DriverSymbolResolver,
  key : @identity.SourceSymbolKey,
  path? : String = "$.symbol",
) -> @logic.TypeSymbol raise BindError {
  match self.resolve(key, path) {
    ResolvedType(symbol) => symbol
    _ => fail_bind(SymbolKindMismatch, path, "expected a type symbol")
  }
}

///|
pub fn DriverSymbolResolver::resolve_logic(
  self : DriverSymbolResolver,
  key : @identity.SourceSymbolKey,
  path? : String = "$.symbol",
) -> @logic.LSymbol raise BindError {
  match self.resolve(key, path) {
    ResolvedLogic(symbol) => symbol
    _ => fail_bind(SymbolKindMismatch, path, "expected a logic symbol")
  }
}

///|
pub fn DriverSymbolResolver::resolve_proposition(
  self : DriverSymbolResolver,
  key : @identity.SourceSymbolKey,
  path? : String = "$.symbol",
) -> @logic.PrSymbol raise BindError {
  match self.resolve(key, path) {
    ResolvedProposition(symbol) => symbol
    _ => fail_bind(SymbolKindMismatch, path, "expected a proposition symbol")
  }
}

///|
fn append_unbound_ty_keys(
  ty : UnboundTy,
  seen : Map[@identity.SourceSymbolKey, Unit],
  result : Array[@identity.SourceSymbolKey],
) -> Unit {
  match ty {
    UnboundTyVariable(_) => ()
    UnboundTyApplication(symbol, arguments) => {
      if !seen.contains(symbol) {
        seen[symbol] = ()
        result.push(symbol)
      }
      for argument in arguments {
        append_unbound_ty_keys(argument, seen, result)
      }
    }
  }
}

///|
fn append_meta_argument_keys(
  argument : UnboundMetaArgument,
  seen : Map[@identity.SourceSymbolKey, Unit],
  result : Array[@identity.SourceSymbolKey],
) -> Unit {
  match argument {
    UnboundMetaType(ty) => append_unbound_ty_keys(ty, seen, result)
    UnboundMetaTypeSymbol(key)
    | UnboundMetaLogicSymbol(key)
    | UnboundMetaPropositionSymbol(key) =>
      if !seen.contains(key) {
        seen[key] = ()
        result.push(key)
      }
    UnboundMetaString(_) | UnboundMetaInteger(_) | UnboundMetaIdentifier(_) =>
      ()
  }
}

///|
pub fn Z3StaticSpec::required_keys(
  self : Z3StaticSpec,
) -> Array[@identity.SourceSymbolKey] {
  let seen : Map[@identity.SourceSymbolKey, Unit] = Map([])
  let result : Array[@identity.SourceSymbolKey] = []
  for groups in [self.meta_groups, self.theory_meta_groups] {
    for group in groups {
      for meta in group.entries {
        for argument in meta.arguments {
          append_meta_argument_keys(argument, seen, result)
        }
      }
    }
  }
  result
}
