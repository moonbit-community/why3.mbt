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
  entries : Map[@identity.SnapshotSymbolKey, ResolvedDriverSymbol]
  ordered_keys : Array[@identity.SnapshotSymbolKey]
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
fn resolved_origin(symbol : ResolvedDriverSymbol) -> @identity.Origin {
  match symbol {
    ResolvedType(value) => value.origin()
    ResolvedLogic(value) => value.view().origin
    ResolvedProposition(value) => value.view().origin
  }
}

///|
fn resolved_kind(symbol : ResolvedDriverSymbol) -> @identity.SnapshotSymbolKind {
  match symbol {
    ResolvedType(_) => Type
    ResolvedLogic(_) => Logic
    ResolvedProposition(_) => Proposition
  }
}

///|
pub fn DriverSymbolResolver::new(
  anchor : @identity.SemanticId,
  entries : ArrayView[(@identity.SnapshotSymbolKey, ResolvedDriverSymbol)],
) -> DriverSymbolResolver raise BindError {
  let table : Map[@identity.SnapshotSymbolKey, ResolvedDriverSymbol] = Map([])
  let ordered_keys : Array[@identity.SnapshotSymbolKey] = []
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
    match resolved_origin(symbol).view() {
      SnapshotOrigin(_, origin_key, _) =>
        if origin_key != key {
          fail_bind(
            SymbolDigestMismatch,
            path,
            "resolver symbol origin key differs",
          )
        }
      _ =>
        fail_bind(InvalidProfile, path, "resolver symbol lacks snapshot origin")
    }
    table[key] = symbol
    ordered_keys.push(key)
  }
  { anchor, entries: table, ordered_keys }
}

///|
pub fn DriverSymbolResolver::context_anchor(
  self : DriverSymbolResolver,
) -> @identity.SemanticId {
  self.anchor
}

///|
fn same_locator(
  left : @identity.SnapshotSymbolKey,
  right : @identity.SnapshotSymbolKey,
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
  key : @identity.SnapshotSymbolKey,
  path : String,
) -> ResolvedDriverSymbol raise BindError {
  match self.entries.get(key) {
    Some(symbol) => symbol
    None => {
      for expected in self.ordered_keys {
        if same_locator(expected, key) {
          if expected.view().symbol_kind != key.view().symbol_kind {
            fail_bind(SymbolKindMismatch, path, "snapshot symbol kind differs")
          }
          fail_bind(
            SymbolDigestMismatch,
            path,
            "snapshot symbol digest differs",
          )
        }
      }
      fail_bind(MissingSymbol, path, "snapshot symbol is absent from resolver")
    }
  }
}

///|
pub fn DriverSymbolResolver::resolve_type(
  self : DriverSymbolResolver,
  key : @identity.SnapshotSymbolKey,
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
  key : @identity.SnapshotSymbolKey,
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
  key : @identity.SnapshotSymbolKey,
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
  seen : Map[@identity.SnapshotSymbolKey, Unit],
  result : Array[@identity.SnapshotSymbolKey],
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
  seen : Map[@identity.SnapshotSymbolKey, Unit],
  result : Array[@identity.SnapshotSymbolKey],
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
) -> Array[@identity.SnapshotSymbolKey] {
  let seen : Map[@identity.SnapshotSymbolKey, Unit] = Map([])
  let result : Array[@identity.SnapshotSymbolKey] = []
  for groups in [self.meta_groups, self.snapshot_meta_groups] {
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
