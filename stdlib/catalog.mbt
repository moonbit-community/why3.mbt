// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum DriverSymbol {
  DriverType(@logic.TypeSymbol)
  DriverLogic(@logic.LSymbol)
  DriverProposition(@logic.PrSymbol)
  DriverProgramType(@mlw.ProgramTypeSymbol)
  DriverRoutine(@mlw.RoutineSymbol)
}

///|
struct DriverSymbolCatalog {
  anchor : @identity.SemanticId
  entries : Map[@identity.SnapshotSymbolKey, DriverSymbol]
  ordered_keys : Array[@identity.SnapshotSymbolKey]
  locator_keys : Map[String, @identity.SnapshotSymbolKey]
}

///|
fn DriverSymbol::semantic_id(self : DriverSymbol) -> @identity.SemanticId {
  match self {
    DriverType(symbol) => symbol.semantic_id()
    DriverLogic(symbol) => symbol.semantic_id()
    DriverProposition(symbol) => symbol.semantic_id()
    DriverProgramType(symbol) => symbol.semantic_id()
    DriverRoutine(symbol) => symbol.semantic_id()
  }
}

///|
fn DriverSymbol::origin(self : DriverSymbol) -> @identity.Origin {
  match self {
    DriverType(symbol) => symbol.origin()
    DriverLogic(symbol) => symbol.view().origin
    DriverProposition(symbol) => symbol.view().origin
    DriverProgramType(symbol) => symbol.view().origin
    DriverRoutine(symbol) => symbol.view().origin
  }
}

///|
fn DriverSymbol::snapshot_kind(
  self : DriverSymbol,
) -> @identity.SnapshotSymbolKind {
  match self {
    DriverType(_) => Type
    DriverLogic(_) => Logic
    DriverProposition(_) => Proposition
    DriverProgramType(_) | DriverRoutine(_) => Program
  }
}

///|
fn DriverSymbolCatalog::new(
  anchor : @identity.SemanticId,
) -> DriverSymbolCatalog {
  { anchor, entries: Map([]), ordered_keys: [], locator_keys: Map([]) }
}

///|
fn DriverSymbolCatalog::insert(
  self : DriverSymbolCatalog,
  key : @identity.SnapshotSymbolKey,
  locator : String,
  symbol : DriverSymbol,
  path : String,
) -> Unit raise SnapshotError {
  if self.entries.contains(key) || self.locator_keys.contains(locator) {
    fail_snapshot(
      DuplicateCatalogEntry,
      path,
      "duplicate snapshot catalog key or locator",
    )
  }
  if !self.anchor.same_context(symbol.semantic_id()) {
    fail_snapshot(
      SemanticInvariantFailure,
      path,
      "catalog symbol belongs to a different compilation context",
    )
  }
  if key.view().symbol_kind != symbol.snapshot_kind() {
    fail_snapshot(
      SemanticInvariantFailure,
      path,
      "catalog descriptor kind disagrees with its typed symbol",
    )
  }
  match symbol.origin().view() {
    SnapshotOrigin(_, origin_key, _) =>
      if origin_key != key {
        fail_snapshot(
          SemanticInvariantFailure,
          path,
          "catalog symbol origin does not match its descriptor key",
        )
      }
    _ =>
      fail_snapshot(
        SemanticInvariantFailure,
        path,
        "catalog symbol lacks snapshot provenance",
      )
  }
  self.entries[key] = symbol
  self.ordered_keys.push(key)
  self.locator_keys[locator] = key
}

///|
pub fn DriverSymbolCatalog::context_anchor(
  self : DriverSymbolCatalog,
) -> @identity.SemanticId {
  self.anchor
}

///|
pub fn DriverSymbolCatalog::length(self : DriverSymbolCatalog) -> Int {
  self.ordered_keys.length()
}

///|
pub fn DriverSymbolCatalog::keys(
  self : DriverSymbolCatalog,
) -> ArrayView[@identity.SnapshotSymbolKey] {
  self.ordered_keys[:]
}

///|
pub fn DriverSymbolCatalog::validate_context(
  self : DriverSymbolCatalog,
  context : @identity.CompilationContext,
) -> Unit raise BindError {
  if !context.contains(self.anchor) {
    fail_bind(
      CatalogContextMismatch,
      "driver catalog belongs to a different compilation context",
    )
  }
}

///|
fn same_key_without_digest(
  left : @identity.SnapshotSymbolKey,
  right : @identity.SnapshotSymbolKey,
) -> Bool {
  let left = left.view()
  let right = right.view()
  left.theory_key == right.theory_key &&
  left.theory_item_ordinal == right.theory_item_ordinal &&
  left.declaration_inner_ordinal == right.declaration_inner_ordinal &&
  left.symbol_kind == right.symbol_kind
}

///|
fn DriverSymbolCatalog::resolve(
  self : DriverSymbolCatalog,
  key : @identity.SnapshotSymbolKey,
) -> DriverSymbol raise BindError {
  match self.entries.get(key) {
    Some(symbol) => symbol
    None => {
      for expected in self.ordered_keys {
        if same_key_without_digest(expected, key) {
          fail_bind(
            SymbolDigestMismatch,
            "snapshot symbol digest differs from the frozen catalog",
          )
        }
      }
      fail_bind(MissingSymbol, "snapshot symbol key is absent from the catalog")
    }
  }
}

///|
/// Resolves one frozen entry without narrowing its semantic kind. Profile
/// binding normally uses the typed methods below; this view supports eager
/// whole-catalog validation.
pub fn DriverSymbolCatalog::resolve_symbol(
  self : DriverSymbolCatalog,
  key : @identity.SnapshotSymbolKey,
) -> DriverSymbol raise BindError {
  self.resolve(key)
}

///|
pub fn DriverSymbolCatalog::resolve_type(
  self : DriverSymbolCatalog,
  key : @identity.SnapshotSymbolKey,
) -> @logic.TypeSymbol raise BindError {
  match self.resolve(key) {
    DriverType(symbol) => symbol
    _ =>
      fail_bind(SymbolKindMismatch, "catalog entry is not a logic type symbol")
  }
}

///|
pub fn DriverSymbolCatalog::resolve_logic(
  self : DriverSymbolCatalog,
  key : @identity.SnapshotSymbolKey,
) -> @logic.LSymbol raise BindError {
  match self.resolve(key) {
    DriverLogic(symbol) => symbol
    _ => fail_bind(SymbolKindMismatch, "catalog entry is not a logic symbol")
  }
}

///|
pub fn DriverSymbolCatalog::resolve_proposition(
  self : DriverSymbolCatalog,
  key : @identity.SnapshotSymbolKey,
) -> @logic.PrSymbol raise BindError {
  match self.resolve(key) {
    DriverProposition(symbol) => symbol
    _ =>
      fail_bind(SymbolKindMismatch, "catalog entry is not a proposition symbol")
  }
}

///|
pub fn DriverSymbolCatalog::resolve_program_type(
  self : DriverSymbolCatalog,
  key : @identity.SnapshotSymbolKey,
) -> @mlw.ProgramTypeSymbol raise BindError {
  match self.resolve(key) {
    DriverProgramType(symbol) => symbol
    _ =>
      fail_bind(
        SymbolKindMismatch,
        "catalog entry is not a program type symbol",
      )
  }
}

///|
pub fn DriverSymbolCatalog::resolve_routine(
  self : DriverSymbolCatalog,
  key : @identity.SnapshotSymbolKey,
) -> @mlw.RoutineSymbol raise BindError {
  match self.resolve(key) {
    DriverRoutine(symbol) => symbol
    _ => fail_bind(SymbolKindMismatch, "catalog entry is not a routine symbol")
  }
}
