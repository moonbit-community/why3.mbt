// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
pub(all) enum TheoryItem {
  TheoryDecl(@logic.Decl)
  TheoryUse(TheoryKey)
  TheoryClone(CloneWitness)
  TheoryMeta(Meta)
}

///|
struct Theory {
  anchor : @identity.SemanticId
  key : TheoryKey
  name : SemanticName
  items : Array[TheoryItem]
  export_namespace : Namespace
  known : @logic.KnownMap
  local_symbols : Map[@identity.SemanticId, Unit]
  used_theories : Array[(TheoryKey, Theory)]
  clone_sources : Array[(TheoryKey, Theory)]
  range_projections : Map[@logic.TypeSymbol, @logic.LSymbol]
  float_projections : Map[@logic.TypeSymbol, (@logic.LSymbol, @logic.LSymbol)]
  coercions : CoercionMap
  proved_wf : Map[@logic.LSymbol, (@logic.PrSymbol, @logic.LSymbol)]
}

///|
pub(all) struct TheoryView {
  key : TheoryKey
  name : SemanticName
  items : ArrayView[TheoryItem]
  tdecls : Array[TDecl]
  export_namespace : Namespace
}

///|
struct TheoryBuilder {
  context : @identity.CompilationContext
  anchor : @identity.SemanticId
  key : TheoryKey
  name : SemanticName
  items : Array[TheoryItem]
  mut import_namespaces : Array[Namespace]
  mut export_namespaces : Array[Namespace]
  mut scope_names : Array[Bytes]
  mut known : @logic.KnownMap
  local_symbols : Map[@identity.SemanticId, Unit]
  used_theories : Array[(TheoryKey, Theory)]
  clone_sources : Array[(TheoryKey, Theory)]
  mut range_projections : Map[@logic.TypeSymbol, @logic.LSymbol]
  mut float_projections : Map[
    @logic.TypeSymbol,
    (@logic.LSymbol, @logic.LSymbol),
  ]
  mut coercions : CoercionMap
  mut proved_wf : Map[@logic.LSymbol, (@logic.PrSymbol, @logic.LSymbol)]
  mut closed : Bool
}

///|
pub fn Theory::context_anchor(self : Theory) -> @identity.SemanticId {
  self.anchor
}

///|
pub fn Theory::key(self : Theory) -> TheoryKey {
  self.key
}

///|
pub fn Theory::view(self : Theory) -> TheoryView {
  {
    key: self.key,
    name: self.name,
    items: self.items[:],
    tdecls: self.items.map(TDecl::from_item),
    export_namespace: self.export_namespace,
  }
}

///|
pub fn Theory::tdecls(self : Theory) -> Array[TDecl] {
  self.items.map(TDecl::from_item)
}

///|
pub fn Theory::export_namespace(self : Theory) -> Namespace {
  self.export_namespace
}

///|
/// Completed declaration environment used to validate and interpret terms
/// against this theory.
pub fn Theory::known_map(self : Theory) -> @logic.KnownMap {
  self.known
}

///|
/// The transitive `use` closure retained by a completed theory.
pub fn Theory::used_theories(self : Theory) -> Array[Theory] {
  self.used_theories.map(entry => entry.1)
}

///|
pub fn Theory::range_projection(
  self : Theory,
  symbol : @logic.TypeSymbol,
) -> @logic.LSymbol? {
  self.range_projections.get(symbol)
}

///|
pub fn Theory::float_projections(
  self : Theory,
  symbol : @logic.TypeSymbol,
) -> (@logic.LSymbol, @logic.LSymbol)? {
  self.float_projections.get(symbol)
}

///|
pub fn Theory::coercions(self : Theory) -> CoercionMap {
  self.coercions
}

///|
pub fn TheoryBuilder::current_coercions(self : TheoryBuilder) -> CoercionMap {
  self.coercions
}

///|
pub fn Theory::proved_wf(
  self : Theory,
  relation : @logic.LSymbol,
) -> (@logic.PrSymbol, @logic.LSymbol)? {
  self.proved_wf.get(relation)
}

///|
/// Returns the same immutable theory with additional declarations appended in
/// order.  VC generation uses this after program elaboration: the projected
/// pure theory is already closed, while generated goals must still precede
/// task splitting without rebuilding or re-resolving its imported theories.
pub fn Theory::append_declarations(
  self : Theory,
  context : @identity.CompilationContext,
  declarations : ArrayView[@logic.Decl],
  span : @identity.SourceSpan?,
) -> Theory raise {
  if !context.contains(self.anchor) {
    fail_theory(
      ContextMismatch,
      span,
      "theory and appended declarations belong to different contexts",
    )
  }
  let items = self.items.copy()
  let mut export_namespace = self.export_namespace
  let mut known = self.known
  let local_symbols = self.local_symbols.copy()
  for declaration in declarations {
    for introduced in declaration.introduced_symbols() {
      require_same_id(self.anchor, introduced.semantic_id(), span)
    }
    known = known.add(declaration, span)
    for introduced in declaration.introduced_symbols() {
      local_symbols[introduced.semantic_id()] = ()
    }
    export_namespace = export_namespace.add_declaration_symbols(
      declaration, span,
    )
    items.push(TheoryDecl(declaration))
  }
  { ..self, items, export_namespace, known, local_symbols }
}

///|
fn CloneWitness::shift_source_item_identity(
  self : CloneWitness,
  offset : Int,
) -> CloneWitness {
  if offset == 0 {
    return self
  }
  {
    ..self,
    source_item_identity: self.source_item_identity +
    offset.reinterpret_as_uint(),
  }
}

///|
/// Inserts generated declarations at absolute boundaries in the original
/// theory item stream. Delayed program VC generation uses the boundary map
/// returned by the pure clone pass to recover Why3's eager `clone_pdecl`
/// ordering without changing the elaborated program module.
pub fn Theory::insert_declarations_at_item_boundaries(
  self : Theory,
  context : @identity.CompilationContext,
  insertions : ArrayView[(Int, Array[Bytes], Array[@logic.Decl])],
  span : @identity.SourceSpan?,
) -> Theory raise {
  if insertions.is_empty() {
    return self
  }
  if !context.contains(self.anchor) {
    fail_theory(
      ContextMismatch,
      span,
      "theory and inserted declarations belong to different contexts",
    )
  }
  let matched = Array::make(insertions.length(), false)
  for index, insertion in insertions {
    if insertion.0 < 0 || insertion.0 > self.items.length() {
      fail_theory(
        InvalidTheoryItem,
        span,
        "inserted declaration boundary is outside the theory",
      )
    }
    for previous = 0; previous < index; previous = previous + 1 {
      if insertions[previous].0 == insertion.0 &&
        insertions[previous].1 == insertion.1 {
        fail_theory(
          InvalidTheoryItem,
          span,
          "two declaration groups target the same theory boundary and scope",
        )
      }
    }
  }
  let items : Array[TheoryItem] = []
  let mut export_namespace = self.export_namespace
  let mut known = self.known
  let local_symbols = self.local_symbols.copy()
  let mut inserted_count = 0
  for item_index, item in self.items {
    for insertion_index, insertion in insertions {
      if insertion.0 != item_index {
        continue
      }
      for declaration in insertion.2 {
        for introduced in declaration.introduced_symbols() {
          require_same_id(self.anchor, introduced.semantic_id(), span)
        }
        known = known.add(declaration, span)
        for introduced in declaration.introduced_symbols() {
          local_symbols[introduced.semantic_id()] = ()
        }
        export_namespace = export_namespace.add_declaration_symbols_at_path(
          insertion.1,
          declaration,
          span,
        )
        items.push(TheoryDecl(declaration))
        inserted_count = inserted_count + 1
      }
      matched[insertion_index] = true
    }
    match item {
      TheoryClone(witness) =>
        items.push(
          TheoryClone(witness.shift_source_item_identity(inserted_count)),
        )
      _ => items.push(item)
    }
  }
  for insertion_index, insertion in insertions {
    if insertion.0 == self.items.length() {
      for declaration in insertion.2 {
        for introduced in declaration.introduced_symbols() {
          require_same_id(self.anchor, introduced.semantic_id(), span)
        }
        known = known.add(declaration, span)
        for introduced in declaration.introduced_symbols() {
          local_symbols[introduced.semantic_id()] = ()
        }
        export_namespace = export_namespace.add_declaration_symbols_at_path(
          insertion.1,
          declaration,
          span,
        )
        items.push(TheoryDecl(declaration))
      }
      matched[insertion_index] = true
    }
  }
  for was_matched in matched {
    if !was_matched {
      fail_theory(
        InvalidTheoryItem,
        span,
        "inserted declarations target an absent theory boundary",
      )
    }
  }
  { ..self, items, export_namespace, known, local_symbols }
}

///|
/// Adds a dependency to a completed theory without exposing its namespace or
/// emitting a `use` item. VC generation uses this for the `int.Int` and
/// `why3.WellFounded.WellFounded` support theories that Why3 loads from its
/// environment independently of the source module.
pub fn Theory::append_hidden_use(
  self : Theory,
  context : @identity.CompilationContext,
  used : Theory,
  span : @identity.SourceSpan?,
) -> Theory raise {
  if !context.contains(self.anchor) {
    fail_theory(
      ContextMismatch,
      span,
      "theory and hidden dependency belong to different contexts",
    )
  }
  require_same_id(self.anchor, used.anchor, span)
  for entry in self.used_theories {
    if entry.0 == used.key {
      if entry.1.anchor != used.anchor {
        fail_theory(
          InvalidTheoryItem,
          span,
          "theory key resolves to two different hidden dependencies",
        )
      }
      return self
    }
  }
  let used_theories = self.used_theories.copy()
  used_theories.push((used.key, used))
  let clone_sources = self.clone_sources.copy()
  if !clone_sources.any(entry => entry.0 == used.key) {
    clone_sources.push((used.key, used))
  }
  {
    ..self,
    known: self.known.merge(used.known, span),
    used_theories,
    clone_sources,
    range_projections: merge_range_projections(
      self.range_projections,
      used.range_projections,
      span,
    ),
    float_projections: merge_float_projections(
      self.float_projections,
      used.float_projections,
      span,
    ),
    coercions: self.coercions.union(used.coercions, span),
    proved_wf: merge_proved_wf(self.proved_wf, used.proved_wf, span),
  }
}

///|
pub fn TheoryBuilder::new(
  context : @identity.CompilationContext,
  key : TheoryKey,
  name : SemanticName,
) -> TheoryBuilder {
  {
    context,
    anchor: context.fresh_id(),
    key,
    name,
    items: [],
    import_namespaces: [Namespace::empty()],
    export_namespaces: [Namespace::empty()],
    scope_names: [],
    known: @logic.KnownMap::new(context),
    local_symbols: Map([]),
    used_theories: [],
    clone_sources: [],
    range_projections: Map([]),
    float_projections: Map([]),
    coercions: CoercionMap::empty(),
    proved_wf: Map([]),
    closed: false,
  }
}

///|
/// Current visible namespace, including inherited and imported scope entries.
pub fn TheoryBuilder::current_namespace(self : TheoryBuilder) -> Namespace {
  self.import_namespaces[self.import_namespaces.length() - 1]
}

///|
/// Current declaration environment used by the delayed source typer for
/// datatype constructors, projections, and record layout.
pub fn TheoryBuilder::current_known(self : TheoryBuilder) -> @logic.KnownMap {
  self.known
}

///|
/// Reports whether every declaration introduced locally by `used` is already
/// reachable through the builder's known map, including through transitive
/// theory uses.
pub fn TheoryBuilder::knows_theory(self : TheoryBuilder, used : Theory) -> Bool {
  for item in used.items {
    if item is TheoryDecl(declaration) {
      for introduced in declaration.introduced_symbols() {
        if !self.known.contains(introduced) {
          return false
        }
      }
    }
  }
  true
}

///|
pub fn TheoryBuilder::item_count(self : TheoryBuilder) -> Int {
  self.items.length()
}

///|
pub fn TheoryBuilder::item_at(
  self : TheoryBuilder,
  index : Int,
  span : @identity.SourceSpan?,
) -> TheoryItem raise TheoryError {
  if index < 0 || index >= self.items.length() {
    fail_theory(
      InvalidTheoryItem,
      span,
      "theory builder item index is out of bounds",
    )
  }
  self.items[index]
}

///|
/// Current visible namespace. Kept as the compatibility accessor used by the
/// program-module builder while its projected pure theory is under construction.
pub fn TheoryBuilder::export_namespace(self : TheoryBuilder) -> Namespace {
  self.current_namespace()
}

///|
fn TheoryBuilder::require_open(
  self : TheoryBuilder,
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  if self.closed {
    fail_theory(BuilderSealed, span, "theory builder has already been closed")
  }
}

///|
fn Namespace::add_declaration_symbols(
  self : Namespace,
  declaration : @logic.Decl,
  span : @identity.SourceSpan?,
) -> Namespace raise TheoryError {
  let mut result = self
  for introduced in declaration.introduced_symbols() {
    match introduced {
      TypeDependency(symbol) =>
        result = result.add_type(symbol.name(), symbol, span)
      LogicDependency(symbol) => {
        let view = symbol.view()
        result = result.add_logic(view.name, symbol, span)
      }
      PropositionDependency(symbol) => {
        let view = symbol.view()
        result = result.add_proposition(view.name, symbol, span)
      }
    }
  }
  result
}

///|
fn Namespace::add_declaration_symbols_at_path(
  self : Namespace,
  path : ArrayView[Bytes],
  declaration : @logic.Decl,
  span : @identity.SourceSpan?,
) -> Namespace raise TheoryError {
  if path.is_empty() {
    return self.add_declaration_symbols(declaration, span)
  }
  let subspaces = self.subspaces.copy()
  for index, entry in subspaces {
    let (name, nested) = entry
    if name == path[0] {
      subspaces[index] = (
        name,
        nested.add_declaration_symbols_at_path(path[1:], declaration, span),
      )
      return { ..self, subspaces, }
    }
  }
  fail_theory(
    UnboundName,
    span,
    "inserted declaration targets an unknown namespace scope",
  )
}

///|
fn TheoryBuilder::replace_current_namespaces(
  self : TheoryBuilder,
  imported : Namespace,
  exported : Namespace,
) -> Unit {
  let index = self.import_namespaces.length() - 1
  self.import_namespaces[index] = imported
  self.export_namespaces[index] = exported
}

///|
fn TheoryBuilder::register_used_theory(
  self : TheoryBuilder,
  used : Theory,
) -> Unit {
  if self.used_theories.any(entry => entry.0 == used.key) {
    return
  }
  for entry in used.used_theories {
    self.register_used_theory(entry.1)
  }
  self.used_theories.push((used.key, used))
}

///|
fn TheoryBuilder::register_clone_source(
  self : TheoryBuilder,
  source : Theory,
) -> Unit {
  if !self.clone_sources.any(entry => entry.0 == source.key) {
    self.clone_sources.push((source.key, source))
  }
}

///|
fn merge_range_projections(
  current : Map[@logic.TypeSymbol, @logic.LSymbol],
  imported : Map[@logic.TypeSymbol, @logic.LSymbol],
  span : @identity.SourceSpan?,
) -> Map[@logic.TypeSymbol, @logic.LSymbol] raise TheoryError {
  let result = current.copy()
  for symbol, projection in imported {
    match result.get(symbol) {
      Some(existing) =>
        if existing != projection {
          fail_theory(
            RangeConflict,
            span,
            "range type has conflicting projection metadata",
          )
        }
      None => result[symbol] = projection
    }
  }
  result
}

///|
fn merge_float_projections(
  current : Map[@logic.TypeSymbol, (@logic.LSymbol, @logic.LSymbol)],
  imported : Map[@logic.TypeSymbol, (@logic.LSymbol, @logic.LSymbol)],
  span : @identity.SourceSpan?,
) -> Map[@logic.TypeSymbol, (@logic.LSymbol, @logic.LSymbol)] raise TheoryError {
  let result = current.copy()
  for symbol, projections in imported {
    match result.get(symbol) {
      Some(existing) =>
        if existing != projections {
          fail_theory(
            FloatConflict,
            span,
            "float type has conflicting projection metadata",
          )
        }
      None => result[symbol] = projections
    }
  }
  result
}

///|
fn apply_derived_meta(
  range_projections : Map[@logic.TypeSymbol, @logic.LSymbol],
  float_projections : Map[@logic.TypeSymbol, (@logic.LSymbol, @logic.LSymbol)],
  coercions : CoercionMap,
  meta : Meta,
  span : @identity.SourceSpan?,
) -> (
  Map[@logic.TypeSymbol, @logic.LSymbol],
  Map[@logic.TypeSymbol, (@logic.LSymbol, @logic.LSymbol)],
  CoercionMap,
) raise TheoryError {
  let view = meta.view()
  match (view.name, view.arguments) {
    (b"range_type", [MetaTypeSymbol(symbol), MetaLogicSymbol(projection)]) => {
      let ranges : Map[@logic.TypeSymbol, @logic.LSymbol] = Map([
        (symbol, projection),
      ])
      (
        merge_range_projections(range_projections, ranges, span),
        float_projections,
        coercions.add(projection, span),
      )
    }
    (
      b"float_type",
      [
        MetaTypeSymbol(symbol),
        MetaLogicSymbol(projection),
        MetaLogicSymbol(finiteness),
      ],
    ) => {
      let floats : Map[@logic.TypeSymbol, (@logic.LSymbol, @logic.LSymbol)] = Map([
          (symbol, (projection, finiteness)),
        ],
      )
      (
        range_projections,
        merge_float_projections(float_projections, floats, span),
        coercions.add(projection, span),
      )
    }
    (b"coercion", [MetaLogicSymbol(function_)]) =>
      (range_projections, float_projections, coercions.add(function_, span))
    (b"range_type", _) | (b"float_type", _) | (b"coercion", _) =>
      fail_theory(MetaTypeMismatch, span, "builtin meta has invalid arguments")
    _ => (range_projections, float_projections, coercions)
  }
}

///|
pub fn TheoryBuilder::add_decl(
  self : TheoryBuilder,
  declaration : @logic.Decl,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  for introduced in declaration.introduced_symbols() {
    require_same_id(self.anchor, introduced.semantic_id(), span)
  }
  self.known = self.known.add(declaration, span)
  for introduced in declaration.introduced_symbols() {
    self.local_symbols[introduced.semantic_id()] = ()
  }
  let exported = self.export_namespaces[self.export_namespaces.length() - 1].add_declaration_symbols(
    declaration, span,
  )
  let imported = self.current_namespace().overlay(exported)
  self.replace_current_namespaces(imported, exported)
  self.items.push(TheoryDecl(declaration))
}

///|
pub fn TheoryBuilder::add_use(
  self : TheoryBuilder,
  used : Theory,
  import_ : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  require_same_id(self.anchor, used.anchor, span)
  let already_used = self.used_theories.any(entry => entry.0 == used.key)
  if !already_used {
    self.known = self.known.merge(used.known, span)
    self.register_used_theory(used)
  }
  let current_import = self.current_namespace()
  let current_export = self.export_namespaces[self.export_namespaces.length() -
    1]
  if import_ {
    let exported = current_export.merge(used.export_namespace, span)
    self.replace_current_namespaces(current_import.overlay(exported), exported)
  } else {
    let exported = current_export.add_subspace(
      used.key.view().name,
      used.export_namespace,
      span,
    )
    self.replace_current_namespaces(current_import.overlay(exported), exported)
  }
  self.range_projections = merge_range_projections(
    self.range_projections,
    used.range_projections,
    span,
  )
  self.float_projections = merge_float_projections(
    self.float_projections,
    used.float_projections,
    span,
  )
  self.coercions = self.coercions.union(used.coercions, span)
  self.proved_wf = merge_proved_wf(self.proved_wf, used.proved_wf, span)
  if !already_used {
    self.items.push(TheoryUse(used.key))
  }
}

///|
/// Adds a semantic dependency without exposing its namespace. Why3 uses this
/// path for declarations that mention built-in higher-order symbols: the
/// dependency must be present in declaration history and the known map, while
/// `(->)` remains absent from the enclosing theory's exported namespace.
pub fn TheoryBuilder::add_hidden_use(
  self : TheoryBuilder,
  used : Theory,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.require_open(span)
  require_same_id(self.anchor, used.anchor, span)
  let already_used = self.used_theories.any(entry => entry.0 == used.key)
  let already_known = self.knows_theory(used)
  let add_dependency = !already_used && !already_known
  if add_dependency {
    self.known = self.known.merge(used.known, span)
    self.register_used_theory(used)
  }
  let current_import = self.current_namespace()
  let current_export = self.export_namespaces[self.export_namespaces.length() -
    1]
  self.replace_current_namespaces(
    current_import.overlay(used.export_namespace),
    current_export,
  )
  self.range_projections = merge_range_projections(
    self.range_projections,
    used.range_projections,
    span,
  )
  self.float_projections = merge_float_projections(
    self.float_projections,
    used.float_projections,
    span,
  )
  self.coercions = self.coercions.union(used.coercions, span)
  self.proved_wf = merge_proved_wf(self.proved_wf, used.proved_wf, span)
  if add_dependency {
    self.items.push(TheoryUse(used.key))
  }
}

///|
/// Opens a Why3 namespace scope. Resolution inherits the enclosing namespace,
/// while the scope's exported namespace starts empty.
pub fn TheoryBuilder::open_scope(
  self : TheoryBuilder,
  name : BytesView,
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  self.require_open(span)
  if name.is_empty() {
    fail_theory(InvalidQualifiedName, span, "scope name is empty")
  }
  self.import_namespaces.push(self.current_namespace())
  self.export_namespaces.push(Namespace::empty())
  self.scope_names.push(name.to_owned())
}

///|
/// Closes the innermost scope. Its exported namespace is always available by
/// qualification and is additionally imported when `import_` is true.
pub fn TheoryBuilder::close_scope(
  self : TheoryBuilder,
  import_ : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  self.require_open(span)
  let depth = self.scope_names.length()
  if depth == 0 {
    fail_theory(NoOpenedNamespace, span, "no namespace scope is open")
  }
  let scope_name = self.scope_names[depth - 1]
  let scope_export = self.export_namespaces[self.export_namespaces.length() - 1]
  let parent_index = self.import_namespaces.length() - 2
  let mut parent_import = self.import_namespaces[parent_index]
  if import_ {
    parent_import = parent_import.overlay(scope_export)
  }
  parent_import = parent_import.overlay(
    Namespace::empty().add_subspace(scope_name, scope_export, span),
  )
  let parent_export = self.export_namespaces[parent_index].add_subspace(
    scope_name, scope_export, span,
  )
  self.import_namespaces = self.import_namespaces[:parent_index + 1].to_owned()
  self.export_namespaces = self.export_namespaces[:parent_index + 1].to_owned()
  self.scope_names = self.scope_names[:depth - 1].to_owned()
  self.import_namespaces[parent_index] = parent_import
  self.export_namespaces[parent_index] = parent_export
}

///|
/// Imports an already-visible qualified namespace for lookup only. Like Why3's
/// `import_scope`, this operation does not alter the exported namespace.
pub fn TheoryBuilder::import_scope(
  self : TheoryBuilder,
  path : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  self.require_open(span)
  let index = self.import_namespaces.length() - 1
  self.import_namespaces[index] = self
    .current_namespace()
    .import_scope(path, span)
}

///|
pub fn TheoryBuilder::add_clone_witness(
  self : TheoryBuilder,
  witness : CloneWitness,
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  self.require_open(span)
  require_same_id(self.anchor, witness.context_anchor(), span)
  self.items.push(TheoryClone(witness))
}

///|
pub fn TheoryBuilder::add_meta(
  self : TheoryBuilder,
  meta : Meta,
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  self.require_open(span)
  meta.validate_context(self.anchor, span)
  meta.validate_known(self.known, span)
  let (ranges, floats, coercions) = apply_derived_meta(
    self.range_projections,
    self.float_projections,
    self.coercions,
    meta,
    span,
  )
  self.range_projections = ranges
  self.float_projections = floats
  self.coercions = coercions
  self.proved_wf = add_proved_wf_meta(self.proved_wf, self.known, meta, span)
  self.items.push(TheoryMeta(meta))
}

///|
pub fn TheoryBuilder::close(self : TheoryBuilder) -> Theory raise TheoryError {
  self.require_open(None)
  if !self.scope_names.is_empty() {
    fail_theory(
      InvalidTheoryItem,
      None,
      "cannot close a theory while a namespace scope is open",
    )
  }
  self.closed = true
  {
    anchor: self.anchor,
    key: self.key,
    name: self.name,
    items: self.items.copy(),
    export_namespace: self.export_namespaces[0],
    known: self.known,
    local_symbols: self.local_symbols.copy(),
    used_theories: self.used_theories.copy(),
    clone_sources: self.clone_sources.copy(),
    range_projections: self.range_projections,
    float_projections: self.float_projections,
    coercions: self.coercions,
    proved_wf: self.proved_wf,
  }
}

///|
pub fn Theory::used_theory(self : Theory, key : TheoryKey) -> Theory {
  for entry in self.used_theories {
    if entry.0 == key {
      return entry.1
    }
  }
  abort("validated theory lost a referenced use target")
}

///|
pub fn Theory::clone_source(self : Theory, key : TheoryKey) -> Theory? {
  for entry in self.clone_sources {
    if entry.0 == key {
      return Some(entry.1)
    }
  }
  for entry in self.used_theories {
    if entry.0 == key {
      return Some(entry.1)
    }
  }
  None
}
