// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

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
  used_theories : Array[(TheoryKey, Theory)]
}

///|
pub(all) struct TheoryView {
  key : TheoryKey
  name : SemanticName
  items : ArrayView[TheoryItem]
  export_namespace : Namespace
}

///|
struct TheoryBuilder {
  anchor : @identity.SemanticId
  key : TheoryKey
  name : SemanticName
  items : Array[TheoryItem]
  mut import_namespaces : Array[Namespace]
  mut export_namespaces : Array[Namespace]
  mut scope_names : Array[Bytes]
  mut known : @logic.KnownMap
  used_theories : Array[(TheoryKey, Theory)]
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
    export_namespace: self.export_namespace,
  }
}

///|
pub fn Theory::export_namespace(self : Theory) -> Namespace {
  self.export_namespace
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
  for declaration in declarations {
    for introduced in declaration.introduced_symbols() {
      require_same_id(self.anchor, introduced.semantic_id(), span)
    }
    known = known.add(declaration, span)
    export_namespace = export_namespace.add_declaration_symbols(
      declaration, span,
    )
    items.push(TheoryDecl(declaration))
  }
  { ..self, items, export_namespace, known }
}

///|
pub fn TheoryBuilder::new(
  context : @identity.CompilationContext,
  key : TheoryKey,
  name : SemanticName,
) -> TheoryBuilder {
  {
    anchor: context.fresh_id(),
    key,
    name,
    items: [],
    import_namespaces: [Namespace::empty()],
    export_namespaces: [Namespace::empty()],
    scope_names: [],
    known: @logic.KnownMap::new(context),
    used_theories: [],
    closed: false,
  }
}

///|
/// Current visible namespace, including inherited and imported scope entries.
pub fn TheoryBuilder::current_namespace(self : TheoryBuilder) -> Namespace {
  self.import_namespaces[self.import_namespaces.length() - 1]
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
  self.replace_current_namespaces(
    self.current_namespace().add_declaration_symbols(declaration, span),
    self.export_namespaces[self.export_namespaces.length() - 1].add_declaration_symbols(
      declaration, span,
    ),
  )
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
  self.known = self.known.merge(used.known, span)
  let current_import = self.current_namespace()
  let current_export = self.export_namespaces[self.export_namespaces.length() -
    1]
  if import_ {
    self.replace_current_namespaces(
      current_import.merge(used.export_namespace, span),
      current_export.merge(used.export_namespace, span),
    )
  } else {
    self.replace_current_namespaces(
      current_import.add_subspace(
        used.key.view().name,
        used.export_namespace,
        span,
      ),
      current_export.add_subspace(
        used.key.view().name,
        used.export_namespace,
        span,
      ),
    )
  }
  if !self.used_theories.any(entry => entry.0 == used.key) {
    self.used_theories.push((used.key, used))
  }
  self.items.push(TheoryUse(used.key))
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
    parent_import = parent_import.merge(scope_export, span)
  }
  parent_import = parent_import.add_subspace(scope_name, scope_export, span)
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
    used_theories: self.used_theories.copy(),
  }
}

///|
pub fn Theory::trusted_snapshot(
  context : @identity.CompilationContext,
  key : TheoryKey,
  name : SemanticName,
  items : ArrayView[TheoryItem],
  export_namespace : Namespace,
  used_theories : ArrayView[Theory],
  span : @identity.SourceSpan?,
) -> Theory raise {
  let anchor = context.fresh_id()
  export_namespace.validate_context(anchor, span)
  let known = @logic.KnownMap::new(context)
  let mut known = known
  for used in used_theories {
    require_same_id(anchor, used.anchor, span)
    known = known.merge(used.known, span)
  }
  for item in items {
    match item {
      TheoryDecl(declaration) => {
        for introduced in declaration.introduced_symbols() {
          require_same_id(anchor, introduced.semantic_id(), span)
        }
        known = known.trusted_add_snapshot(declaration, span)
      }
      TheoryUse(_) => ()
      TheoryClone(witness) =>
        require_same_id(anchor, witness.context_anchor(), span)
      TheoryMeta(meta) => meta.validate_context(anchor, span)
    }
  }
  {
    anchor,
    key,
    name,
    items: items.to_owned(),
    export_namespace,
    known,
    used_theories: used_theories.map(theory => (theory.key, theory)),
  }
}

///|
/// Completes the trusted known-map after the whole snapshot theory graph has
/// been decoded. This is separate from semantic item decoding because the
/// snapshot inventory is canonically ordered, not dependency-topological.
pub fn Theory::trusted_import_known(
  self : Theory,
  used_theories : ArrayView[Theory],
  span : @identity.SourceSpan?,
) -> Theory raise {
  let mut known = self.known
  for used in used_theories {
    require_same_id(self.anchor, used.anchor, span)
    known = known.merge(used.known, span)
  }
  {
    ..self,
    known,
    used_theories: used_theories.map(theory => (theory.key, theory)),
  }
}

///|
fn Theory::used_theory(self : Theory, key : TheoryKey) -> Theory {
  for entry in self.used_theories {
    if entry.0 == key {
      return entry.1
    }
  }
  abort("validated theory lost a referenced use target")
}
