// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
/// A single-threaded allocator for semantic identities belonging to one
/// compilation. Its token is deliberately opaque and never serialized.
struct CompilationContext {
  token : Ref[Unit]
  mut next_local_id : Int64
  mut next_declaration_id : Int64
  mut next_identifier_id : Int64
  identifier_clone_events : Array[IdentifierCloneEvent]
  source_display_paths : Map[Bytes, Bytes]
}

///|
/// An identity whose numeric component is meaningful only together with its
/// opaque compilation-context token.
struct SemanticId {
  token : Ref[Unit]
  local_id : Int64
}

///|
/// Identity of one immutable declaration allocation. It is separate from
/// symbol identity so declaration-cache bookkeeping cannot perturb semantic
/// allocation or equality.
struct DeclarationId {
  token : Ref[Unit]
  local_id : Int64
}

///|
/// An identity used only to follow Why3-style identifier cloning. It is kept
/// separate from semantic identity so provenance-only clones cannot perturb
/// semantic allocation, equality, or canonical ordering.
struct IdentifierId {
  token : Ref[Unit]
  domain : Int
  local_id : Int64
}

///|
/// One Why3-style identifier clone notification. These events are replayed to
/// the currently active per-goal provenance observer.
struct IdentifierCloneEvent {
  original : IdentifierId
  clone : IdentifierId
}

///|
/// A compilation-local boundary in the identifier-clone event stream.
///
/// The opaque token prevents a watermark from one compilation from making
/// identifiers in another compilation appear newly allocated.
struct IdentifierWatermark {
  token : Ref[Unit]
  event_index : Int
}

///|
/// Raised when semantic objects from different compilation contexts are
/// combined.
pub(all) suberror ContextMismatch {
  ContextMismatch(String)
} derive(Eq, Debug)

///|
/// Creates a fresh compilation context. Allocation through one context is
/// intentionally single-threaded.
pub fn CompilationContext::new() -> CompilationContext {
  {
    token: Ref(()),
    next_local_id: 0L,
    next_declaration_id: 0L,
    next_identifier_id: 0L,
    identifier_clone_events: [],
    source_display_paths: Map([]),
  }
}

///|
/// Associates a stable logical parser filename with the physical filename
/// Why3 uses when materializing location attributes. Semantic source spans
/// keep the logical filename; only explicitly rendered location attributes
/// consult this table.
pub fn CompilationContext::register_source_display_path(
  self : CompilationContext,
  logical : BytesView,
  display : BytesView,
) -> Unit {
  self.source_display_paths[logical.to_owned()] = display.to_owned()
}

///|
pub fn CompilationContext::source_display_path(
  self : CompilationContext,
  logical : BytesView,
) -> Bytes {
  match self.source_display_paths.get(logical.to_owned()) {
    Some(display) => display
    None => logical.to_owned()
  }
}

///|
/// Allocates the next context-local semantic identity.
pub fn CompilationContext::fresh_id(self : CompilationContext) -> SemanticId {
  let local_id = self.next_local_id
  self.next_local_id = local_id + 1L
  { token: self.token, local_id }
}

///|
/// Allocates the next immutable declaration identity.
pub fn CompilationContext::fresh_declaration_id(
  self : CompilationContext,
) -> DeclarationId {
  let local_id = self.next_declaration_id
  self.next_declaration_id = local_id + 1L
  { token: self.token, local_id }
}

///|
/// Allocates an identifier-clone identity without consuming a semantic ID.
pub fn CompilationContext::fresh_identifier_id(
  self : CompilationContext,
) -> IdentifierId {
  let local_id = self.next_identifier_id
  self.next_identifier_id = local_id + 1L
  { token: self.token, domain: 1, local_id }
}

///|
/// Allocates a cloned identifier and emits the corresponding observer event.
pub fn CompilationContext::fresh_identifier_clone_id(
  self : CompilationContext,
  original : IdentifierId,
) -> IdentifierId {
  let clone = self.fresh_identifier_id()
  self.identifier_clone_events.push({ original, clone })
  clone
}

///|
/// Captures the end of the current identifier-clone event stream.
pub fn CompilationContext::identifier_watermark(
  self : CompilationContext,
) -> IdentifierWatermark {
  { token: self.token, event_index: self.identifier_clone_events.length() }
}

///|
/// Returns clone events emitted since the watermark. A foreign watermark
/// cannot expose events from this compilation.
pub fn CompilationContext::identifier_clone_events_since(
  self : CompilationContext,
  watermark : IdentifierWatermark,
) -> Array[IdentifierCloneEvent] {
  if !physical_equal(self.token, watermark.token) {
    return []
  }
  let events = []
  for index = watermark.event_index
      index < self.identifier_clone_events.length()
      index = index + 1 {
    events.push(self.identifier_clone_events[index])
  }
  events
}

///|
pub fn IdentifierCloneEvent::original(
  self : IdentifierCloneEvent,
) -> IdentifierId {
  self.original
}

///|
pub fn IdentifierCloneEvent::clone(self : IdentifierCloneEvent) -> IdentifierId {
  self.clone
}

///|
/// Uses a semantic object's identity as its initial, uncloned identifier.
pub fn SemanticId::identifier_id(self : SemanticId) -> IdentifierId {
  { token: self.token, domain: 0, local_id: self.local_id }
}

///|
/// Returns true only when the identity was allocated by this exact context.
pub fn CompilationContext::contains(
  self : CompilationContext,
  id : SemanticId,
) -> Bool {
  physical_equal(self.token, id.token)
}

///|
/// Exposes the context-local counter for diagnostics and invariant tests. It
/// must not be used as a portable or canonical identity.
pub fn SemanticId::local_id(self : SemanticId) -> Int64 {
  self.local_id
}

///|
/// Tests whether two identities belong to the same compilation context.
pub fn SemanticId::same_context(self : SemanticId, other : SemanticId) -> Bool {
  physical_equal(self.token, other.token)
}

///|
/// Rejects a cross-context semantic operation without exposing either token.
pub fn SemanticId::require_same_context(
  self : SemanticId,
  other : SemanticId,
  operation? : String = "semantic operation",
) -> Unit raise ContextMismatch {
  if !self.same_context(other) {
    raise ContextMismatch(operation)
  }
}

///|
pub impl Eq for SemanticId with fn equal(self, other) {
  self.local_id == other.local_id && self.same_context(other)
}

///|
/// Hashing only the local component is valid because equal identities always
/// share it. Different contexts may collide and are then separated by `Eq`.
pub impl Hash for SemanticId with fn hash_combine(self, hasher) {
  hasher.combine(self.local_id)
}

///|
pub impl Eq for DeclarationId with fn equal(self, other) {
  self.local_id == other.local_id && physical_equal(self.token, other.token)
}

///|
pub impl Hash for DeclarationId with fn hash_combine(self, hasher) {
  hasher.combine(self.local_id)
}

///|
pub impl Eq for IdentifierId with fn equal(self, other) {
  self.domain == other.domain &&
  self.local_id == other.local_id &&
  physical_equal(self.token, other.token)
}

///|
pub impl Hash for IdentifierId with fn hash_combine(self, hasher) {
  hasher.combine(self.domain)
  hasher.combine(self.local_id)
}
