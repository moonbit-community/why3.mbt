// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
/// A single-threaded allocator for semantic identities belonging to one
/// compilation. Its token is deliberately opaque and never serialized.
struct CompilationContext {
  token : Ref[Unit]
  mut next_local_id : Int64
}

///|
/// An identity whose numeric component is meaningful only together with its
/// opaque compilation-context token.
struct SemanticId {
  token : Ref[Unit]
  local_id : Int64
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
  { token: Ref(()), next_local_id: 0L }
}

///|
/// Allocates the next context-local semantic identity.
pub fn CompilationContext::fresh_id(self : CompilationContext) -> SemanticId {
  let local_id = self.next_local_id
  self.next_local_id = local_id + 1L
  { token: self.token, local_id }
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
