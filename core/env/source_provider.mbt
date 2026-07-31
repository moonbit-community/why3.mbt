// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
struct LibraryPath {
  segments : Array[Bytes]
}

///|
pub(all) struct LibraryPathView {
  segments : ArrayView[Bytes]
}

///|
fn invalid_path_segment(segment : BytesView) -> Bool {
  segment.is_empty() ||
  segment == b"." ||
  segment == b".." ||
  segment.find(b"/") is Some(_) ||
  segment.find(b"\\") is Some(_)
}

///|
/// Builds a validated Why3 library path. The empty path is accepted because
/// `Env.read_library` gives it the special builtin meaning `why3`.
pub fn LibraryPath::new(
  segments : ArrayView[Bytes],
) -> LibraryPath raise SourceError {
  for segment in segments {
    if invalid_path_segment(segment) {
      fail_source(
        InvalidLibraryPath,
        segments,
        [],
        [],
        "invalid library path qualifier",
      )
    }
  }
  { segments: segments.to_owned() }
}

///|
pub fn LibraryPath::view(self : LibraryPath) -> LibraryPathView {
  { segments: self.segments[:] }
}

///|
pub fn LibraryPath::is_empty(self : LibraryPath) -> Bool {
  self.segments.is_empty()
}

///|
pub fn LibraryPath::is_builtin(self : LibraryPath) -> Bool {
  !self.segments.is_empty() && self.segments[0] == b"why3"
}

///|
/// Matches Why3's empty-path normalization in `Env.read_library`.
pub fn LibraryPath::normalized_request(self : LibraryPath) -> LibraryPath {
  if self.segments.is_empty() {
    { segments: [b"why3"] }
  } else {
    self
  }
}

///|
pub fn LibraryPath::without_builtin_prefix(self : LibraryPath) -> LibraryPath? {
  if self.is_builtin() {
    Some({ segments: self.segments[1:].to_owned() })
  } else {
    None
  }
}

///|
pub fn LibraryPath::lexical_compare(
  self : LibraryPath,
  other : LibraryPath,
) -> Int {
  let shared = self.segments.length().min(other.segments.length())
  for index = 0; index < shared; index = index + 1 {
    let order = self.segments[index].lexical_compare(other.segments[index])
    if order != 0 {
      return order
    }
  }
  self.segments.length().compare(other.segments.length())
}

///|
pub impl Eq for LibraryPath with fn equal(self, other) {
  self.segments == other.segments
}

///|
pub impl Hash for LibraryPath with fn hash_combine(self, hasher) {
  hasher.combine(self.segments.length())
  for segment in self.segments {
    hasher.combine(segment)
  }
}

///|
struct MemorySource {
  path : LibraryPath
  extension : Bytes
  contents : Bytes
}

///|
pub(all) struct MemorySourceView {
  path : LibraryPath
  extension : Bytes
  contents : Bytes
}

///|
fn validate_extension(
  extension : BytesView,
  path : ArrayView[Bytes],
) -> Unit raise SourceError {
  if extension.is_empty() ||
    extension.find(b"/") is Some(_) ||
    extension.find(b"\\") is Some(_) {
    fail_source(
      InvalidExtension,
      path,
      [],
      [],
      "library extension must be non-empty and contain no path separator",
    )
  }
}

///|
pub fn MemorySource::new(
  path : LibraryPath,
  extension : BytesView,
  contents : BytesView,
) -> MemorySource raise SourceError {
  let segments = path.view().segments
  if segments.is_empty() {
    fail_source(
      InvalidLibraryPath,
      segments,
      [],
      [],
      "a memory source cannot have an empty library path",
    )
  }
  validate_extension(extension, segments)
  { path, extension: extension.to_owned(), contents: contents.to_owned() }
}

///|
pub fn MemorySource::view(self : MemorySource) -> MemorySourceView {
  { path: self.path, extension: self.extension, contents: self.contents }
}

///|
struct SourceCandidate {
  provider_root : Bytes
  path : LibraryPath
  extension : Bytes
  location : Bytes
  contents : Bytes
}

///|
pub(all) struct SourceCandidateView {
  provider_root : Bytes
  path : LibraryPath
  extension : Bytes
  location : Bytes
  contents : Bytes
}

///|
pub fn SourceCandidate::view(self : SourceCandidate) -> SourceCandidateView {
  {
    provider_root: self.provider_root,
    path: self.path,
    extension: self.extension,
    location: self.location,
    contents: self.contents,
  }
}

///|
priv struct MemoryRoot {
  name : Bytes
  sources : Array[MemorySource]
}

///|
/// Pure all-target source provider. Roots preserve loadpath order, while each
/// lookup enumerates extensions in caller order, just like Why3's
/// `locate_library`.
struct SourceProvider {
  roots : Array[MemoryRoot]
}

///|
pub fn SourceProvider::empty() -> SourceProvider {
  { roots: [] }
}

///|
pub fn SourceProvider::memory(
  root : BytesView,
  sources : ArrayView[MemorySource],
) -> SourceProvider {
  { roots: [{ name: root.to_owned(), sources: sources.to_owned() }] }
}

///|
pub fn SourceProvider::combine(
  providers : ArrayView[SourceProvider],
) -> SourceProvider {
  let roots : Array[MemoryRoot] = []
  for provider in providers {
    for root in provider.roots {
      roots.push({ name: root.name, sources: root.sources.copy() })
    }
  }
  { roots, }
}

///|
fn source_location(
  root : BytesView,
  path : LibraryPath,
  extension : BytesView,
) -> Bytes {
  let mut location = root.to_owned()
  for segment in path.view().segments {
    if !location.is_empty() && !location.has_suffix(b"/") {
      location = location + b"/"
    }
    location = location + segment
  }
  location + b"." + extension.to_owned()
}

///|
/// Returns every matching source. Ambiguity is deliberately not collapsed at
/// the provider boundary: callers receive the complete candidate set.
pub fn SourceProvider::candidates(
  self : SourceProvider,
  path : LibraryPath,
  extensions : ArrayView[Bytes],
) -> Array[SourceCandidate] raise SourceError {
  let segments = path.view().segments
  if path.is_empty() || path == LibraryPath::new([b"why3"]) {
    fail_source(
      InvalidLibraryPath,
      segments,
      [],
      [],
      "Env.locate_library does not accept the empty or why3 root path",
    )
  }
  for extension in extensions {
    validate_extension(extension, segments)
  }
  let result : Array[SourceCandidate] = []
  for root in self.roots {
    for extension in extensions {
      for source in root.sources {
        if source.path == path && source.extension == extension {
          result.push({
            provider_root: root.name,
            path,
            extension: source.extension,
            location: source_location(root.name, path, extension),
            contents: source.contents,
          })
        }
      }
    }
  }
  result
}

///|
pub fn SourceProvider::locate(
  self : SourceProvider,
  path : LibraryPath,
  extensions : ArrayView[Bytes],
) -> SourceCandidate raise SourceError {
  let candidates = self.candidates(path, extensions)
  match candidates {
    [] =>
      fail_source(
        LibraryNotFound,
        path.view().segments,
        [],
        [],
        "library file not found",
      )
    [candidate] => candidate
    _ => {
      let locations = candidates.map(candidate => candidate.location)
      fail_source(
        AmbiguousPath,
        path.view().segments,
        locations,
        [],
        "ambiguous library path",
      )
    }
  }
}
