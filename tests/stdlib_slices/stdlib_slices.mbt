// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn require_stdlib_slice(condition : Bool, message : String) -> Unit {
  if !condition {
    abort(message)
  }
}

///|
fn upstream_stdlib_paths() -> Array[String] {
  [
    "algebra", "array", "bag", "bintree", "bool", "bv", "byte_string", "cursor",
    "debug", "exn", "floating_point", "fmap", "for_drivers", "function", "graph",
    "hashtbl", "ieee_float", "int", "io", "list", "mach/array", "mach/bv", "mach/c",
    "mach/float", "mach/fxp", "mach/int", "mach/matrix", "mach/onetime", "mach/peano",
    "mach/tagset", "map", "matrix", "microc", "null", "number", "ocaml", "option",
    "pigeon", "pqueue", "python", "queue", "random", "real", "ref", "regexp", "relations",
    "seq", "set", "stack", "string", "tptp", "tree", "witness",
  ]
}

///|
fn upstream_stdlib_provider() -> @env.SourceProvider raise {
  let sources : Array[@env.MemorySource] = []
  for path in upstream_stdlib_paths() {
    let segments = [ for segment in path.split("/") => @utf8.encode(segment) ]
    sources.push(
      @env.MemorySource::new(
        @env.LibraryPath::new(segments),
        b"mlw",
        @fs.read_file_to_bytes("../why3/stdlib/" + path + ".mlw"),
      ),
    )
  }
  @env.SourceProvider::memory(b"upstream-stdlib", sources)
}

///|
fn require_slice_bounds(start : Int, end : Int, length : Int) -> Unit {
  require_stdlib_slice(
    start >= 0 && start < end && end <= length,
    "invalid standard-library test slice",
  )
}

///|
fn require_cached_path(
  environment : @environment.Environment,
  path : @env.LibraryPath,
  label : String,
) -> Unit raise {
  require_stdlib_slice(
    environment.cached_library_paths().any(found => found == path),
    label + " was not published in the typed cache",
  )
  ignore(
    environment.read_library(path, (_, _, _) => {
      abort(label + " invoked its loader after being cached")
    }),
  )
}

///|
fn require_complete_cache(
  environment : @environment.Environment,
  source_count : Int,
) -> Unit raise {
  let cached = environment.cached_library_paths()
  require_stdlib_slice(
    cached.any(path => path == @env.LibraryPath::new([b"why3", b"Ref"])),
    "the complete standard-library load omitted the generated Ref builtin",
  )
  require_stdlib_slice(
    cached.any(path => path == @env.LibraryPath::new([b"why3", b"WellFounded"])),
    "the complete standard-library load omitted the generated WellFounded builtin",
  )
  require_stdlib_slice(
    cached.length() == source_count + 2,
    "the complete standard-library cache has an unexpected size",
  )
}

///|
pub fn check_upstream_stdlib_slice(start : Int, end : Int) -> Unit raise {
  let paths = upstream_stdlib_paths()
  require_stdlib_slice(
    paths.length() == 53,
    "the upstream standard-library inventory must contain 53 sources",
  )
  require_slice_bounds(start, end, paths.length())
  let context = @identity.CompilationContext::new()
  let environment = @environment.Environment::with_source_in_context(
    context,
    upstream_stdlib_provider(),
  )
  for index in start..<end {
    let label = paths[index]
    let path = @env.LibraryPath::new(
      [
        for segment in label.split("/") => @utf8.encode(segment)
      ],
    )
    ignore(
      environment.read_library(path, @why3_elab.load_mlw_library) catch {
        @why3_elab.ElabError(diagnostic) => {
          let (relative_path, line, column) = match diagnostic.span {
            Some(span) => {
              let view = span.view()
              (
                view.relative_path.to_string(),
                view.start_line,
                view.start_column,
              )
            }
            None => ("<unknown>", Int64::from_int(-1), Int64::from_int(-1))
          }
          let type_detail = match
            (diagnostic.actual_type, diagnostic.expected_type) {
            (Some(actual), Some(expected)) =>
              " (" + actual.to_string() + " vs " + expected.to_string() + ")"
            _ => ""
          }
          abort(
            "failed to load " +
            label +
            " at " +
            relative_path +
            ":" +
            line.to_string() +
            ":" +
            column.to_string() +
            ": " +
            diagnostic.message +
            type_detail,
          )
        }
        _ => abort("failed to load " + label + " with another error family")
      },
    )
    require_cached_path(environment, path, label)
  }
  if start == 0 && end == paths.length() {
    require_complete_cache(environment, paths.length())
  }
}

///|
pub fn check_embedded_stdlib_slice(start : Int, end : Int) -> Unit raise {
  let paths = @stdlib.embedded_stdlib_paths()
  require_stdlib_slice(
    paths.length() == 53,
    "the embedded standard-library inventory must contain 53 sources",
  )
  require_slice_bounds(start, end, paths.length())
  let context = @identity.CompilationContext::new()
  let environment = @environment.Environment::with_source_in_context(
    context,
    @stdlib.embedded_source_provider(),
  )
  for index in start..<end {
    let path = paths[index]
    let label = path.view().segments
      .map(segment => segment.to_string())
      .join("/")
    ignore(
      environment.read_library(path, @why3_elab.load_mlw_library) catch {
        @why3_elab.ElabError(diagnostic) => {
          let location = match diagnostic.span {
            Some(span) => {
              let view = span.view()
              view.relative_path.to_string() +
              ":" +
              view.start_line.to_string() +
              ":" +
              view.start_column.to_string()
            }
            None => "<unknown>"
          }
          abort(
            "embedded stdlib failed at " + location + ": " + diagnostic.message,
          )
        }
        _ => abort("embedded stdlib raised another error family")
      },
    )
    require_cached_path(environment, path, label)
  }
  if start == 0 && end == paths.length() {
    require_complete_cache(environment, paths.length())
  }
}
