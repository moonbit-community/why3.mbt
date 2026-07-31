// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn source_file_parts(name : BytesView) -> (Bytes, Bytes)? {
  if name.length() > 4 && name.has_suffix(b".mlw") {
    Some((name[0:name.length() - 4].to_owned(), b"mlw"))
  } else if name.length() > 4 && name.has_suffix(b".why") {
    Some((name[0:name.length() - 4].to_owned(), b"why"))
  } else {
    None
  }
}

///|
fn relative_directory_segments(
  root : BytesView,
  directory : BytesView,
) -> Array[Bytes] raise CliError {
  if !directory.has_prefix(root) {
    fail_cli(LoadpathError, "filesystem traversal escaped its loadpath root")
  }
  let mut start = root.length()
  while start < directory.length() &&
        (directory[start] == b'/' || directory[start] == b'\\') {
    start = start + 1
  }
  let segments : Array[Bytes] = []
  let mut segment_start = start
  for index = start; index < directory.length(); index = index + 1 {
    if directory[index] == b'/' || directory[index] == b'\\' {
      if index > segment_start {
        segments.push(directory[segment_start:index].to_owned())
      }
      segment_start = index + 1
    }
  }
  if segment_start < directory.length() {
    segments.push(directory[segment_start:].to_owned())
  }
  segments
}

///|
async fn loadpath_source_provider(
  requested_root : String,
) -> @source_env.SourceProvider raise CliError {
  let root = @fs.realpath(requested_root) catch {
    error =>
      fail_cli(
        LoadpathError,
        "cannot open loadpath " + requested_root + ": \{error}",
      )
  }
  let root_bytes = @utf8.encode(root)
  let sources : Array[@source_env.MemorySource] = []
  @fs.walk(root, max_concurrency=1, (directory, entries) => {
    let directory_bytes = @utf8.encode(directory)
    let prefix = relative_directory_segments(root_bytes, directory_bytes)
    for entry in entries {
      let entry_bytes = @utf8.encode(entry)
      if source_file_parts(entry_bytes) is Some((stem, extension)) {
        let path_segments = prefix.copy()
        path_segments.push(stem)
        let library_path = @source_env.LibraryPath::new(path_segments) catch {
          error =>
            fail_cli(
              LoadpathError,
              "invalid library path below " +
              requested_root +
              ": " +
              @debug.to_string(error),
            )
        }
        let separator = if directory.has_suffix("/") { "" } else { "/" }
        let filename = directory + separator + entry
        let contents = @fs.read_file(filename).binary() catch {
          error =>
            fail_cli(
              LoadpathError,
              "cannot read library source " + filename + ": \{error}",
            )
        }
        sources.push(
          @source_env.MemorySource::new(library_path, extension, contents) catch {
            error =>
              fail_cli(
                LoadpathError,
                "invalid library source " +
                filename +
                ": " +
                @debug.to_string(error),
              )
          },
        )
      }
    }
  }) catch {
    CliError(diagnostic) => raise CliError(diagnostic)
    error =>
      fail_cli(
        LoadpathError,
        "cannot traverse loadpath " + requested_root + ": \{error}",
      )
  }
  @source_env.SourceProvider::memory(root_bytes, sources)
}
