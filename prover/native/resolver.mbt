// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
struct ResolvedExecutable {
  path : String
}

///|
priv struct ResolvedLauncher {
  executable : ResolvedExecutable
  arguments : Array[String]
}

///|
pub fn ResolvedExecutable::path(self : ResolvedExecutable) -> StringView {
  self.path[:]
}

///|
fn process_error(
  kind : @prover.ProcessErrorKind,
  message : String,
) -> @prover.ProcessError {
  @prover.ProcessError({ kind, exit_code: None, signal: None, message })
}

///|
fn decode_command_bytes(value : BytesView) -> String raise @prover.ConfigError {
  @utf8.decode(value) catch {
    _ =>
      raise @prover.ConfigError({
        kind: @prover.InvalidCommand,
        message: "native prover command is not UTF-8",
      })
  }
}

///|
fn join_path(directory : StringView, name : StringView) -> String {
  if directory.is_empty() {
    "./" + name.to_owned()
  } else if directory[directory.length() - 1] == '/' {
    directory.to_owned() + name.to_owned()
  } else {
    directory.to_owned() + "/" + name.to_owned()
  }
}

///|
async fn executable_candidate(path : String) -> String? {
  if !@fs.can_execute(path) {
    return None
  }
  Some(@fs.realpath(path))
}

///|
pub async fn resolve_executable(request : BytesView) -> ResolvedExecutable {
  let requested = decode_command_bytes(request)
  if requested.find("/") is Some(_) {
    let inspected = executable_candidate(requested) catch {
      err =>
        raise process_error(
          @prover.SpawnFailed,
          "cannot inspect prover executable: \{@debug.to_string(err)}",
        )
    }
    return match inspected {
      Some(path) => { path, }
      None =>
        raise process_error(
          @prover.ExecutableNotFound,
          "prover executable is missing or not executable",
        )
    }
  }
  let search_path = @env.get_env_var("PATH").unwrap_or("")
  for directory in search_path.split(":") {
    let candidate = join_path(directory, requested)
    let resolved = executable_candidate(candidate) catch { _ => None }
    if resolved is Some(path) {
      return { path, }
    }
  }
  raise process_error(
    @prover.ExecutableNotFound,
    "prover executable was not found on PATH",
  )
}

///|
async fn resolve_current_launcher() -> ResolvedLauncher {
  let arguments = @env.args()
  if arguments.is_empty() {
    raise process_error(
      @prover.SpawnFailed,
      "cannot determine the current executable",
    )
  }
  let direct = executable_candidate(arguments[0]) catch { _ => None }
  if direct is Some(path) {
    return { executable: { path, }, arguments: [] }
  }
  let source_file = @fs.realpath(arguments[0]) catch {
    _ =>
      raise process_error(
        @prover.SpawnFailed,
        "current executable is neither runnable nor a TCC response file",
      )
  }
  if source_file.length() < 2 || source_file[source_file.length() - 2:] != ".c" {
    raise process_error(
      @prover.SpawnFailed,
      "the TCC native test launcher did not expose a generated C source",
    )
  }
  let response_file = @fs.realpath(
    source_file[:source_file.length() - 2].to_owned() + ".rspfile",
  ) catch {
    _ =>
      raise process_error(
        @prover.SpawnFailed,
        "cannot locate MoonBit's native test response file",
      )
  }
  let moon = resolve_executable(b"moon")
  let moon_path = moon.path()
  if moon_path.length() < 4 || moon_path[moon_path.length() - 4:] != "moon" {
    raise process_error(
      @prover.SpawnFailed,
      "cannot locate MoonBit's native test launcher",
    )
  }
  let tcc_path = moon_path[:moon_path.length() - 4].to_owned() + "internal/tcc"
  let tcc = resolve_executable(@utf8.encode(tcc_path))
  { executable: tcc, arguments: ["@" + response_file] }
}
