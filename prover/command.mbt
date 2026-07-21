// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum ProverTransport {
  StandardInput
} derive(Eq, Debug)

///|
pub(all) enum ParentDeadlinePolicy {
  NoAutomaticDeadline
  DeadlineAfterSeconds(Int)
} derive(Eq, Debug)

///|
struct CommandSpec {
  profile_id : Bytes
  transport : ProverTransport
  executable_request : Bytes
  arguments : Array[Bytes]
  solver_seconds : Int
  parent_deadline_policy : ParentDeadlinePolicy
  stdout_limit_bytes : Int
  stderr_limit_bytes : Int
}

///|
pub(all) struct CommandSpecView {
  profile_id : Bytes
  transport : ProverTransport
  executable_request : Bytes
  arguments : ArrayView[Bytes]
  solver_seconds : Int
  parent_deadline_policy : ParentDeadlinePolicy
  stdout_limit_bytes : Int
  stderr_limit_bytes : Int
}

///|
fn contains_nul(value : BytesView) -> Bool {
  for byte in value {
    if byte == b'\x00' {
      return true
    }
  }
  false
}

///|
pub fn CommandSpec::new(
  profile_id : BytesView,
  transport : ProverTransport,
  executable_request : BytesView,
  arguments : ArrayView[Bytes],
  solver_seconds : Int,
) -> CommandSpec raise ConfigError {
  let seconds = validate_solver_seconds(solver_seconds)
  if executable_request.is_empty() || contains_nul(executable_request) {
    raise ConfigError({
      kind: InvalidCommand,
      message: "prover executable request must be non-empty and contain no NUL",
    })
  }
  for argument in arguments {
    if contains_nul(argument) {
      raise ConfigError({
        kind: InvalidCommand,
        message: "prover argument contains NUL",
      })
    }
  }
  let deadline = match parent_deadline_seconds(seconds) {
    None => NoAutomaticDeadline
    Some(value) => DeadlineAfterSeconds(value)
  }
  {
    profile_id: profile_id.to_owned(),
    transport,
    executable_request: executable_request.to_owned(),
    arguments: arguments.to_owned(),
    solver_seconds: seconds,
    parent_deadline_policy: deadline,
    stdout_limit_bytes: prover_stream_limit_bytes(),
    stderr_limit_bytes: prover_stream_limit_bytes(),
  }
}

///|
pub fn CommandSpec::view(self : CommandSpec) -> CommandSpecView {
  {
    profile_id: self.profile_id,
    transport: self.transport,
    executable_request: self.executable_request,
    arguments: self.arguments[:],
    solver_seconds: self.solver_seconds,
    parent_deadline_policy: self.parent_deadline_policy,
    stdout_limit_bytes: self.stdout_limit_bytes,
    stderr_limit_bytes: self.stderr_limit_bytes,
  }
}
