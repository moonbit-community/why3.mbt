// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn decimal_bytes(value : Int) -> Bytes {
  @utf8.encode(value.to_string())
}

///|
fn z3_time_argument(seconds : Int) -> Bytes {
  let buffer = @buffer.Buffer(size_hint=12)
  buffer.write_bytes(b"-T:")
  buffer.write_bytes(decimal_bytes(seconds))
  buffer.to_bytes()
}

///|
fn command_spec_from_template(
  template : Z3CommandTemplate,
  solver_seconds? : Int = @prover.default_solver_seconds(),
  executable_request? : BytesView? = None,
) -> @prover.CommandSpec raise @prover.ConfigError {
  let seconds = @prover.validate_solver_seconds(solver_seconds)
  let template = template.view()
  let executable = executable_request.unwrap_or(template.executable[:])
  let arguments : Array[Bytes] = [b"-smt2", b"-in"]
  if seconds > 0 {
    arguments.push(z3_time_argument(seconds))
  }
  arguments.push(b"sat.random_seed=42")
  arguments.push(b"nlsat.randomize=false")
  arguments.push(b"smt.random_seed=42")
  arguments.push(b"-st")
  @prover.CommandSpec::new(
    b"z3_487",
    @prover.StandardInput,
    executable,
    arguments,
    seconds,
  )
}

///|
pub fn Z3StaticSpec::command_spec(
  self : Z3StaticSpec,
  solver_seconds? : Int = @prover.default_solver_seconds(),
  executable_request? : BytesView? = None,
) -> @prover.CommandSpec raise @prover.ConfigError {
  command_spec_from_template(
    self.view().command,
    solver_seconds~,
    executable_request~,
  )
}

///|
pub fn Z3Profile::command_spec(
  self : Z3Profile,
  solver_seconds? : Int = @prover.default_solver_seconds(),
  executable_request? : BytesView? = None,
) -> @prover.CommandSpec raise @prover.ConfigError {
  command_spec_from_template(
    self.command(),
    solver_seconds~,
    executable_request~,
  )
}
