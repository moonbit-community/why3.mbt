// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub fn default_solver_seconds() -> Int {
  10
}

///|
pub fn maximum_solver_seconds() -> Int {
  86400
}

///|
pub fn prover_stream_limit_bytes() -> Int {
  2 * 1024 * 1024
}

///|
pub(all) enum ConfigErrorKind {
  InvalidTimeout
  InvalidCommand
  NonUtf8Path
} derive(Eq, Debug)

///|
pub(all) struct ConfigDiagnostic {
  kind : ConfigErrorKind
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror ConfigError {
  ConfigError(ConfigDiagnostic)
} derive(Eq, Debug)

///|
pub fn validate_solver_seconds(seconds : Int) -> Int raise ConfigError {
  if seconds < 0 || seconds > maximum_solver_seconds() {
    raise ConfigError({
      kind: InvalidTimeout,
      message: "solver timeout must be an integer in 0..86400",
    })
  }
  seconds
}

///|
pub fn parent_deadline_seconds(seconds : Int) -> Int? raise ConfigError {
  let seconds = validate_solver_seconds(seconds)
  if seconds == 0 {
    None
  } else {
    Some(4 * seconds + 1)
  }
}
