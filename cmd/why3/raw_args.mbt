// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
#cfg(not(platform="windows"))
priv struct RawCliArgument(Bytes)

///|
#cfg(platform="windows")
priv struct RawCliArgument(String)

///|
extern "C" fn raw_cli_arguments() -> FixedArray[RawCliArgument] = "moonbit_rt_get_cli_args"

///|
#cfg(not(platform="windows"))
fn validate_file_argument_utf8() -> Unit raise @prover.ConfigError {
  let arguments = raw_cli_arguments()
  if arguments.length() <= 2 {
    return
  }
  ignore(@utf8.decode(arguments[2].0)) catch {
    _ =>
      raise @prover.ConfigError({
        kind: @prover.NonUtf8Path,
        message: "input file path is not valid UTF-8",
      })
  }
}

///|
#cfg(platform="windows")
fn validate_file_argument_utf8() -> Unit {
  // Windows provides command-line arguments as native UTF-16 Strings.
  ignore(raw_cli_arguments())
}
