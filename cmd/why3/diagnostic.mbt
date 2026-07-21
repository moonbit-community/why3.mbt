// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
enum CliErrorKind {
  UsageError
  InvalidArgument
  InvalidTimeout
  ExternalLoadpath
  SelectionError
  OutputError
} derive(Eq, Debug)

///|
struct CliDiagnostic {
  kind : CliErrorKind
  message : String
} derive(Eq, Debug)

///|
suberror CliError {
  CliError(CliDiagnostic)
} derive(Eq, Debug)
