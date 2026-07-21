// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum ProverResult {
  Valid
  Invalid
  Unknown(Bytes)
  Timeout
  OutOfMemory
  StepLimitExceeded
} derive(Eq, Debug)

///|
pub(all) enum ProcessErrorKind {
  ExecutableNotFound
  SpawnFailed
  BrokenPipe
  ReadFailed
  WaitFailed
  UnclassifiedExit
  SignaledProcess
  Cancelled
} derive(Eq, Debug)

///|
pub(all) struct ProcessDiagnostic {
  kind : ProcessErrorKind
  exit_code : Int?
  signal : Bytes?
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror ProcessError {
  ProcessError(ProcessDiagnostic)
} derive(Eq, Debug)

///|
pub(all) enum MalformedProverOutputKind {
  InvalidUtf8
  UnrecognizedOutput
} derive(Eq, Debug)

///|
pub(all) struct MalformedProverOutputDiagnostic {
  kind : MalformedProverOutputKind
  message : String
} derive(Eq, Debug)

///|
pub(all) suberror MalformedProverOutput {
  MalformedProverOutput(MalformedProverOutputDiagnostic)
} derive(Eq, Debug)

///|
pub(all) enum ProverStream {
  StandardOutput
  StandardError
} derive(Eq, Debug)

///|
pub(all) struct OutputLimitDiagnostic {
  stream : ProverStream
  limit_bytes : Int
} derive(Eq, Debug)

///|
pub(all) suberror OutputLimitExceeded {
  OutputLimitExceeded(OutputLimitDiagnostic)
} derive(Eq, Debug)
