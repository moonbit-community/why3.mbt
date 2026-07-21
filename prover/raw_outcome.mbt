// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub(all) enum ProcessExitStatus {
  Exited(Int)
  Signaled(Bytes)
} derive(Eq, Debug)

///|
struct RawProcessOutcome {
  stdout : Bytes
  stderr : Bytes
  status : ProcessExitStatus
}

///|
pub(all) struct RawProcessOutcomeView {
  stdout : BytesView
  stderr : BytesView
  status : ProcessExitStatus
}

///|
pub fn RawProcessOutcome::new(
  stdout : BytesView,
  stderr : BytesView,
  status : ProcessExitStatus,
) -> RawProcessOutcome {
  { stdout: stdout.to_owned(), stderr: stderr.to_owned(), status }
}

///|
pub fn RawProcessOutcome::view(
  self : RawProcessOutcome,
) -> RawProcessOutcomeView {
  { stdout: self.stdout[:], stderr: self.stderr[:], status: self.status }
}
