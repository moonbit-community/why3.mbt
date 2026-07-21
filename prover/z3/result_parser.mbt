// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Result precedence follows Why3 1.7.2 driver/call_provers.ml for the frozen
// z3_487 answer rules. Runtime-limit heuristics are intentionally excluded.

///|
fn bytes_equal(left : BytesView, right : BytesView) -> Bool {
  if left.length() != right.length() {
    return false
  }
  for index = 0; index < left.length(); index = index + 1 {
    if left[index] != right[index] {
      return false
    }
  }
  true
}

///|
fn bytes_starts_with(value : BytesView, prefix : BytesView) -> Bool {
  if value.length() < prefix.length() {
    return false
  }
  for index = 0; index < prefix.length(); index = index + 1 {
    if value[index] != prefix[index] {
      return false
    }
  }
  true
}

///|
fn find_bytes(value : BytesView, needle : BytesView) -> Int? {
  if needle.is_empty() {
    return Some(0)
  }
  if needle.length() > value.length() {
    return None
  }
  for start = 0; start + needle.length() <= value.length(); start = start + 1 {
    let mut matches = true
    for offset = 0; offset < needle.length(); offset = offset + 1 {
      if value[start + offset] != needle[offset] {
        matches = false
        break
      }
    }
    if matches {
      return Some(start)
    }
  }
  None
}

///|
fn bytes_contains(value : BytesView, needle : BytesView) -> Bool {
  find_bytes(value, needle) is Some(_)
}

///|
fn trim_ascii(value : BytesView) -> BytesView {
  let mut start = 0
  let mut end = value.length()
  while start < end &&
        (value[start] == b' ' || value[start] == b'\t' || value[start] == b'\r') {
    start = start + 1
  }
  while end > start &&
        (
          value[end - 1] == b' ' ||
          value[end - 1] == b'\t' ||
          value[end - 1] == b'\r'
        ) {
    end = end - 1
  }
  value[start:end]
}

///|
fn normalized_reason(line : BytesView) -> Bytes? {
  let prefix = b"(:reason-unknown "
  guard bytes_starts_with(line, prefix) &&
    line.length() > prefix.length() &&
    line[line.length() - 1] == b')' else {
    return None
  }
  let raw = trim_ascii(line[prefix.length():line.length() - 1])
  if raw.length() >= 2 && raw[0] == b'"' && raw[raw.length() - 1] == b'"' {
    Some(raw[1:raw.length() - 1].to_owned())
  } else {
    Some(raw.to_owned())
  }
}

///|
fn has_ascii_digits(value : BytesView) -> Bool {
  if value.is_empty() {
    return false
  }
  for byte in value {
    if byte < b'0' || byte > b'9' {
      return false
    }
  }
  true
}

///|
fn matches_step_limit(line : BytesView) -> Bool {
  let prefix = b"Maximal allocation counts "
  let suffix = b" have been exceeded"
  guard bytes_starts_with(line, prefix) &&
    line.length() >= prefix.length() + suffix.length() else {
    return false
  }
  let suffix_start = line.length() - suffix.length()
  bytes_equal(line[suffix_start:], suffix) &&
  has_ascii_digits(line[prefix.length():suffix_start])
}

///|
fn split_lines(output : BytesView) -> Array[Bytes] {
  let result : Array[Bytes] = []
  let mut start = 0
  for index, byte in output {
    if byte == b'\n' {
      result.push(trim_ascii(output[start:index]).to_owned())
      start = index + 1
    }
  }
  if start < output.length() {
    result.push(trim_ascii(output[start:]).to_owned())
  }
  result
}

///|
fn validate_utf8(
  output : BytesView,
) -> Unit raise @prover.MalformedProverOutput {
  ignore(@utf8.decode(output)) catch {
    _ =>
      raise @prover.MalformedProverOutput({
        kind: @prover.InvalidUtf8,
        message: "prover output is not UTF-8",
      })
  }
  ()
}

///|
fn classify_line(line : BytesView) -> @prover.ProverResult? {
  if bytes_equal(line, b"unsat") {
    return Some(@prover.Valid)
  }
  if bytes_equal(line, b"sat") {
    return Some(@prover.Unknown(b"sat"))
  }
  if bytes_equal(line, b"unknown") || bytes_equal(line, b"Fail") {
    return Some(@prover.Unknown(line.to_owned()))
  }
  if normalized_reason(line) is Some(reason) {
    return Some(@prover.Unknown(reason))
  }
  if bytes_equal(line, b"timeout") ||
    bytes_contains(line, b"interrupted by timeout") {
    return Some(@prover.Timeout)
  }
  if (
      bytes_contains(line, b"(error \"") &&
      bytes_contains(line, b"out of memory\")")
    ) ||
    bytes_contains(line, b"Failed to verify: pthread_create") ||
    bytes_contains(line, b"std::bad_alloc") ||
    bytes_contains(line, b"Resource temporarily unavailable") ||
    bytes_contains(line, b"Cannot allocate memory") {
    return Some(@prover.OutOfMemory)
  }
  if matches_step_limit(line) {
    return Some(@prover.StepLimitExceeded)
  }
  None
}

///|
fn merge_answer(
  current : @prover.ProverResult?,
  next : @prover.ProverResult,
) -> @prover.ProverResult? {
  match (current, next) {
    (_, @prover.Valid) => Some(@prover.Valid)
    (Some(@prover.Valid), _) => current
    (Some(@prover.Unknown(reason)), @prover.Unknown(next_reason)) =>
      if reason == b"unknown" {
        if next_reason == b"timeout" {
          Some(@prover.Timeout)
        } else if next_reason == b"resourceout" {
          Some(@prover.StepLimitExceeded)
        } else {
          Some(@prover.Unknown(next_reason))
        }
      } else {
        current
      }
    (None, _) => Some(next)
    (Some(@prover.Unknown(_)), @prover.Timeout) => Some(@prover.Timeout)
    (Some(@prover.Unknown(_)), @prover.OutOfMemory) => Some(@prover.OutOfMemory)
    (Some(@prover.Unknown(_)), @prover.StepLimitExceeded) =>
      Some(@prover.StepLimitExceeded)
    _ => current
  }
}

///|
pub fn parse_result(
  outcome : @prover.RawProcessOutcome,
) -> @prover.ProverResult raise {
  let view = outcome.view()
  validate_utf8(view.stdout)
  validate_utf8(view.stderr)
  let mut answer : @prover.ProverResult? = None
  for output in [view.stdout, view.stderr] {
    for line in split_lines(output) {
      if classify_line(line) is Some(next) {
        answer = merge_answer(answer, next)
      }
    }
  }
  if answer is Some(answer) {
    return answer
  }
  match view.status {
    @prover.Signaled(signal) =>
      raise @prover.ProcessError({
        kind: @prover.SignaledProcess,
        exit_code: None,
        signal: Some(signal),
        message: "prover terminated by signal",
      })
    @prover.Exited(code) if code != 0 =>
      raise @prover.ProcessError({
        kind: @prover.UnclassifiedExit,
        exit_code: Some(code),
        signal: None,
        message: "prover exited without a recognized answer",
      })
    @prover.Exited(_) =>
      raise @prover.MalformedProverOutput({
        kind: @prover.UnrecognizedOutput,
        message: "prover output contains no recognized answer",
      })
  }
}
