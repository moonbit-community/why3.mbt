// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn bytes_hex_string(bytes : BytesView) -> String {
  @utf8.decode(@canonical.bytes_to_lower_hex(bytes)) catch {
    _ => abort("lowercase hexadecimal output is not UTF-8")
  }
}

///|
fn display_bytes(bytes : BytesView) -> String {
  @utf8.decode(bytes) catch {
    _ => "0x" + bytes_hex_string(bytes)
  }
}

///|
async fn write_bytes_stdout(bytes : BytesView) -> Unit {
  let text = @utf8.decode(bytes) catch {
    _ => abort("CLI textual output is not UTF-8")
  }
  @stdio.stdout.write(text)
}

///|
fn unit_kind_text(kind : @z3.GoalUnitKind) -> String {
  match kind {
    TheoryUnit => "theory"
    ModuleUnit => "module"
  }
}

///|
fn goal_json_prefix(info : @z3.GoalInfoView, stage : String) -> String {
  "{\"schema\":1,\"stage\":\"" +
  stage +
  "\",\"unit_kind\":\"" +
  unit_kind_text(info.unit_kind) +
  "\",\"unit_name_hex\":\"" +
  bytes_hex_string(info.unit_name) +
  "\",\"goal_name_hex\":\"" +
  bytes_hex_string(info.goal.view().name) +
  "\",\"goal_ordinal\":" +
  info.ordinal.to_string()
}

///|
fn prover_result_kind(result : @prover.ProverResult) -> String {
  match result {
    Valid => "Valid"
    Invalid => "Invalid"
    Unknown(_) => "Unknown"
    Timeout => "Timeout"
    OutOfMemory => "OutOfMemory"
    StepLimitExceeded => "StepLimitExceeded"
  }
}

///|
fn prover_result_human(result : @prover.ProverResult) -> String {
  match result {
    Unknown(reason) => "Unknown(" + display_bytes(reason) + ")"
    _ => prover_result_kind(result)
  }
}

///|
fn prover_result_json(result : @prover.ProverResult) -> String {
  match result {
    Unknown(reason) =>
      "{\"kind\":\"Unknown\",\"reason_hex\":\"" +
      bytes_hex_string(reason) +
      "\"}"
    _ => "{\"kind\":\"" + prover_result_kind(result) + "\"}"
  }
}

///|
fn six_digit_ordinal(ordinal : Int) -> String raise CliError {
  if ordinal < 0 || ordinal > 999999 {
    fail_cli(OutputError, "SMT output ordinal is outside 000000..999999")
  }
  let mut result = ordinal.to_string()
  while result.length() < 6 {
    result = "0" + result
  }
  result
}
