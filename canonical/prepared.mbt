// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn canonical_goal_unit_kind(kind : @z3.GoalUnitKind) -> CanonicalValue {
  canonical_text(
    match kind {
      TheoryUnit => b"theory"
      ModuleUnit => b"module"
    },
  )
}

///|
fn canonical_goal_info(
  state : CanonicalV3State,
  info : @z3.GoalInfo,
) -> CanonicalValue {
  let view = info.view()
  v3_node(b"GoalInfoV1", [
    canonical_goal_unit_kind(view.unit_kind),
    v3_bytes(view.unit_name),
    v3_prsymbol(state, view.goal),
    v3_bytes(view.display_name),
    v3_int(view.ordinal),
    v3_origin(state, view.origin),
    v3_set([ for attribute in view.expl_attributes => v3_bytes(attribute) ]),
  ])
}

///|
fn canonical_transport(transport : @prover.ProverTransport) -> CanonicalValue {
  match transport {
    StandardInput => canonical_text(b"stdin")
  }
}

///|
fn canonical_deadline(policy : @prover.ParentDeadlinePolicy) -> CanonicalValue {
  match policy {
    NoAutomaticDeadline => canonical_array([canonical_text(b"none")])
    DeadlineAfterSeconds(seconds) =>
      canonical_array([
        canonical_text(b"seconds"),
        Unsigned(seconds.reinterpret_as_uint()),
      ])
  }
}

///|
fn canonical_command(command : @prover.CommandSpec) -> CanonicalValue {
  let view = command.view()
  // Deliberately omit expanded argv and resolved paths: they are runtime
  // diagnostics, not portable semantic data.
  canonical_array([
    canonical_text(b"CommandSpecV1"),
    canonical_hex(view.profile_id),
    canonical_transport(view.transport),
    canonical_hex(view.executable_request),
    Unsigned(view.solver_seconds.reinterpret_as_uint()),
    canonical_deadline(view.parent_deadline_policy),
    Unsigned(view.stdout_limit_bytes.reinterpret_as_uint()),
    Unsigned(view.stderr_limit_bytes.reinterpret_as_uint()),
  ])
}

///|
pub fn encode_prepared_call(
  call : @z3.PreparedCall,
) -> CanonicalJson raise @smtv2.PrinterError {
  let state = CanonicalV3State::new()
  let tokens = @smtv2.normalize_smt_query(call.query())
  let raw_task = v3_task(state, call.raw_task())
  let prepared_task = v3_task(state, call.prepared_task())
  let goal = canonical_goal_info(state, call.goal_info())
  state.finish([
    v3_node(b"PreparedCallV1", [
      raw_task,
      prepared_task,
      canonical_smt_token_stream(tokens),
      canonical_command(call.command()),
      goal,
    ]),
  ])
}

///|
fn encode_prepared_call_for_source(
  call : @z3.PreparedCall,
  selected_source_path : BytesView,
) -> CanonicalJson raise @smtv2.PrinterError {
  let state = CanonicalV3State::new_for_source(selected_source_path)
  let tokens = @smtv2.normalize_smt_query(call.query())
  let raw_task = v3_task(state, call.raw_task())
  let prepared_task = v3_task(state, call.prepared_task())
  let goal = canonical_goal_info(state, call.goal_info())
  state.finish([
    v3_node(b"PreparedCallV1", [
      raw_task,
      prepared_task,
      canonical_smt_token_stream(tokens),
      canonical_command(call.command()),
      goal,
    ]),
  ])
}

///|
pub fn encode_prepared_call_record(
  fixture : BytesView,
  source : BytesView,
  call : @z3.PreparedCall,
) -> Bytes raise @smtv2.PrinterError {
  let info = call.goal_info().view()
  let unit_kind = match info.unit_kind {
    TheoryUnit => b"theory"
    ModuleUnit => b"module"
  }
  let buffer = start_portable_record(
    fixture,
    source,
    b"goal",
    unit_kind,
    info.unit_name,
  )
  write_record_hex_field(buffer, b"goal_name_hex", info.goal.view().name)
  buffer.write_byte(b',')
  write_record_field_name(buffer, b"goal_ordinal")
  buffer.write_string_utf8(info.ordinal.to_string())
  write_record_text_field(buffer, b"stage", b"prepared-call", false)
  write_canonical_field(buffer, encode_prepared_call_for_source(call, fixture))
  buffer.write_bytes(b"}\n")
  buffer.to_bytes()
}

///|
fn canonical_prover_result(result : @prover.ProverResult) -> CanonicalValue {
  match result {
    Valid => canonical_array([canonical_text(b"Valid")])
    Invalid => canonical_array([canonical_text(b"Invalid")])
    Unknown(reason) =>
      canonical_array([canonical_text(b"Unknown"), canonical_hex(reason)])
    Timeout => canonical_array([canonical_text(b"Timeout")])
    OutOfMemory => canonical_array([canonical_text(b"OutOfMemory")])
    StepLimitExceeded => canonical_array([canonical_text(b"StepLimitExceeded")])
  }
}

///|
pub fn encode_prover_result(result : @prover.ProverResult) -> CanonicalJson {
  encode_canonical_value(canonical_prover_result(result))
}

///|
pub fn encode_prover_result_record(
  fixture : BytesView,
  source : BytesView,
  info : @z3.GoalInfo,
  result : @prover.ProverResult,
) -> Bytes {
  let info = info.view()
  let unit_kind = match info.unit_kind {
    TheoryUnit => b"theory"
    ModuleUnit => b"module"
  }
  let buffer = start_portable_record(
    fixture,
    source,
    b"goal",
    unit_kind,
    info.unit_name,
  )
  write_record_hex_field(buffer, b"goal_name_hex", info.goal.view().name)
  buffer.write_byte(b',')
  write_record_field_name(buffer, b"goal_ordinal")
  buffer.write_string_utf8(info.ordinal.to_string())
  write_record_text_field(buffer, b"stage", b"prover-result", false)
  write_canonical_field(buffer, encode_prover_result(result))
  buffer.write_bytes(b"}\n")
  buffer.to_bytes()
}
