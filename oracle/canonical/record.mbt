// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
let semantic_profile_sha256_v1 : Bytes = b"f788bd465967b186e1db9f910b8e04e3f4803413a705b661bafc2da5d07658ab"

///|
fn write_record_field_name(buffer : @buffer.Buffer, name : BytesView) -> Unit {
  write_json_string(buffer, name)
  buffer.write_byte(b':')
}

///|
fn write_record_text_field(
  buffer : @buffer.Buffer,
  name : BytesView,
  value : BytesView,
  first : Bool,
) -> Unit {
  if !first {
    buffer.write_byte(b',')
  }
  write_record_field_name(buffer, name)
  write_json_string(buffer, value)
}

///|
fn write_record_hex_field(
  buffer : @buffer.Buffer,
  name : BytesView,
  value : BytesView,
) -> Unit {
  buffer.write_byte(b',')
  write_record_field_name(buffer, name)
  write_json_string(buffer, bytes_to_lower_hex(value))
}

///|
fn write_canonical_field(
  buffer : @buffer.Buffer,
  canonical : CanonicalJson,
) -> Unit {
  buffer.write_byte(b',')
  write_record_field_name(buffer, b"canonical_sha256")
  write_json_string(buffer, canonical.sha256_hex())
  buffer.write_byte(b',')
  write_record_field_name(buffer, b"canonical")
  let bytes = canonical.bytes()
  guard bytes.length() > 0 && bytes[bytes.length() - 1] == b'\n' else {
    abort("canonical semantic payload must end in exactly one LF")
  }
  buffer.write_bytes(bytes[:bytes.length() - 1])
}

///|
fn start_portable_record(
  fixture : BytesView,
  source : BytesView,
  scope : BytesView,
  unit_kind : BytesView,
  unit_name : BytesView,
) -> @buffer.Buffer {
  let buffer = @buffer.Buffer()
  buffer.write_byte(b'{')
  write_record_field_name(buffer, b"schema")
  buffer.write_byte(b'2')
  write_record_text_field(
    buffer, b"semantic_profile_sha256", semantic_profile_sha256_v1, false,
  )
  write_record_text_field(buffer, b"fixture", fixture, false)
  write_record_text_field(buffer, b"source_sha256", sha256_hex(source), false)
  write_record_text_field(buffer, b"scope", scope, false)
  write_record_text_field(buffer, b"unit_kind", unit_kind, false)
  write_record_hex_field(buffer, b"unit_name_hex", unit_name)
  buffer
}

///|
/// Encodes one portable typed-unit NDJSON record. The returned bytes contain
/// exactly one final LF and are ready to write to stdout or hash as a record.
pub fn encode_typed_theory_record(
  fixture : BytesView,
  source : BytesView,
  theory : @theory.Theory,
) -> Bytes {
  let view = theory.view()
  let buffer = start_portable_record(
    fixture,
    source,
    b"unit",
    b"theory",
    view.name.view().name,
  )
  write_record_text_field(buffer, b"stage", b"typed-semantic", false)
  write_canonical_field(buffer, encode_theory(theory))
  buffer.write_bytes(b"}\n")
  buffer.to_bytes()
}

///|
/// Encodes one portable typed program-module NDJSON record.
pub fn encode_typed_module_record(
  fixture : BytesView,
  source : BytesView,
  pmodule : @mlw.Pmodule,
) -> Bytes raise {
  let view = pmodule.pure_theory().view()
  let buffer = start_portable_record(
    fixture,
    source,
    b"unit",
    b"module",
    view.name.view().name,
  )
  write_record_text_field(buffer, b"stage", b"typed-program", false)
  write_canonical_field(buffer, encode_pmodule(pmodule))
  buffer.write_bytes(b"}\n")
  buffer.to_bytes()
}

///|
fn task_goal_name(task : @theory.Task) -> BytesView {
  let items = task.view().items
  guard !items.is_empty() &&
    items[items.length() - 1] is TheoryDecl(goal) &&
    goal.view() is Dprop(Pgoal, proposition, _) else {
    abort("validated raw task has no final goal")
  }
  proposition.view().name[:]
}

///|
/// Encodes one portable raw-task NDJSON record in source-goal order.
pub fn encode_raw_task_record(
  fixture : BytesView,
  source : BytesView,
  unit_name : BytesView,
  goal_ordinal : Int,
  task : @theory.Task,
) -> Bytes {
  encode_task_checkpoint_record(
    fixture,
    source,
    unit_name,
    task_goal_name(task),
    goal_ordinal,
    b"raw-task",
    task,
  )
}

///|
/// Encodes one goal-scoped Task checkpoint. `goal_name` is the name from the
/// raw Task inventory and therefore remains stable even if a transform
/// replaces the goal proposition symbol.
pub fn encode_task_checkpoint_record(
  fixture : BytesView,
  source : BytesView,
  unit_name : BytesView,
  goal_name : BytesView,
  goal_ordinal : Int,
  stage : BytesView,
  task : @theory.Task,
) -> Bytes {
  if goal_ordinal < 0 {
    abort("goal ordinal cannot be negative")
  }
  let buffer = start_portable_record(
    fixture, source, b"goal", b"theory", unit_name,
  )
  write_record_hex_field(buffer, b"goal_name_hex", goal_name)
  buffer.write_byte(b',')
  write_record_field_name(buffer, b"goal_ordinal")
  buffer.write_string_utf8(goal_ordinal.to_string())
  write_record_text_field(buffer, b"stage", stage, false)
  write_canonical_field(buffer, encode_task(task))
  buffer.write_bytes(b"}\n")
  buffer.to_bytes()
}
