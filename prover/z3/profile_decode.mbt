// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn json_object(
  value : Json,
  path : String,
) -> Map[String, Json] raise BindError {
  match value {
    Object(fields) => fields
    _ => fail_bind(InvalidProfile, path, "expected a JSON object")
  }
}

///|
fn json_array(value : Json, path : String) -> Array[Json] raise BindError {
  match value {
    Array(values) => values
    _ => fail_bind(InvalidProfile, path, "expected a JSON array")
  }
}

///|
fn json_string(value : Json, path : String) -> String raise BindError {
  match value {
    String(text) => text
    _ => fail_bind(InvalidProfile, path, "expected a JSON string")
  }
}

///|
fn json_int(value : Json, path : String) -> Int raise BindError {
  match value {
    Number(number, ..) => {
      let integer = number.to_int()
      if integer.to_double() != number {
        fail_bind(InvalidProfile, path, "expected an integral JSON number")
      }
      integer
    }
    _ => fail_bind(InvalidProfile, path, "expected a JSON number")
  }
}

///|
fn json_field(
  object : Map[String, Json],
  name : String,
  path : String,
) -> Json raise BindError {
  match object.get(name) {
    Some(value) => value
    None => fail_bind(InvalidProfile, path, "missing field " + name)
  }
}

///|
fn string_bytes(text : String) -> Bytes {
  @utf8.encode(text)
}

///|
fn decode_hex_nibble(byte : Byte, path : String) -> Byte raise BindError {
  let value = byte.to_int()
  if value >= b'0'.to_int() && value <= b'9'.to_int() {
    (value - b'0'.to_int()).to_byte()
  } else if value >= b'a'.to_int() && value <= b'f'.to_int() {
    (10 + value - b'a'.to_int()).to_byte()
  } else {
    fail_bind(InvalidProfile, path, "invalid lowercase hexadecimal text")
  }
}

///|
fn decode_hex(text : String, path : String) -> Bytes raise BindError {
  let encoded = string_bytes(text)
  if encoded.length() % 2 != 0 {
    fail_bind(InvalidProfile, path, "hexadecimal text has odd length")
  }
  let result : Array[Byte] = []
  for index = 0; index < encoded.length() / 2; index = index + 1 {
    let high = decode_hex_nibble(encoded[index * 2], path).to_int()
    let low = decode_hex_nibble(encoded[index * 2 + 1], path).to_int()
    result.push((high * 16 + low).to_byte())
  }
  Bytes::from_array(result)
}

///|
fn theory_key_from_string(
  text : String,
  path : String,
) -> @theory.TheoryKey raise BindError {
  let encoded = string_bytes(text)
  let segments : Array[Bytes] = []
  let mut start = 0
  for index, byte in encoded {
    if byte == b'.' {
      if index == start {
        fail_bind(InvalidProfile, path, "empty theory-key segment")
      }
      segments.push(encoded[start:index].to_owned())
      start = index + 1
    }
  }
  if start == encoded.length() {
    fail_bind(InvalidProfile, path, "empty theory-key suffix")
  }
  let name = encoded[start:].to_owned()
  @theory.TheoryKey::new(segments, name) catch {
    _ => fail_bind(InvalidProfile, path, "invalid theory key")
  }
}

///|
fn symbol_kind(
  text : String,
  path : String,
) -> @identity.SnapshotSymbolKind raise BindError {
  match text {
    "type" => Type
    "logic" => Logic
    "proposition" => Proposition
    "program" => Program
    "region" => Region
    _ => fail_bind(InvalidProfile, path, "unknown snapshot symbol kind")
  }
}

///|
fn snapshot_key(
  value : Json,
  path : String,
) -> @identity.SnapshotSymbolKey raise BindError {
  let object = json_object(value, path)
  let theory = json_string(
    json_field(object, "theoryKey", path),
    path + ".theoryKey",
  )
  let item = json_int(
    json_field(object, "theoryItemOrdinal", path),
    path + ".theoryItemOrdinal",
  )
  let inner = json_int(
    json_field(object, "declarationInnerOrdinal", path),
    path + ".declarationInnerOrdinal",
  )
  if item < 0 || inner < 0 {
    fail_bind(InvalidProfile, path, "negative snapshot symbol ordinal")
  }
  let kind_text = json_string(
    json_field(object, "symbolKind", path),
    path + ".symbolKind",
  )
  let digest = decode_hex(
    json_string(json_field(object, "digest", path), path + ".digest"),
    path + ".digest",
  )
  if digest.length() != 32 {
    fail_bind(InvalidProfile, path, "snapshot symbol digest is not SHA-256")
  }
  @identity.SnapshotSymbolKey::new(
    string_bytes(theory),
    item.reinterpret_as_uint(),
    inner.reinterpret_as_uint(),
    symbol_kind(kind_text, path + ".symbolKind"),
    digest,
  )
}

///|
fn unbound_ty(value : Json, path : String) -> UnboundTy raise BindError {
  let object = json_object(value, path)
  match json_string(json_field(object, "kind", path), path + ".kind") {
    "variable" =>
      UnboundTyVariable(
        string_bytes(
          json_string(json_field(object, "name", path), path + ".name"),
        ),
      )
    "application" => {
      let arguments : Array[UnboundTy] = []
      for
        index, argument in json_array(
          json_field(object, "arguments", path),
          path + ".arguments",
        ) {
        arguments.push(
          unbound_ty(argument, path + ".arguments[" + index.to_string() + "]"),
        )
      }
      UnboundTyApplication(
        snapshot_key(json_field(object, "symbol", path), path + ".symbol"),
        arguments,
      )
    }
    _ => fail_bind(InvalidProfile, path + ".kind", "unknown unbound type kind")
  }
}

///|
fn unbound_meta_argument(
  value : Json,
  path : String,
) -> UnboundMetaArgument raise BindError {
  let object = json_object(value, path)
  match json_string(json_field(object, "kind", path), path + ".kind") {
    "type" =>
      UnboundMetaType(
        unbound_ty(json_field(object, "value", path), path + ".value"),
      )
    "typeSymbol" =>
      UnboundMetaTypeSymbol(
        snapshot_key(json_field(object, "value", path), path + ".value"),
      )
    "logicSymbol" =>
      UnboundMetaLogicSymbol(
        snapshot_key(json_field(object, "value", path), path + ".value"),
      )
    "propositionSymbol" =>
      UnboundMetaPropositionSymbol(
        snapshot_key(json_field(object, "value", path), path + ".value"),
      )
    "string" =>
      UnboundMetaString(
        string_bytes(
          json_string(json_field(object, "value", path), path + ".value"),
        ),
      )
    "integer" =>
      UnboundMetaInteger(
        json_int(json_field(object, "value", path), path + ".value").to_int64(),
      )
    "identifier" =>
      UnboundMetaIdentifier(
        string_bytes(
          json_string(json_field(object, "name", path), path + ".name"),
        ),
      )
    _ => fail_bind(InvalidProfile, path + ".kind", "unknown meta argument kind")
  }
}

///|
fn unbound_meta(
  value : Json,
  path : String,
  ordinal : Int,
) -> UnboundDriverMeta raise BindError {
  let object = json_object(value, path)
  if json_int(json_field(object, "ordinal", path), path + ".ordinal") != ordinal {
    fail_bind(
      InvalidProfile,
      path + ".ordinal",
      "meta ordinal is not contiguous",
    )
  }
  let arguments : Array[UnboundMetaArgument] = []
  for
    index, argument in json_array(
      json_field(object, "arguments", path),
      path + ".arguments",
    ) {
    arguments.push(
      unbound_meta_argument(
        argument,
        path + ".arguments[" + index.to_string() + "]",
      ),
    )
  }
  {
    name: string_bytes(
      json_string(json_field(object, "name", path), path + ".name"),
    ),
    arguments,
  }
}

///|
fn unbound_meta_groups(
  value : Json,
  path : String,
) -> Array[UnboundMetaGroup] raise BindError {
  let groups : Array[UnboundMetaGroup] = []
  for group_index, value in json_array(value, path) {
    let group_path = path + "[" + group_index.to_string() + "]"
    let object = json_object(value, group_path)
    let entries : Array[UnboundDriverMeta] = []
    for
      index, entry in json_array(
        json_field(object, "entries", group_path),
        group_path + ".entries",
      ) {
      entries.push(
        unbound_meta(
          entry,
          group_path + ".entries[" + index.to_string() + "]",
          index,
        ),
      )
    }
    groups.push({
      theory_key: theory_key_from_string(
        json_string(
          json_field(object, "theoryKey", group_path),
          group_path + ".theoryKey",
        ),
        group_path + ".theoryKey",
      ),
      entries,
    })
  }
  groups
}

///|
fn theory_preludes(
  value : Json,
  path : String,
) -> Array[TheoryPrelude] raise BindError {
  let groups : Array[TheoryPrelude] = []
  for index, value in json_array(value, path) {
    let group_path = path + "[" + index.to_string() + "]"
    let object = json_object(value, group_path)
    groups.push({
      theory_key: theory_key_from_string(
        json_string(
          json_field(object, "theoryKey", group_path),
          group_path + ".theoryKey",
        ),
        group_path + ".theoryKey",
      ),
      values: byte_strings(
        json_field(object, "values", group_path),
        group_path + ".values",
      ),
    })
  }
  groups
}

///|
fn transform_id(text : String, path : String) -> TransformId raise BindError {
  match text {
    "counterexamples_dependent_intros" => CounterexamplesDependentIntros
    "inline_trivial" => InlineTrivial
    "eliminate_builtin" => EliminateBuiltin
    "remove_unused_keep_constants" => RemoveUnusedKeepConstants
    "detect_polymorphism" => DetectPolymorphism
    "eliminate_definition_conditionally" => EliminateDefinitionConditionally
    "eliminate_inductive" => EliminateInductive
    "eliminate_epsilon" => EliminateEpsilon
    "eliminate_literal" => EliminateLiteral
    "simplify_formula" => SimplifyFormula
    "prepare_for_counterexmp" => PrepareForCounterexmp
    "eliminate_projections_sums" => EliminateProjectionsSums
    "discriminate_if_poly" => DiscriminateIfPoly
    "eliminate_algebraic_if_poly" => EliminateAlgebraicIfPoly
    "encoding_smt_if_poly" => EncodingSmtIfPoly
    _ => fail_bind(InvalidProfile, path, "unknown driver transform")
  }
}

///|
fn byte_strings(value : Json, path : String) -> Array[Bytes] raise BindError {
  let result : Array[Bytes] = []
  for index, entry in json_array(value, path) {
    result.push(
      string_bytes(json_string(entry, path + "[" + index.to_string() + "]")),
    )
  }
  result
}

///|
fn prover_answer_rule(
  value : Json,
  path : String,
) -> ProverAnswerRule raise BindError {
  let object = json_object(value, path)
  match json_string(json_field(object, "kind", path), path + ".kind") {
    "valid" => RuleValid
    "invalid" => RuleInvalid
    "timeout" => RuleTimeout
    "outOfMemory" => RuleOutOfMemory
    "stepLimitExceeded" => RuleStepLimitExceeded
    "unknown" =>
      RuleUnknown(
        string_bytes(
          json_string(json_field(object, "message", path), path + ".message"),
        ),
      )
    "failure" =>
      RuleFailure(
        string_bytes(
          json_string(json_field(object, "message", path), path + ".message"),
        ),
      )
    "highFailure" => RuleHighFailure
    _ => fail_bind(InvalidProfile, path + ".kind", "unknown result answer")
  }
}

///|
fn result_regexps(
  value : Json,
  path : String,
) -> Array[ResultRegexp] raise BindError {
  let result : Array[ResultRegexp] = []
  for index, entry in json_array(value, path) {
    let entry_path = path + "[" + index.to_string() + "]"
    let object = json_object(entry, entry_path)
    result.push({
      pattern: string_bytes(
        json_string(
          json_field(object, "pattern", entry_path),
          entry_path + ".pattern",
        ),
      ),
      answer: prover_answer_rule(
        json_field(object, "answer", entry_path),
        entry_path + ".answer",
      ),
    })
  }
  result
}

///|
fn result_exit_codes(
  value : Json,
  path : String,
) -> Array[ResultExitCode] raise BindError {
  let result : Array[ResultExitCode] = []
  for index, entry in json_array(value, path) {
    let entry_path = path + "[" + index.to_string() + "]"
    let object = json_object(entry, entry_path)
    result.push({
      code: json_int(
        json_field(object, "code", entry_path),
        entry_path + ".code",
      ),
      answer: prover_answer_rule(
        json_field(object, "answer", entry_path),
        entry_path + ".answer",
      ),
    })
  }
  result
}

///|
fn derive_printer_entries(
  groups : ArrayView[UnboundMetaGroup],
) -> (Array[UnboundSyntaxEntry], Array[@identity.SnapshotSymbolKey]) {
  let syntax : Array[UnboundSyntaxEntry] = []
  let remove : Array[@identity.SnapshotSymbolKey] = []
  for group in groups {
    for meta in group.entries {
      match (meta.name, meta.arguments) {
        (
          b"syntax_type",
          [
            UnboundMetaTypeSymbol(symbol),
            UnboundMetaString(template),
            UnboundMetaInteger(overriding),
          ],
        ) =>
          syntax.push({
            kind: TypeSyntax,
            symbol,
            template,
            overriding: overriding != 0L,
          })
        (
          b"syntax_logic",
          [
            UnboundMetaLogicSymbol(symbol),
            UnboundMetaString(template),
            UnboundMetaInteger(overriding),
          ],
        ) =>
          syntax.push({
            kind: LogicSyntax,
            symbol,
            template,
            overriding: overriding != 0L,
          })
        (
          b"syntax_literal",
          [
            UnboundMetaTypeSymbol(symbol),
            UnboundMetaString(template),
            UnboundMetaInteger(overriding),
          ],
        ) =>
          syntax.push({
            kind: LiteralSyntax,
            symbol,
            template,
            overriding: overriding != 0L,
          })
        (b"remove_prop", [UnboundMetaPropositionSymbol(symbol)]) =>
          remove.push(symbol)
        _ => ()
      }
    }
  }
  (syntax, remove)
}

///|
fn profile_payload() -> Bytes {
  let buffer = @buffer.Buffer(size_hint=984000)
  for shard in generated_z3_profile_shards() {
    for chunk in shard {
      buffer.write_bytes(chunk)
    }
  }
  buffer.to_bytes()
}

///|
pub fn z3_static_spec() -> Z3StaticSpec raise BindError {
  let payload = profile_payload()
  let text = @utf8.decode(payload[:]) catch {
    _ => fail_bind(InvalidProfile, "$", "static profile is not UTF-8")
  }
  let root = @json.parse(text[:]) catch {
    _ => fail_bind(InvalidProfile, "$", "static profile is not valid JSON")
  }
  let object = json_object(root, "$")
  if json_int(json_field(object, "schemaVersion", "$"), "$.schemaVersion") != 1 {
    fail_bind(
      InvalidProfile,
      "$.schemaVersion",
      "unsupported static profile schema",
    )
  }
  let why3 = json_object(json_field(object, "why3", "$"), "$.why3")
  if json_string(json_field(why3, "version", "$.why3"), "$.why3.version") !=
    "1.7.2" ||
    json_string(json_field(why3, "commit", "$.why3"), "$.why3.commit") !=
    "1343338d3bb1941c0d4f134283bb0790816113c4" ||
    json_string(json_field(why3, "tree", "$.why3"), "$.why3.tree") !=
    "f5e82693620413d7d8e3ebcba69addcb6a65f877" {
    fail_bind(InvalidProfile, "$.why3", "Why3 profile identity drift")
  }
  if json_string(json_field(object, "driverProfile", "$"), "$.driverProfile") !=
    "z3_487" ||
    json_string(json_field(object, "printer", "$"), "$.printer") != "smtv2.6" {
    fail_bind(InvalidProfile, "$", "Z3 driver identity drift")
  }
  let transforms : Array[TransformId] = []
  for
    index, entry in json_array(
      json_field(object, "transforms", "$"),
      "$.transforms",
    ) {
    transforms.push(
      transform_id(
        json_string(entry, "$.transforms[" + index.to_string() + "]"),
        "$.transforms[" + index.to_string() + "]",
      ),
    )
  }
  if transforms.length() != 15 {
    fail_bind(InvalidProfile, "$.transforms", "Z3 transform count drift")
  }
  let meta_groups = unbound_meta_groups(
    json_field(object, "driverMetaGroups", "$"),
    "$.driverMetaGroups",
  )
  let snapshot_meta_groups = unbound_meta_groups(
    json_field(object, "snapshotMetaClosure", "$"),
    "$.snapshotMetaClosure",
  )
  if meta_groups.length() != 48 ||
    meta_count(meta_groups) != 992 ||
    snapshot_meta_groups.length() != 14 ||
    meta_count(snapshot_meta_groups) != 491 {
    fail_bind(InvalidProfile, "$", "static profile inventory drift")
  }
  let (syntax, remove) = derive_printer_entries(meta_groups)
  let theory_preludes = theory_preludes(
    json_field(object, "theoryPreludes", "$"),
    "$.theoryPreludes",
  )
  if theory_preludes.length() != 5 {
    fail_bind(InvalidProfile, "$.theoryPreludes", "theory prelude count drift")
  }
  let command_object = json_object(
    json_field(object, "command", "$"),
    "$.command",
  )
  let checkpoints = json_object(
    json_field(
      json_object(json_field(object, "tracePatch", "$"), "$.tracePatch"),
      "checkpointSequences",
      "$.tracePatch",
    ),
    "$.tracePatch.checkpointSequences",
  )
  {
    printer: SmtV26,
    transforms,
    meta_groups,
    snapshot_meta_groups,
    syntax,
    remove,
    preludes: byte_strings(json_field(object, "preludes", "$"), "$.preludes"),
    theory_preludes,
    result_regexps: result_regexps(
      json_field(object, "resultRegexps", "$"),
      "$.resultRegexps",
    ),
    result_exit_codes: result_exit_codes(
      json_field(object, "resultExitCodes", "$"),
      "$.resultExitCodes",
    ),
    command: {
      executable: string_bytes(
        json_string(
          json_field(command_object, "executable", "$.command"),
          "$.command.executable",
        ),
      ),
      common_arguments: byte_strings(
        json_field(command_object, "commonArguments", "$.command"),
        "$.command.commonArguments",
      ),
      time_limit_argument: string_bytes(
        json_string(
          json_field(command_object, "timeLimitArgument", "$.command"),
          "$.command.timeLimitArgument",
        ),
      ),
      step_limit_argument: string_bytes(
        json_string(
          json_field(command_object, "stepLimitArgument", "$.command"),
          "$.command.stepLimitArgument",
        ),
      ),
    },
    monomorphic_checkpoints: byte_strings(
      json_field(checkpoints, "monomorphic", "$.tracePatch.checkpointSequences"),
      "$.tracePatch.checkpointSequences.monomorphic",
    ),
    polymorphic_checkpoints: byte_strings(
      json_field(checkpoints, "polymorphic", "$.tracePatch.checkpointSequences"),
      "$.tracePatch.checkpointSequences.polymorphic",
    ),
  }
}
