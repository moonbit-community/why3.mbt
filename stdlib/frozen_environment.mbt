// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
priv struct RootMapping {
  requested : String
  requested_key : @theory.TheoryKey
  resolved_text : String
  resolved_key : @theory.TheoryKey
}

///|
struct StdlibHandles {
  builtin_module : @mlw.Pmodule
  bool_module : @mlw.Pmodule
  unit_module : @mlw.Pmodule
  int_module : @mlw.Pmodule
  real_module : @mlw.Pmodule
  bool_type : @mlw.ProgramTypeSymbol
  unit_type : @mlw.ProgramTypeSymbol
  int_type : @mlw.ProgramTypeSymbol
  real_type : @mlw.ProgramTypeSymbol
  int_negate : @mlw.RoutineSymbol
  int_less_than : @mlw.RoutineSymbol
  int_greater_equal : @mlw.RoutineSymbol
  real_negate : @mlw.RoutineSymbol
  real_add : @mlw.RoutineSymbol
  real_subtract : @mlw.RoutineSymbol
  real_multiply : @mlw.RoutineSymbol
  real_divide : @mlw.RoutineSymbol
  real_less_than : @mlw.RoutineSymbol
  real_greater_equal : @mlw.RoutineSymbol
}

///|
pub(all) struct StdlibHandlesView {
  builtin_module : @mlw.Pmodule
  bool_module : @mlw.Pmodule
  unit_module : @mlw.Pmodule
  int_module : @mlw.Pmodule
  real_module : @mlw.Pmodule
  bool_type : @mlw.ProgramTypeSymbol
  unit_type : @mlw.ProgramTypeSymbol
  int_type : @mlw.ProgramTypeSymbol
  real_type : @mlw.ProgramTypeSymbol
  int_negate : @mlw.RoutineSymbol
  int_less_than : @mlw.RoutineSymbol
  int_greater_equal : @mlw.RoutineSymbol
  real_negate : @mlw.RoutineSymbol
  real_add : @mlw.RoutineSymbol
  real_subtract : @mlw.RoutineSymbol
  real_multiply : @mlw.RoutineSymbol
  real_divide : @mlw.RoutineSymbol
  real_less_than : @mlw.RoutineSymbol
  real_greater_equal : @mlw.RoutineSymbol
}

///|
pub fn StdlibHandles::view(self : StdlibHandles) -> StdlibHandlesView {
  {
    builtin_module: self.builtin_module,
    bool_module: self.bool_module,
    unit_module: self.unit_module,
    int_module: self.int_module,
    real_module: self.real_module,
    bool_type: self.bool_type,
    unit_type: self.unit_type,
    int_type: self.int_type,
    real_type: self.real_type,
    int_negate: self.int_negate,
    int_less_than: self.int_less_than,
    int_greater_equal: self.int_greater_equal,
    real_negate: self.real_negate,
    real_add: self.real_add,
    real_subtract: self.real_subtract,
    real_multiply: self.real_multiply,
    real_divide: self.real_divide,
    real_less_than: self.real_less_than,
    real_greater_equal: self.real_greater_equal,
  }
}

///|
struct FrozenEnvironment {
  environment : @environment.Environment
  handles : StdlibHandles
  catalog : DriverSymbolCatalog
  manifest : SnapshotManifest
  semantic_projection : FrozenSemanticProjection
}

///|
priv struct FrozenSemanticProjection {
  theory_sha256 : Bytes
  module_sha256 : Bytes
}

///|
pub(all) struct FrozenSemanticProjectionView {
  theory_sha256 : Bytes
  module_sha256 : Bytes
}

///|
pub fn FrozenEnvironment::handles(self : FrozenEnvironment) -> StdlibHandles {
  self.handles
}

///|
pub fn FrozenEnvironment::driver_catalog(
  self : FrozenEnvironment,
) -> DriverSymbolCatalog {
  self.catalog
}

///|
pub fn FrozenEnvironment::manifest(
  self : FrozenEnvironment,
) -> SnapshotManifestView {
  self.manifest.view()
}

///|
pub fn FrozenEnvironment::semantic_projection(
  self : FrozenEnvironment,
) -> FrozenSemanticProjectionView {
  {
    theory_sha256: self.semantic_projection.theory_sha256,
    module_sha256: self.semantic_projection.module_sha256,
  }
}

///|
pub fn FrozenEnvironment::view(
  self : FrozenEnvironment,
) -> @environment.EnvironmentView {
  self.environment.view()
}

///|
/// Semantic environment consumed by later parser/elaboration pipeline stages.
pub fn FrozenEnvironment::semantic_environment(
  self : FrozenEnvironment,
) -> @environment.Environment {
  self.environment
}

///|
pub fn FrozenEnvironment::resolve_theory(
  self : FrozenEnvironment,
  key : @theory.TheoryKey,
  span : @identity.SourceSpan?,
) -> @theory.Theory raise @environment.EnvironmentError {
  self.environment.resolve_theory(key, span)
}

///|
pub fn FrozenEnvironment::resolve_module(
  self : FrozenEnvironment,
  key : @theory.TheoryKey,
  span : @identity.SourceSpan?,
) -> @mlw.Pmodule raise @environment.EnvironmentError {
  self.environment.resolve_module(key, span)
}

///|
pub fn FrozenEnvironment::use_theory(
  self : FrozenEnvironment,
  builder : @theory.TheoryBuilder,
  key : @theory.TheoryKey,
  import_ : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.environment.use_theory(builder, key, import_, span)
}

///|
pub fn FrozenEnvironment::use_module(
  self : FrozenEnvironment,
  builder : @mlw.PmoduleBuilder,
  key : @theory.TheoryKey,
  import_ : Bool,
  span : @identity.SourceSpan?,
) -> Unit raise {
  self.environment.use_module(builder, key, import_, span)
}

///|
fn requested_theory_key(text : String) -> @theory.TheoryKey raise {
  let bytes = string_bytes(text)
  let segments : Array[Bytes] = []
  let mut start = 0
  for index, byte in bytes {
    if byte == b'.' {
      if index == start {
        fail_snapshot(MalformedSnapshot, "$.roots", "empty root-name segment")
      }
      segments.push(bytes[start:index].to_owned())
      start = index + 1
    }
  }
  if start == bytes.length() {
    fail_snapshot(MalformedSnapshot, "$.roots", "empty root-name suffix")
  }
  let name = bytes[start:].to_owned()
  @theory.TheoryKey::new(segments, name)
}

///|
fn SnapshotDecoder::decode_root_mappings(
  self : SnapshotDecoder,
  value : Json,
  field : String,
) -> Array[RootMapping] raise {
  let root = json_object(value, "$.roots")
  let path = "$.roots." + field
  let mappings : Array[RootMapping] = []
  let seen : Map[@theory.TheoryKey, Unit] = Map([])
  for index, entry in json_array(json_field(root, field, "$.roots"), path) {
    let entry_path = path + "[" + index.to_string() + "]"
    let object = json_object(entry, entry_path)
    let requested = json_string(
      json_field(object, "requested", entry_path),
      entry_path + ".requested",
    )
    let requested_key = requested_theory_key(requested)
    if seen.contains(requested_key) {
      fail_snapshot(MalformedSnapshot, entry_path, "duplicate requested root")
    }
    seen[requested_key] = ()
    let resolved_text = json_string(
      json_field(object, "resolvedKey", entry_path),
      entry_path + ".resolvedKey",
    )
    mappings.push({
      requested,
      requested_key,
      resolved_text,
      resolved_key: self.theory_key(resolved_text, entry_path + ".resolvedKey"),
    })
  }
  mappings
}

///|
fn snapshot_payload() -> Bytes {
  let buffer = @buffer.Buffer(size_hint=10512401)
  for shard in generated_snapshot_shards() {
    for chunk in shard {
      buffer.write_bytes(chunk)
    }
  }
  buffer.to_bytes()
}

///|
fn parse_snapshot_payload(
  manifest : SnapshotManifest,
) -> Map[String, Json] raise SnapshotError {
  let payload = snapshot_payload()
  if payload.length() != manifest.payload_length {
    fail_snapshot(
      PayloadLengthMismatch,
      "$",
      "generated snapshot payload length differs from manifest",
    )
  }
  if @canonical.sha256(payload[:]) != manifest.payload_sha256 {
    fail_snapshot(
      PayloadDigestMismatch,
      "$",
      "generated snapshot payload SHA-256 differs from manifest",
    )
  }
  let text = @utf8.decode(payload[:]) catch {
    _ => fail_snapshot(InvalidUtf8, "$", "snapshot payload is not UTF-8")
  }
  let json = @json.parse(text[:]) catch {
    _ => fail_snapshot(InvalidJson, "$", "snapshot payload is not valid JSON")
  }
  json_object(json, "$")
}

///|
fn validate_root_shape(
  root : Map[String, Json],
  manifest : SnapshotManifest,
) -> Unit raise SnapshotError {
  let schema = json_int(
    json_field(root, "schemaVersion", "$"),
    "$.schemaVersion",
  )
  if schema != manifest.snapshot_schema_version {
    fail_snapshot(
      SchemaMismatch,
      "$.schemaVersion",
      "snapshot schema version drift",
    )
  }
  let theory_count = json_array(json_field(root, "theories", "$"), "$.theories").length()
  let module_count = json_array(json_field(root, "modules", "$"), "$.modules").length()
  let symbol_count = json_array(json_field(root, "catalog", "$"), "$.catalog").length()
  let type_variable_count = json_array(
    json_field(root, "typeVariables", "$"),
    "$.typeVariables",
  ).length()
  if theory_count != manifest.theory_count ||
    module_count != manifest.module_count ||
    symbol_count != manifest.symbol_count ||
    type_variable_count != manifest.type_variable_count {
    fail_snapshot(SchemaMismatch, "$", "snapshot inventory count drift")
  }
  ignore(
    json_object(json_field(root, "observedVariants", "$"), "$.observedVariants"),
  )
}

///|
fn build_environment(
  context : @identity.CompilationContext,
  theories : Map[String, @theory.Theory],
  modules : Map[String, @mlw.Pmodule],
  visible_roots : ArrayView[RootMapping],
) -> @environment.Environment raise {
  let environment = @environment.Environment::new(context)
  for entry in theories.to_array() {
    environment.register_theory(entry.1, false, None)
  }
  for entry in modules.to_array() {
    environment.register_module(entry.1, false, None)
  }
  for root in visible_roots {
    if !theories.contains(root.resolved_text) {
      fail_snapshot(
        UnknownReference,
        "$.roots.modules",
        "visible module root has no projected pure theory",
      )
    }
    if !modules.contains(root.resolved_text) {
      fail_snapshot(
        UnknownReference,
        "$.roots.modules",
        "visible module root is absent",
      )
    }
    environment.add_theory_alias(root.requested_key, root.resolved_key, None)
    environment.add_module_alias(root.requested_key, root.resolved_key, None)
  }
  environment
}

///|
fn find_visible_module(
  environment : @environment.Environment,
  name : String,
) -> @mlw.Pmodule raise {
  environment.resolve_module(requested_theory_key(name), None)
}

///|
fn build_stdlib_handles(
  environment : @environment.Environment,
) -> StdlibHandles raise {
  let builtin_module = find_visible_module(environment, "BuiltIn")
  let bool_module = find_visible_module(environment, "Bool")
  let unit_module = find_visible_module(environment, "Unit")
  let int_module = find_visible_module(environment, "int.Int")
  let real_module = find_visible_module(environment, "real.Real")
  let bool_namespace = bool_module.export_namespace()
  let unit_namespace = unit_module.export_namespace()
  let int_namespace = int_module.export_namespace()
  let real_namespace = real_module.export_namespace()
  {
    builtin_module,
    bool_module,
    unit_module,
    int_module,
    real_module,
    bool_type: bool_namespace.find_type([b"bool"], None),
    unit_type: unit_namespace.find_type([b"unit"], None),
    int_type: int_namespace.find_type([b"int"], None),
    real_type: real_namespace.find_type([b"real"], None),
    int_negate: int_namespace.find_routine([b"prefix -"], None),
    int_less_than: int_namespace.find_routine([b"infix <"], None),
    int_greater_equal: int_namespace.find_routine([b"infix >="], None),
    real_negate: real_namespace.find_routine([b"prefix -"], None),
    real_add: real_namespace.find_routine([b"infix +"], None),
    real_subtract: real_namespace.find_routine([b"infix -"], None),
    real_multiply: real_namespace.find_routine([b"infix *"], None),
    real_divide: real_namespace.find_routine([b"infix /"], None),
    real_less_than: real_namespace.find_routine([b"infix <"], None),
    real_greater_equal: real_namespace.find_routine([b"infix >="], None),
  }
}

///|
fn build_semantic_projection(
  theories : Map[String, @theory.Theory],
  modules : Map[String, @mlw.Pmodule],
) -> FrozenSemanticProjection raise {
  let theory_keys = theories.keys().to_array()
  theory_keys.sort()
  let theory_bytes = @buffer.Buffer()
  for key in theory_keys {
    theory_bytes.write_bytes(@canonical.encode_theory(theories[key]).bytes())
  }
  let module_keys = modules.keys().to_array()
  module_keys.sort()
  let module_bytes = @buffer.Buffer()
  for key in module_keys {
    module_bytes.write_bytes(@canonical.encode_pmodule(modules[key]).bytes())
  }
  {
    theory_sha256: @canonical.sha256(theory_bytes.to_bytes()),
    module_sha256: @canonical.sha256(module_bytes.to_bytes()),
  }
}

///|
/// Reconstructs the complete frozen Why3 1.7.2 semantic closure inside the
/// caller's compilation context. Runtime semantic IDs are freshly interned on
/// every call; only `SnapshotSymbolKey` values are context-free.
pub fn minimal_env(
  context : @identity.CompilationContext,
) -> FrozenEnvironment raise {
  let manifest = frozen_snapshot_manifest()
  let root = parse_snapshot_payload(manifest)
  validate_root_shape(root, manifest)
  let decoder = SnapshotDecoder::new(context, root)
  decoder.decode_type_variables(json_field(root, "typeVariables", "$"))
  decoder.decode_types()
  decoder.decode_logic_symbols()
  decoder.decode_proposition_symbols()
  decoder.decode_program_types()
  decoder.decode_routines()
  decoder.decode_theory_keys(json_field(root, "theories", "$"))
  let theories = decoder.decode_theories(json_field(root, "theories", "$"))
  let modules = decoder.decode_modules(
    json_field(root, "modules", "$"),
    theories,
  )
  let roots = json_field(root, "roots", "$")
  let theory_roots = decoder.decode_root_mappings(roots, "theories")
  let module_roots = decoder.decode_root_mappings(roots, "modules")
  if theory_roots.length() != 48 || module_roots.length() != 5 {
    fail_snapshot(SchemaMismatch, "$.roots", "snapshot root inventory drift")
  }
  for root_mapping in theory_roots {
    guard theories.get(root_mapping.resolved_text) is Some(theory) else {
      fail_snapshot(
        UnknownReference,
        "$.roots.theories",
        "driver theory root is absent from the decoded closure",
      )
    }
    if theory.key() != root_mapping.resolved_key {
      fail_snapshot(
        SemanticInvariantFailure,
        "$.roots.theories",
        "driver theory root key disagrees with its decoded theory",
      )
    }
  }
  let expected_visible = ["BuiltIn", "Bool", "Unit", "int.Int", "real.Real"]
  for index, expected in expected_visible {
    if module_roots[index].requested != expected {
      fail_snapshot(
        SchemaMismatch,
        "$.roots.modules",
        "user-visible program root order drift",
      )
    }
  }
  let catalog = decoder.build_catalog()
  if catalog.length() != manifest.symbol_count {
    fail_snapshot(SchemaMismatch, "$.catalog", "decoded catalog count drift")
  }
  let environment = build_environment(context, theories, modules, module_roots)
  {
    environment,
    handles: build_stdlib_handles(environment),
    catalog,
    manifest,
    semantic_projection: build_semantic_projection(theories, modules),
  }
}
