// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
priv struct CatalogDescriptor {
  path : String
  locator : String
  key : @identity.SnapshotSymbolKey
  tag : String
  symbol : Json
}

///|
priv struct SnapshotDecoder {
  context : @identity.CompilationContext
  descriptors : Array[CatalogDescriptor]
  type_variables : Map[Int, @logic.TyVarSymbol]
  types : Map[String, @logic.TypeSymbol]
  logic : Map[String, @logic.LSymbol]
  propositions : Map[String, @logic.PrSymbol]
  program_types : Map[String, @mlw.ProgramTypeSymbol]
  routines : Map[String, @mlw.RoutineSymbol]
  theory_keys : Map[String, @theory.TheoryKey]
}

///|
fn snapshot_symbol_kind(
  text : String,
  path : String,
) -> @identity.SnapshotSymbolKind raise SnapshotError {
  match text {
    "type" => Type
    "logic" => Logic
    "proposition" => Proposition
    "program" => Program
    "region" => Region
    _ => fail_snapshot(MalformedSnapshot, path, "unknown snapshot symbol kind")
  }
}

///|
fn catalog_descriptor(
  value : Json,
  index : Int,
) -> CatalogDescriptor raise SnapshotError {
  let path = "$.catalog[" + index.to_string() + "]"
  let entry = json_object(value, path)
  let locator_object = json_object(
    json_field(entry, "locator", path),
    path + ".locator",
  )
  let key_object = json_object(json_field(entry, "key", path), path + ".key")
  let locator = json_string(
    json_field(locator_object, "id", path),
    path + ".locator.id",
  )
  let locator_theory = json_string(
    json_field(locator_object, "theoryKey", path),
    path + ".locator.theoryKey",
  )
  let locator_item = json_int(
    json_field(locator_object, "itemOrdinal", path),
    path + ".locator.itemOrdinal",
  )
  let locator_inner = json_int(
    json_field(locator_object, "innerOrdinal", path),
    path + ".locator.innerOrdinal",
  )
  let locator_kind = json_string(
    json_field(locator_object, "kind", path),
    path + ".locator.kind",
  )
  let expected_locator = locator_theory +
    "#" +
    locator_item.to_string() +
    "#" +
    locator_inner.to_string() +
    "#" +
    locator_kind
  if locator != expected_locator {
    fail_snapshot(MalformedSnapshot, path, "catalog locator fields disagree")
  }
  let key_theory = json_string(
    json_field(key_object, "theoryKey", path),
    path + ".key.theoryKey",
  )
  let key_item = json_int(
    json_field(key_object, "theoryItemOrdinal", path),
    path + ".key.theoryItemOrdinal",
  )
  let key_inner = json_int(
    json_field(key_object, "declarationInnerOrdinal", path),
    path + ".key.declarationInnerOrdinal",
  )
  let key_kind = json_string(
    json_field(key_object, "symbolKind", path),
    path + ".key.symbolKind",
  )
  if key_theory != locator_theory ||
    key_item != locator_item ||
    key_inner != locator_inner ||
    key_kind != locator_kind {
    fail_snapshot(MalformedSnapshot, path, "catalog key and locator disagree")
  }
  if key_item < 0 || key_inner < 0 {
    fail_snapshot(MalformedSnapshot, path, "negative catalog ordinal")
  }
  let digest = decode_hex(
    json_string(json_field(key_object, "digest", path), path + ".key.digest"),
    path + ".key.digest",
  )
  if digest.length() != 32 {
    fail_snapshot(MalformedSnapshot, path, "catalog digest is not SHA-256")
  }
  let symbol = json_field(entry, "symbol", path)
  let symbol_object = json_object(symbol, path + ".symbol")
  let tag = json_string(
    json_field(symbol_object, "tag", path),
    path + ".symbol.tag",
  )
  let shape = json_string(
    json_field(locator_object, "shape", path),
    path + ".locator.shape",
  )
  let expected_shape = match tag {
    "TypeSymbol" => "typeSymbol"
    "LogicSymbol" => "logicSymbol"
    "PropositionSymbol" => "propositionSymbol"
    "ProgramTypeSymbol" => "programTypeSymbol"
    "RoutineSymbol" => "routineSymbol"
    _ =>
      fail_snapshot(
        UnsupportedSnapshotVariant,
        path,
        "unknown catalog symbol tag",
      )
  }
  if shape != expected_shape {
    fail_snapshot(
      MalformedSnapshot,
      path,
      "catalog shape and symbol tag disagree",
    )
  }
  let expected_kind = match tag {
    "TypeSymbol" => "type"
    "LogicSymbol" => "logic"
    "PropositionSymbol" => "proposition"
    "ProgramTypeSymbol" | "RoutineSymbol" => "program"
    _ => abort("catalog tag was validated above")
  }
  if key_kind != expected_kind {
    fail_snapshot(
      MalformedSnapshot,
      path,
      "catalog kind and symbol tag disagree",
    )
  }
  {
    path,
    locator,
    key: @identity.SnapshotSymbolKey::new(
      string_bytes(key_theory),
      key_item.reinterpret_as_uint(),
      key_inner.reinterpret_as_uint(),
      snapshot_symbol_kind(key_kind, path + ".key.symbolKind"),
      digest,
    ),
    tag,
    symbol,
  }
}

///|
fn SnapshotDecoder::new(
  context : @identity.CompilationContext,
  root : Map[String, Json],
) -> SnapshotDecoder raise SnapshotError {
  let descriptor_json = json_array(
    json_field(root, "catalog", "$"),
    "$.catalog",
  )
  let descriptors : Array[CatalogDescriptor] = []
  let seen_locators : Map[String, Unit] = Map([])
  for index, entry in descriptor_json {
    let descriptor = catalog_descriptor(entry, index)
    if seen_locators.contains(descriptor.locator) {
      fail_snapshot(
        DuplicateCatalogEntry,
        descriptor.path,
        "duplicate catalog locator",
      )
    }
    seen_locators[descriptor.locator] = ()
    descriptors.push(descriptor)
  }
  {
    context,
    descriptors,
    type_variables: Map([]),
    types: Map([]),
    logic: Map([]),
    propositions: Map([]),
    program_types: Map([]),
    routines: Map([]),
    theory_keys: Map([]),
  }
}

///|
fn SnapshotDecoder::decode_type_variables(
  self : SnapshotDecoder,
  value : Json,
) -> Unit raise SnapshotError {
  for index, entry in json_array(value, "$.typeVariables") {
    let path = "$.typeVariables[" + index.to_string() + "]"
    let object = json_object(entry, path)
    let id = json_int(json_field(object, "id", path), path + ".id")
    if id < 0 {
      fail_snapshot(MalformedSnapshot, path, "negative type variable id")
    }
    if self.type_variables.contains(id) {
      fail_snapshot(MalformedSnapshot, path, "duplicate type variable id")
    }
    let name = semantic_name(json_field(object, "name", path), path + ".name")
    let view = name.view()
    let key = @identity.SnapshotSymbolKey::new(
      b"__snapshot.typeVariables",
      id.reinterpret_as_uint(),
      0U,
      Type,
      Bytes::make(32, b'\x00'),
    )
    self.type_variables[id] = @logic.TyVarSymbol::new(
      self.context,
      view.name,
      @identity.Origin::snapshot_with_span(
        view.name,
        key,
        view.source_span,
        view.attributes,
      ),
    )
  }
}

///|
fn SnapshotDecoder::type_variable(
  self : SnapshotDecoder,
  id : Int,
  path : String,
) -> @logic.TyVarSymbol raise SnapshotError {
  match self.type_variables.get(id) {
    Some(variable) => variable
    None => fail_snapshot(UnknownReference, path, "unknown type variable id")
  }
}

///|
fn SnapshotDecoder::type_symbol(
  self : SnapshotDecoder,
  locator : String,
  path : String,
) -> @logic.TypeSymbol raise SnapshotError {
  match self.types.get(locator) {
    Some(symbol) => symbol
    None => fail_snapshot(UnknownReference, path, "unknown type symbol locator")
  }
}

///|
fn SnapshotDecoder::decode_ty(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> @logic.Ty raise {
  let (tag, fields) = tagged(value, path)
  match tag {
    "TyVar" => {
      require_tag_arity(fields, 1, path)
      @logic.Ty::variable(self.type_variable(json_int(fields[1], path), path))
    }
    "TyApp" => {
      require_tag_arity(fields, 2, path)
      let locator = json_string(fields[1], path + "[1]")
      let arguments = [
        for index, argument in json_array(fields[2], path + "[2]") => {
          self.decode_ty(argument, path + "[2][" + index.to_string() + "]")
        }
      ]
      @logic.Ty::app(self.type_symbol(locator, path + "[1]"), arguments, None)
    }
    _ => fail_snapshot(UnsupportedSnapshotVariant, path, "unknown type node")
  }
}

///|
fn SnapshotDecoder::decode_optional_ty(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> @logic.Ty? raise {
  match value {
    Null => None
    _ => Some(self.decode_ty(value, path))
  }
}

///|
fn SnapshotDecoder::decode_type_parameters(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> Array[@logic.TyVarSymbol] raise SnapshotError {
  [
    for index, entry in json_array(value, path) => {
      self.type_variable(
        json_int(entry, path + "[" + index.to_string() + "]"),
        path + "[" + index.to_string() + "]",
      )
    }
  ]
}

///|
fn builtin_type_kind(
  value : Json,
  path : String,
) -> @logic.BuiltinTypeKind? raise SnapshotError {
  match value {
    Null => None
    String("integer") => Some(BuiltinInteger)
    String("real") => Some(BuiltinReal)
    String("boolean") => Some(BuiltinBoolean)
    String("string") => Some(BuiltinString)
    _ => fail_snapshot(MalformedSnapshot, path, "unknown builtin type kind")
  }
}

///|
fn SnapshotDecoder::decode_non_alias_type(
  self : SnapshotDecoder,
  descriptor : CatalogDescriptor,
) -> Unit raise {
  let path = descriptor.path + ".symbol"
  let object = json_object(descriptor.symbol, path)
  let name = semantic_name(json_field(object, "name", path), path + ".name")
  let origin = origin_from_name(name, descriptor.key)
  let name_view = name.view()
  let parameters = self.decode_type_parameters(
    json_field(object, "typeParameters", path),
    path + ".typeParameters",
  )
  let (definition_tag, definition) = tagged(
    json_field(object, "definition", path),
    path + ".definition",
  )
  if definition_tag == "Alias" {
    return
  }
  let builtin = builtin_type_kind(
    json_field(object, "builtinKind", path),
    path + ".builtinKind",
  )
  let symbol = match definition_tag {
    "NoDef" => {
      require_tag_arity(definition, 0, path + ".definition")
      match builtin {
        Some(kind) => {
          if !parameters.is_empty() {
            fail_snapshot(
              MalformedSnapshot,
              path,
              "builtin type has type parameters",
            )
          }
          @logic.TypeSymbol::trusted_builtin(
            self.context,
            name_view.name,
            origin,
            kind,
            name_view.source_span,
          )
        }
        None =>
          @logic.TypeSymbol::new_abstract(
            self.context,
            name_view.name,
            origin,
            parameters,
            name_view.source_span,
          )
      }
    }
    "Range" => {
      require_tag_arity(definition, 2, path + ".definition")
      if !parameters.is_empty() || builtin is Some(_) {
        fail_snapshot(MalformedSnapshot, path, "Range metadata is invalid")
      }
      @logic.TypeSymbol::trusted_range(
        self.context,
        name_view.name,
        origin,
        @bigint.BigInt::from_string(json_string(definition[1], path)),
        @bigint.BigInt::from_string(json_string(definition[2], path)),
        name_view.source_span,
      )
    }
    "Float" => {
      require_tag_arity(definition, 2, path + ".definition")
      if !parameters.is_empty() || builtin is Some(_) {
        fail_snapshot(MalformedSnapshot, path, "Float metadata is invalid")
      }
      @logic.TypeSymbol::trusted_float(
        self.context,
        name_view.name,
        origin,
        json_int(definition[1], path),
        json_int(definition[2], path),
        name_view.source_span,
      )
    }
    _ =>
      fail_snapshot(
        UnsupportedSnapshotVariant,
        path,
        "unknown type symbol definition",
      )
  }
  self.types[descriptor.locator] = symbol
}

///|
fn SnapshotDecoder::decode_alias_type(
  self : SnapshotDecoder,
  descriptor : CatalogDescriptor,
) -> Unit raise {
  let path = descriptor.path + ".symbol"
  let object = json_object(descriptor.symbol, path)
  let (definition_tag, definition) = tagged(
    json_field(object, "definition", path),
    path + ".definition",
  )
  if definition_tag != "Alias" {
    return
  }
  require_tag_arity(definition, 1, path + ".definition")
  if !(json_field(object, "builtinKind", path) is Null) {
    fail_snapshot(MalformedSnapshot, path, "alias cannot be a builtin type")
  }
  let name = semantic_name(json_field(object, "name", path), path + ".name")
  let name_view = name.view()
  self.types[descriptor.locator] = @logic.TypeSymbol::new_alias(
    self.context,
    name_view.name,
    origin_from_name(name, descriptor.key),
    self.decode_type_parameters(
      json_field(object, "typeParameters", path),
      path + ".typeParameters",
    ),
    self.decode_ty(definition[1], path + ".definition[1]"),
    name_view.source_span,
  )
}

///|
fn SnapshotDecoder::decode_types(self : SnapshotDecoder) -> Unit raise {
  for descriptor in self.descriptors {
    if descriptor.tag == "TypeSymbol" {
      self.decode_non_alias_type(descriptor)
    }
  }
  for descriptor in self.descriptors {
    if descriptor.tag == "TypeSymbol" {
      self.decode_alias_type(descriptor)
    }
  }
}

///|
fn SnapshotDecoder::logic_symbol(
  self : SnapshotDecoder,
  locator : String,
  path : String,
) -> @logic.LSymbol raise SnapshotError {
  match self.logic.get(locator) {
    Some(symbol) => symbol
    None =>
      fail_snapshot(UnknownReference, path, "unknown logic symbol locator")
  }
}

///|
fn SnapshotDecoder::proposition_symbol(
  self : SnapshotDecoder,
  locator : String,
  path : String,
) -> @logic.PrSymbol raise SnapshotError {
  match self.propositions.get(locator) {
    Some(symbol) => symbol
    None =>
      fail_snapshot(
        UnknownReference,
        path,
        "unknown proposition symbol locator",
      )
  }
}

///|
fn SnapshotDecoder::decode_logic_symbols(self : SnapshotDecoder) -> Unit raise {
  for descriptor in self.descriptors {
    if descriptor.tag != "LogicSymbol" {
      continue
    }
    let path = descriptor.path + ".symbol"
    let object = json_object(descriptor.symbol, path)
    let name = semantic_name(json_field(object, "name", path), path + ".name")
    let name_view = name.view()
    let arguments = [
      for
        index, argument in json_array(
          json_field(object, "argumentTypes", path),
          path + ".argumentTypes",
        ) => {
        self.decode_ty(
          argument,
          path + ".argumentTypes[" + index.to_string() + "]",
        )
      }
    ]
    let result = self.decode_optional_ty(
      json_field(object, "resultType", path),
      path + ".resultType",
    )
    let (role, role_fields) = tagged(
      json_field(object, "role", path),
      path + ".role",
    )
    let origin = origin_from_name(name, descriptor.key)
    let symbol = match role {
      "Ordinary" => {
        require_tag_arity(role_fields, 0, path + ".role")
        match result {
          Some(result) =>
            @logic.LSymbol::new_function(
              self.context,
              name_view.name,
              origin,
              arguments,
              result,
              name_view.source_span,
            )
          None =>
            @logic.LSymbol::new_predicate(
              self.context,
              name_view.name,
              origin,
              arguments,
              name_view.source_span,
            )
        }
      }
      "Constructor" => {
        require_tag_arity(role_fields, 1, path + ".role")
        guard result is Some(result) else {
          fail_snapshot(
            MalformedSnapshot,
            path,
            "constructor has no result type",
          )
        }
        @logic.LSymbol::trusted_constructor(
          self.context,
          name_view.name,
          origin,
          arguments,
          result,
          json_int(role_fields[1], path + ".role[1]"),
          name_view.source_span,
        )
      }
      "Projection" => {
        require_tag_arity(role_fields, 0, path + ".role")
        guard arguments is [source] && result is Some(result) else {
          fail_snapshot(
            MalformedSnapshot,
            path,
            "projection signature is invalid",
          )
        }
        @logic.LSymbol::trusted_projection(
          self.context,
          name_view.name,
          origin,
          source,
          result,
          name_view.source_span,
        )
      }
      _ =>
        fail_snapshot(
          UnsupportedSnapshotVariant,
          path,
          "unknown logic symbol role",
        )
    }
    let expected_parameters = self.decode_type_parameters(
      json_field(object, "typeParameters", path),
      path + ".typeParameters",
    )
    let actual_parameters = symbol.view().type_parameters
    if actual_parameters.length() != expected_parameters.length() {
      fail_snapshot(
        SemanticInvariantFailure,
        path,
        "logic symbol type-parameter inference differs from snapshot",
      )
    }
    for index, parameter in actual_parameters {
      if parameter != expected_parameters[index] {
        fail_snapshot(
          SemanticInvariantFailure,
          path,
          "logic symbol type-parameter order differs from snapshot",
        )
      }
    }
    self.logic[descriptor.locator] = symbol
  }
}

///|
fn SnapshotDecoder::decode_proposition_symbols(
  self : SnapshotDecoder,
) -> Unit raise {
  for descriptor in self.descriptors {
    if descriptor.tag != "PropositionSymbol" {
      continue
    }
    let path = descriptor.path + ".symbol"
    let object = json_object(descriptor.symbol, path)
    let name = semantic_name(json_field(object, "name", path), path + ".name")
    let view = name.view()
    self.propositions[descriptor.locator] = @logic.PrSymbol::new(
      self.context,
      view.name,
      origin_from_name(name, descriptor.key),
    )
  }
}

///|
fn SnapshotDecoder::program_type_symbol(
  self : SnapshotDecoder,
  locator : String,
  path : String,
) -> @mlw.ProgramTypeSymbol raise SnapshotError {
  match self.program_types.get(locator) {
    Some(symbol) => symbol
    None =>
      fail_snapshot(
        UnknownReference,
        path,
        "unknown program type symbol locator",
      )
  }
}

///|
fn SnapshotDecoder::decode_ity(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> @mlw.Ity raise {
  let (tag, fields) = tagged(value, path)
  if tag != "ItyApp" {
    fail_snapshot(UnsupportedSnapshotVariant, path, "unknown program type node")
  }
  require_tag_arity(fields, 4, path)
  let locator = json_string(fields[1], path + "[1]")
  let arguments = [
    for index, argument in json_array(fields[2], path + "[2]") => {
      self.decode_ity(argument, path + "[2][" + index.to_string() + "]")
    }
  ]
  json_expect_empty(fields[3], path + "[3]")
  if !json_bool(fields[4], path + "[4]") {
    fail_snapshot(
      UnsupportedSnapshotVariant,
      path,
      "snapshot contains an impure Ity",
    )
  }
  @mlw.Ity::app(
    self.program_type_symbol(locator, path + "[1]"),
    arguments,
    None,
  )
}

///|
fn program_type_argument_flag(
  value : Json,
  path : String,
) -> @mlw.ProgramTypeArgumentFlag raise SnapshotError {
  let object = json_object(value, path)
  {
    frozen: json_bool(json_field(object, "frozen", path), path + ".frozen"),
    exposed: json_bool(json_field(object, "exposed", path), path + ".exposed"),
    liable: json_bool(json_field(object, "liable", path), path + ".liable"),
    fixed: json_bool(json_field(object, "fixed", path), path + ".fixed"),
    visible: json_bool(json_field(object, "visible", path), path + ".visible"),
  }
}

///|
fn SnapshotDecoder::decode_non_alias_program_type(
  self : SnapshotDecoder,
  descriptor : CatalogDescriptor,
) -> Unit raise {
  let path = descriptor.path + ".symbol"
  let object = json_object(descriptor.symbol, path)
  let (definition_tag, definition) = tagged(
    json_field(object, "definition", path),
    path + ".definition",
  )
  if definition_tag == "Alias" {
    return
  }
  json_expect_empty(
    json_field(object, "mutableFields", path),
    path + ".mutableFields",
  )
  json_expect_empty(
    json_field(object, "immutableFields", path),
    path + ".immutableFields",
  )
  let logic_type = self.type_symbol(
    json_string(
      json_field(object, "logicTypeSymbol", path),
      path + ".logicTypeSymbol",
    ),
    path + ".logicTypeSymbol",
  )
  let logic_origin = logic_type.origin()
  let origin = @identity.Origin::snapshot_with_span(
    logic_type.name(),
    descriptor.key,
    logic_origin.source_span(),
    logic_origin.attributes(),
  )
  let definition = match definition_tag {
    "NoDef" => {
      require_tag_arity(definition, 0, path + ".definition")
      @mlw.ProgramNoDef
    }
    "Range" => {
      require_tag_arity(definition, 2, path + ".definition")
      ProgramRange(
        @bigint.BigInt::from_string(json_string(definition[1], path)),
        @bigint.BigInt::from_string(json_string(definition[2], path)),
      )
    }
    "Float" => {
      require_tag_arity(definition, 2, path + ".definition")
      ProgramFloat(json_int(definition[1], path), json_int(definition[2], path))
    }
    _ =>
      fail_snapshot(
        UnsupportedSnapshotVariant,
        path,
        "unknown program type definition",
      )
  }
  let argument_flags = [
    for
      index, flag in json_array(
        json_field(object, "argumentFlags", path),
        path + ".argumentFlags",
      ) => {
      program_type_argument_flag(
        flag,
        path + ".argumentFlags[" + index.to_string() + "]",
      )
    }
  ]
  let region_flags = [
    for
      index, flag in json_array(
        json_field(object, "regionFlags", path),
        path + ".regionFlags",
      ) => {
      program_type_argument_flag(
        flag,
        path + ".regionFlags[" + index.to_string() + "]",
      )
    }
  ]
  self.program_types[descriptor.locator] = @mlw.ProgramTypeSymbol::trusted_new(
    self.context,
    logic_type,
    origin,
    {
      nonfree: json_bool(json_field(object, "nonfree", path), path + ".nonfree"),
      private_: json_bool(
        json_field(object, "private", path),
        path + ".private",
      ),
      mutable_: json_bool(
        json_field(object, "mutable", path),
        path + ".mutable",
      ),
      fragile: json_bool(json_field(object, "fragile", path), path + ".fragile"),
      argument_flags,
      region_flags,
    },
    definition,
    [],
    [],
    logic_origin.source_span(),
  )
}

///|
fn SnapshotDecoder::decode_alias_program_type(
  self : SnapshotDecoder,
  descriptor : CatalogDescriptor,
) -> Unit raise {
  let path = descriptor.path + ".symbol"
  let object = json_object(descriptor.symbol, path)
  let (definition_tag, definition) = tagged(
    json_field(object, "definition", path),
    path + ".definition",
  )
  if definition_tag != "Alias" {
    return
  }
  require_tag_arity(definition, 1, path + ".definition")
  json_expect_empty(
    json_field(object, "mutableFields", path),
    path + ".mutableFields",
  )
  json_expect_empty(
    json_field(object, "immutableFields", path),
    path + ".immutableFields",
  )
  let logic_type = self.type_symbol(
    json_string(
      json_field(object, "logicTypeSymbol", path),
      path + ".logicTypeSymbol",
    ),
    path + ".logicTypeSymbol",
  )
  let logic_origin = logic_type.origin()
  let argument_flags = [
    for
      index, flag in json_array(
        json_field(object, "argumentFlags", path),
        path + ".argumentFlags",
      ) => {
      program_type_argument_flag(
        flag,
        path + ".argumentFlags[" + index.to_string() + "]",
      )
    }
  ]
  let region_flags = [
    for
      index, flag in json_array(
        json_field(object, "regionFlags", path),
        path + ".regionFlags",
      ) => {
      program_type_argument_flag(
        flag,
        path + ".regionFlags[" + index.to_string() + "]",
      )
    }
  ]
  self.program_types[descriptor.locator] = @mlw.ProgramTypeSymbol::trusted_new(
    self.context,
    logic_type,
    @identity.Origin::snapshot_with_span(
      logic_type.name(),
      descriptor.key,
      logic_origin.source_span(),
      logic_origin.attributes(),
    ),
    {
      nonfree: json_bool(json_field(object, "nonfree", path), path + ".nonfree"),
      private_: json_bool(
        json_field(object, "private", path),
        path + ".private",
      ),
      mutable_: json_bool(
        json_field(object, "mutable", path),
        path + ".mutable",
      ),
      fragile: json_bool(json_field(object, "fragile", path), path + ".fragile"),
      argument_flags,
      region_flags,
    },
    ProgramAlias(self.decode_ity(definition[1], path + ".definition[1]")),
    [],
    [],
    logic_origin.source_span(),
  )
}

///|
fn SnapshotDecoder::decode_program_types(self : SnapshotDecoder) -> Unit raise {
  for descriptor in self.descriptors {
    if descriptor.tag == "ProgramTypeSymbol" {
      self.decode_non_alias_program_type(descriptor)
    }
  }
  for descriptor in self.descriptors {
    if descriptor.tag == "ProgramTypeSymbol" {
      self.decode_alias_program_type(descriptor)
    }
  }
}

///|
fn local_variable_origin(name : @theory.SemanticName) -> @identity.Origin {
  let view = name.view()
  @identity.Origin::user(view.name, view.source_span, view.attributes)
}

///|
fn SnapshotDecoder::decode_vsymbol(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> (Int, @logic.VSymbol) raise {
  let object = json_object(value, path)
  let id = json_int(json_field(object, "id", path), path + ".id")
  let name = semantic_name(json_field(object, "name", path), path + ".name")
  let view = name.view()
  (
    id,
    @logic.VSymbol::new(
      self.context,
      view.name,
      local_variable_origin(name),
      self.decode_ty(json_field(object, "type", path), path + ".type"),
      view.source_span,
    ),
  )
}

///|
fn copy_variable_map(
  variables : Map[Int, @logic.VSymbol],
) -> Map[Int, @logic.VSymbol] {
  Map(variables.to_array())
}

///|
fn decode_constant(
  value : Json,
  path : String,
) -> @logic.Constant raise SnapshotError {
  let (tag, fields) = tagged(value, path)
  match tag {
    "ConstantInt" => {
      require_tag_arity(fields, 2, path)
      let kind = match json_string(fields[1], path + "[1]") {
        "ILitUnk" => @logic.IntegerUnknown
        "ILitDec" => IntegerDecimal
        "ILitHex" => IntegerHexadecimal
        _ =>
          fail_snapshot(
            UnsupportedSnapshotVariant,
            path,
            "unknown integer literal kind",
          )
      }
      @logic.Constant::integer(
        kind,
        @bigint.BigInt::from_string(json_string(fields[2], path + "[2]")),
      )
    }
    "ConstantReal" => {
      require_tag_arity(fields, 4, path)
      let (kind_tag, kind_fields) = tagged(fields[1], path + "[1]")
      require_tag_arity(kind_fields, 1, path + "[1]")
      let exponent = json_int(kind_fields[1], path + "[1][1]").to_int64()
      let kind = match kind_tag {
        "RLitDec" => @logic.RealDecimal(exponent)
        "RLitHex" => RealHexadecimal(exponent)
        _ =>
          fail_snapshot(
            UnsupportedSnapshotVariant,
            path,
            "unknown real literal kind",
          )
      }
      @logic.Constant::real(
        kind,
        @parser.RealValue::normalized(
          @bigint.BigInt::from_string(json_string(fields[2], path + "[2]")),
          @bigint.BigInt::from_string(json_string(fields[3], path + "[3]")),
          @bigint.BigInt::from_string(json_string(fields[4], path + "[4]")),
        ),
      )
    }
    "ConstantString" => {
      require_tag_arity(fields, 1, path)
      @logic.Constant::string(bytes_from_json_hex(fields[1], path + "[1]"))
    }
    _ =>
      fail_snapshot(UnsupportedSnapshotVariant, path, "unknown constant node")
  }
}

///|
fn SnapshotDecoder::decode_pattern(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> @logic.Pattern raise {
  let (tag, fields) = tagged(value, path)
  match tag {
    "Pwild" => {
      require_tag_arity(fields, 1, path)
      @logic.Pattern::trusted_wild(self.decode_ty(fields[1], path + "[1]"))
    }
    "Papp" => {
      require_tag_arity(fields, 3, path)
      let arguments = [
        for index, argument in json_array(fields[2], path + "[2]") => {
          self.decode_pattern(argument, path + "[2][" + index.to_string() + "]")
        }
      ]
      @logic.Pattern::trusted_app(
        self.logic_symbol(json_string(fields[1], path + "[1]"), path + "[1]"),
        arguments,
        self.decode_ty(fields[3], path + "[3]"),
        None,
      )
    }
    "Por" => {
      require_tag_arity(fields, 3, path)
      let left = self.decode_pattern(fields[1], path + "[1]")
      let right = self.decode_pattern(fields[2], path + "[2]")
      let expected_type = self.decode_ty(fields[3], path + "[3]")
      if left.ty() != expected_type || right.ty() != expected_type {
        fail_snapshot(
          SemanticInvariantFailure,
          path,
          "or-pattern type metadata disagrees",
        )
      }
      @logic.Pattern::trusted_or(left, right, None)
    }
    _ => fail_snapshot(UnsupportedSnapshotVariant, path, "unknown pattern node")
  }
}

///|
fn require_term_result(
  term : @logic.Term,
  expected : @logic.Ty?,
  path : String,
) -> @logic.Term raise SnapshotError {
  if term.ty() != expected {
    fail_snapshot(
      SemanticInvariantFailure,
      path,
      "term result-type metadata disagrees",
    )
  }
  term
}

///|
fn SnapshotDecoder::decode_term(
  self : SnapshotDecoder,
  value : Json,
  locals : Map[Int, @logic.VSymbol],
  program_variables : Map[Int, @logic.VSymbol],
  path : String,
) -> @logic.Term raise {
  let object = json_object(value, path)
  let span = source_span(
    json_field(object, "sourceSpan", path),
    path + ".sourceSpan",
  )
  let attributes = byte_attributes(
    json_field(object, "attributes", path),
    path + ".attributes",
  )
  let (tag, fields) = tagged(json_field(object, "node", path), path + ".node")
  let decode = fn(value, suffix) -> @logic.Term raise {
    self.decode_term(value, locals, program_variables, path + ".node" + suffix)
  }
  let term = match tag {
    "Tvar" => {
      require_tag_arity(fields, 1, path + ".node")
      let (reference_tag, reference) = tagged(fields[1], path + ".node[1]")
      require_tag_arity(reference, 1, path + ".node[1]")
      let id = json_int(reference[1], path + ".node[1][1]")
      let variable = match reference_tag {
        "LocalVariable" => locals.get(id)
        "ProgramVariable" => program_variables.get(id)
        _ =>
          fail_snapshot(
            UnsupportedSnapshotVariant,
            path,
            "unknown term variable reference",
          )
      }
      guard variable is Some(variable) else {
        fail_snapshot(UnknownReference, path, "unknown term variable id")
      }
      @logic.Term::variable(variable)
    }
    "Tconst" => {
      require_tag_arity(fields, 2, path + ".node")
      guard self.decode_optional_ty(fields[2], path + ".node[2]")
        is Some(result_type) else {
        fail_snapshot(MalformedSnapshot, path, "constant has no result type")
      }
      @logic.Term::constant(
        decode_constant(fields[1], path + ".node[1]"),
        result_type,
        span,
      )
    }
    "Tapp" => {
      require_tag_arity(fields, 3, path + ".node")
      let arguments = [
        for index, argument in json_array(fields[2], path + ".node[2]") => {
          decode(argument, "[2][" + index.to_string() + "]")
        }
      ]
      @logic.Term::trusted_snapshot_apply(
        self.logic_symbol(
          json_string(fields[1], path + ".node[1]"),
          path + ".node[1]",
        ),
        arguments,
        self.decode_optional_ty(fields[3], path + ".node[3]"),
        span,
      )
    }
    "Tif" => {
      require_tag_arity(fields, 4, path + ".node")
      require_term_result(
        @logic.Term::if_then_else(
          decode(fields[1], "[1]"),
          decode(fields[2], "[2]"),
          decode(fields[3], "[3]"),
          span,
        ),
        self.decode_optional_ty(fields[4], path + ".node[4]"),
        path,
      )
    }
    "Tlet" => {
      require_tag_arity(fields, 4, path + ".node")
      let value = decode(fields[1], "[1]")
      let (id, variable) = self.decode_vsymbol(fields[2], path + ".node[2]")
      let nested = copy_variable_map(locals)
      if nested.contains(id) {
        fail_snapshot(MalformedSnapshot, path, "duplicate local variable id")
      }
      nested[id] = variable
      let body = self.decode_term(
        fields[3],
        nested,
        program_variables,
        path + ".node[3]",
      )
      require_term_result(
        @logic.Term::let_in(variable, value, body, span),
        self.decode_optional_ty(fields[4], path + ".node[4]"),
        path,
      )
    }
    "Tcase" => {
      require_tag_arity(fields, 3, path + ".node")
      let branches : Array[(@logic.Pattern, @logic.Term)] = []
      for index, branch in json_array(fields[2], path + ".node[2]") {
        let branch_path = path + ".node[2][" + index.to_string() + "]"
        let pair = json_array(branch, branch_path)
        if pair.length() != 2 {
          fail_snapshot(MalformedSnapshot, branch_path, "invalid case branch")
        }
        let pattern = self.decode_pattern(pair[0], branch_path + "[0]")
        if !pattern.bound_variables().is_empty() {
          fail_snapshot(
            UnsupportedSnapshotVariant,
            branch_path,
            "trusted snapshot case pattern unexpectedly binds variables",
          )
        }
        branches.push(
          (
            pattern,
            self.decode_term(
              pair[1],
              locals,
              program_variables,
              branch_path + "[1]",
            ),
          ),
        )
      }
      require_term_result(
        @logic.Term::trusted_case(decode(fields[1], "[1]"), branches, span),
        self.decode_optional_ty(fields[3], path + ".node[3]"),
        path,
      )
    }
    "Teps" => {
      require_tag_arity(fields, 3, path + ".node")
      let (id, variable) = self.decode_vsymbol(fields[1], path + ".node[1]")
      let nested = copy_variable_map(locals)
      if nested.contains(id) {
        fail_snapshot(MalformedSnapshot, path, "duplicate epsilon variable id")
      }
      nested[id] = variable
      require_term_result(
        @logic.Term::trusted_epsilon(
          variable,
          self.decode_term(
            fields[2],
            nested,
            program_variables,
            path + ".node[2]",
          ),
          span,
        ),
        self.decode_optional_ty(fields[3], path + ".node[3]"),
        path,
      )
    }
    "Tquant.Forall" => {
      require_tag_arity(fields, 3, path + ".node")
      let nested = copy_variable_map(locals)
      let binders : Array[@logic.VSymbol] = []
      for index, binder in json_array(fields[1], path + ".node[1]") {
        let binder_path = path + ".node[1][" + index.to_string() + "]"
        let (id, variable) = self.decode_vsymbol(binder, binder_path)
        if nested.contains(id) {
          fail_snapshot(MalformedSnapshot, binder_path, "duplicate binder id")
        }
        nested[id] = variable
        binders.push(variable)
      }
      let triggers : Array[Array[@logic.Term]] = []
      for group_index, group in json_array(fields[2], path + ".node[2]") {
        let decoded_group : Array[@logic.Term] = []
        for
          term_index, trigger in json_array(
            group,
            path + ".node[2][" + group_index.to_string() + "]",
          ) {
          decoded_group.push(
            self.decode_term(
              trigger,
              nested,
              program_variables,
              path +
              ".node[2][" +
              group_index.to_string() +
              "][" +
              term_index.to_string() +
              "]",
            ),
          )
        }
        triggers.push(decoded_group)
      }
      @logic.Term::quantify(
        ForallQuantifier,
        binders,
        triggers,
        self.decode_term(
          fields[3],
          nested,
          program_variables,
          path + ".node[3]",
        ),
        span,
      )
    }
    "Tbinop.And" | "Tbinop.Or" | "Tbinop.Implies" | "Tbinop.Iff" => {
      require_tag_arity(fields, 2, path + ".node")
      let operator = match tag {
        "Tbinop.And" => @logic.And
        "Tbinop.Or" => Or
        "Tbinop.Implies" => Implies
        "Tbinop.Iff" => Iff
        _ => abort("binary tag was matched above")
      }
      @logic.Term::binary(
        operator,
        decode(fields[1], "[1]"),
        decode(fields[2], "[2]"),
        span,
      )
    }
    "Tnot" => {
      require_tag_arity(fields, 1, path + ".node")
      @logic.Term::not(decode(fields[1], "[1]"), span)
    }
    _ => fail_snapshot(UnsupportedSnapshotVariant, path, "unknown term node")
  }
  term.trusted_snapshot_decorate(span, attributes)
}

///|
fn SnapshotDecoder::decode_pvariable(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> (Int, @mlw.PVariable) raise {
  let object = json_object(value, path)
  let id = json_int(json_field(object, "id", path), path + ".id")
  let name = semantic_name(json_field(object, "name", path), path + ".name")
  let span = name.view().source_span
  (
    id,
    @mlw.PVariable::trusted_new(
      self.context,
      name,
      self.decode_ity(json_field(object, "ity", path), path + ".ity"),
      json_bool(json_field(object, "ghost", path), path + ".ghost"),
      span,
    ),
  )
}

///|
fn SnapshotDecoder::decode_cty(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> @mlw.Cty raise {
  let object = json_object(value, path)
  let variables_by_id : Map[Int, @mlw.PVariable] = Map([])
  let pure_by_id : Map[Int, @logic.VSymbol] = Map([])
  let variables : Array[@mlw.PVariable] = []
  for
    index, descriptor in json_array(
      json_field(object, "programVariables", path),
      path + ".programVariables",
    ) {
    let descriptor_path = path + ".programVariables[" + index.to_string() + "]"
    let (id, variable) = self.decode_pvariable(descriptor, descriptor_path)
    if variables_by_id.contains(id) {
      fail_snapshot(
        MalformedSnapshot,
        descriptor_path,
        "duplicate program variable id",
      )
    }
    variables_by_id[id] = variable
    pure_by_id[id] = variable.view().pure_symbol
    variables.push(variable)
  }
  let arguments : Array[@mlw.PVariable] = []
  for
    index, argument in json_array(
      json_field(object, "arguments", path),
      path + ".arguments",
    ) {
    let argument_path = path + ".arguments[" + index.to_string() + "]"
    let id = json_int(argument, argument_path)
    guard variables_by_id.get(id) is Some(variable) else {
      fail_snapshot(UnknownReference, argument_path, "unknown Cty argument id")
    }
    arguments.push(variable)
  }
  let empty_locals : Map[Int, @logic.VSymbol] = Map([])
  let preconditions = [
    for
      index, condition in json_array(
        json_field(object, "preconditions", path),
        path + ".preconditions",
      ) => {
      self.decode_term(
        condition,
        empty_locals,
        pure_by_id,
        path + ".preconditions[" + index.to_string() + "]",
      )
    }
  ]
  let postconditions : Array[@mlw.Postcondition] = []
  for
    index, post in json_array(
      json_field(object, "postconditions", path),
      path + ".postconditions",
    ) {
    let post_path = path + ".postconditions[" + index.to_string() + "]"
    let post_object = json_object(post, post_path)
    let (id, result) = self.decode_vsymbol(
      json_field(post_object, "result", post_path),
      post_path + ".result",
    )
    let post_locals : Map[Int, @logic.VSymbol] = Map([])
    post_locals[id] = result
    postconditions.push(
      @mlw.Postcondition::trusted_new(
        result,
        self.decode_term(
          json_field(post_object, "formula", post_path),
          post_locals,
          pure_by_id,
          post_path + ".formula",
        ),
        None,
      ),
    )
  }
  json_expect_empty(
    json_field(object, "exceptionalPostconditions", path),
    path + ".exceptionalPostconditions",
  )
  json_expect_empty(json_field(object, "oldies", path), path + ".oldies")
  let effect_object = json_object(
    json_field(object, "effect", path),
    path + ".effect",
  )
  for
    field in [
      "reads", "writes", "taints", "covers", "resets", "raises", "spoils",
    ] {
    json_expect_empty(
      json_field(effect_object, field, path + ".effect"),
      path + ".effect." + field,
    )
  }
  if json_string(
      json_field(effect_object, "termination", path + ".effect"),
      path + ".effect.termination",
    ) !=
    "Total" {
    fail_snapshot(
      UnsupportedSnapshotVariant,
      path,
      "non-total Cty effect in snapshot",
    )
  }
  let result = self.decode_ity(
    json_field(object, "result", path),
    path + ".result",
  )
  let mask = match
    json_string(json_field(object, "mask", path), path + ".mask") {
    "Visible" => @mlw.Visible
    "Ghost" => Ghost
    _ => fail_snapshot(UnsupportedSnapshotVariant, path, "unknown Cty mask")
  }
  let freeze = json_object(json_field(object, "freeze", path), path + ".freeze")
  json_expect_empty(
    json_field(freeze, "typeVariables", path + ".freeze"),
    path + ".freeze.typeVariables",
  )
  json_expect_empty(
    json_field(freeze, "regions", path + ".freeze"),
    path + ".freeze.regions",
  )
  @mlw.Cty::trusted_new(
    result.context_anchor(),
    variables,
    arguments,
    preconditions,
    postconditions,
    @mlw.Effect::pure(
      json_bool(
        json_field(effect_object, "ghost", path + ".effect"),
        path + ".effect.ghost",
      ),
    ),
    result,
    mask,
    None,
  )
}

///|
fn SnapshotDecoder::routine_symbol(
  self : SnapshotDecoder,
  locator : String,
  path : String,
) -> @mlw.RoutineSymbol raise SnapshotError {
  match self.routines.get(locator) {
    Some(symbol) => symbol
    None =>
      fail_snapshot(UnknownReference, path, "unknown routine symbol locator")
  }
}

///|
fn SnapshotDecoder::decode_routines(self : SnapshotDecoder) -> Unit raise {
  for descriptor in self.descriptors {
    if descriptor.tag != "RoutineSymbol" {
      continue
    }
    let path = descriptor.path + ".symbol"
    let object = json_object(descriptor.symbol, path)
    let name = semantic_name(json_field(object, "name", path), path + ".name")
    let view = name.view()
    let cty = self.decode_cty(json_field(object, "cty", path), path + ".cty")
    let (logic_tag, logic_fields) = tagged(
      json_field(object, "logic", path),
      path + ".logic",
    )
    let logic = match logic_tag {
      "RLnone" => {
        require_tag_arity(logic_fields, 0, path + ".logic")
        @mlw.RLnone
      }
      "RLls" => {
        require_tag_arity(logic_fields, 1, path + ".logic")
        RLls(
          self.logic_symbol(
            json_string(logic_fields[1], path + ".logic[1]"),
            path + ".logic[1]",
          ),
        )
      }
      _ =>
        fail_snapshot(
          UnsupportedSnapshotVariant,
          path,
          "unknown routine logic link",
        )
    }
    if !(json_field(object, "field", path) is Null) {
      fail_snapshot(
        UnsupportedSnapshotVariant,
        path,
        "routine field is outside frozen shell",
      )
    }
    self.routines[descriptor.locator] = @mlw.RoutineSymbol::trusted_new(
      self.context,
      view.name,
      origin_from_name(name, descriptor.key),
      cty,
      logic,
      None,
      view.source_span,
    )
  }
}
