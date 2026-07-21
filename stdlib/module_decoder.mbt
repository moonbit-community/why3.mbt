// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn SnapshotDecoder::decode_program_namespace(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> @mlw.ProgramNamespace raise {
  let object = json_object(value, path)
  let mut result = @mlw.ProgramNamespace::empty()
  for
    index, entry in json_array(
      json_field(object, "types", path),
      path + ".types",
    ) {
    let entry_path = path + ".types[" + index.to_string() + "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(MalformedSnapshot, entry_path, "invalid program type entry")
    }
    result = result.add_type(
      bytes_from_json_hex(pair[0], entry_path + "[0]"),
      self.program_type_symbol(
        json_string(pair[1], entry_path + "[1]"),
        entry_path + "[1]",
      ),
      None,
    )
  }
  for
    index, entry in json_array(
      json_field(object, "program", path),
      path + ".program",
    ) {
    let entry_path = path + ".program[" + index.to_string() + "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(MalformedSnapshot, entry_path, "invalid routine entry")
    }
    result = result.add_routine(
      bytes_from_json_hex(pair[0], entry_path + "[0]"),
      self.routine_symbol(
        json_string(pair[1], entry_path + "[1]"),
        entry_path + "[1]",
      ),
      None,
    )
  }
  json_expect_empty(
    json_field(object, "exceptions", path),
    path + ".exceptions",
  )
  for
    index, entry in json_array(
      json_field(object, "subspaces", path),
      path + ".subspaces",
    ) {
    let entry_path = path + ".subspaces[" + index.to_string() + "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(MalformedSnapshot, entry_path, "invalid program subspace")
    }
    result = result.add_subspace(
      bytes_from_json_hex(pair[0], entry_path + "[0]"),
      self.decode_program_namespace(pair[1], entry_path + "[1]"),
      None,
    )
  }
  result
}

///|
fn SnapshotDecoder::decode_pure_declarations(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> Array[@logic.Decl] raise {
  [
    for index, declaration in json_array(value, path) => {
      self.decode_declaration(declaration, path + "[" + index.to_string() + "]")
    }
  ]
}

///|
fn SnapshotDecoder::decode_program_computation(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> @mlw.ProgramComputation raise {
  let object = json_object(value, path)
  let (tag, fields) = tagged(json_field(object, "node", path), path + ".node")
  require_tag_arity(fields, 0, path + ".node")
  let cty = self.decode_cty(json_field(object, "cty", path), path + ".cty")
  match tag {
    "Cany" => Cany(cty)
    "Cfun" => Cfun(cty, None)
    _ =>
      fail_snapshot(
        UnsupportedSnapshotVariant,
        path,
        "unknown program computation",
      )
  }
}

///|
fn SnapshotDecoder::decode_program_declaration(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> @mlw.ProgramDeclaration raise {
  let object = json_object(value, path)
  let pure = self.decode_pure_declarations(
    json_field(object, "pureDeclarations", path),
    path + ".pureDeclarations",
  )
  let (tag, fields) = tagged(json_field(object, "node", path), path + ".node")
  match tag {
    "PDtype" => {
      require_tag_arity(fields, 1, path + ".node")
      let declarations : Array[@mlw.ProgramTypeDeclaration] = []
      for index, declaration in json_array(fields[1], path + ".node[1]") {
        let declaration_path = path + ".node[1][" + index.to_string() + "]"
        let declaration_object = json_object(declaration, declaration_path)
        if !(json_field(declaration_object, "witness", declaration_path) is Null) {
          fail_snapshot(
            UnsupportedSnapshotVariant,
            declaration_path,
            "program type witness is outside the frozen shell",
          )
        }
        let fields_symbols = [
          for
            field_index, field in json_array(
              json_field(declaration_object, "fields", declaration_path),
              declaration_path + ".fields",
            ) => {
            self.routine_symbol(
              json_string(
                field,
                declaration_path + ".fields[" + field_index.to_string() + "]",
              ),
              declaration_path + ".fields[" + field_index.to_string() + "]",
            )
          }
        ]
        let constructors = [
          for
            constructor_index, constructor_value in json_array(
              json_field(declaration_object, "constructors", declaration_path),
              declaration_path + ".constructors",
            ) => {
            self.routine_symbol(
              json_string(
                constructor_value,
                declaration_path +
                ".constructors[" +
                constructor_index.to_string() +
                "]",
              ),
              declaration_path +
              ".constructors[" +
              constructor_index.to_string() +
              "]",
            )
          }
        ]
        let no_variables : Map[Int, @logic.VSymbol] = Map([])
        let invariants = [
          for
            invariant_index, invariant in json_array(
              json_field(declaration_object, "invariants", declaration_path),
              declaration_path + ".invariants",
            ) => {
            self.decode_term(
              invariant,
              no_variables,
              no_variables,
              declaration_path +
              ".invariants[" +
              invariant_index.to_string() +
              "]",
            )
          }
        ]
        declarations.push(
          @mlw.ProgramTypeDeclaration::trusted_new(
            self.program_type_symbol(
              json_string(
                json_field(declaration_object, "symbol", declaration_path),
                declaration_path + ".symbol",
              ),
              declaration_path + ".symbol",
            ),
            fields_symbols,
            constructors,
            invariants,
            None,
          ),
        )
      }
      PDtype(declarations, pure)
    }
    "PDpure" => {
      require_tag_arity(fields, 0, path + ".node")
      PDpure(pure)
    }
    "PDlet.LDsym" => {
      require_tag_arity(fields, 2, path + ".node")
      PDlet(
        self.routine_symbol(
          json_string(fields[1], path + ".node[1]"),
          path + ".node[1]",
        ),
        self.decode_program_computation(fields[2], path + ".node[2]"),
        pure,
      )
    }
    _ =>
      fail_snapshot(
        UnsupportedSnapshotVariant,
        path,
        "unknown program declaration",
      )
  }
}

///|
fn SnapshotDecoder::decode_program_clone(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> @mlw.ProgramCloneWitness raise {
  let object = json_object(value, path)
  let type_instantiations : Array[(@logic.TypeSymbol, @mlw.Ity)] = []
  for
    index, entry in json_array(
      json_field(object, "typeInstantiations", path),
      path + ".typeInstantiations",
    ) {
    let entry_path = path + ".typeInstantiations[" + index.to_string() + "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(
        MalformedSnapshot,
        entry_path,
        "invalid module type instantiation",
      )
    }
    type_instantiations.push(
      (
        self.type_symbol(json_string(pair[0], entry_path), entry_path),
        self.decode_ity(pair[1], entry_path + "[1]"),
      ),
    )
  }
  let program_type_instantiations : Array[
    (@logic.TypeSymbol, @mlw.ProgramTypeSymbol),
  ] = []
  for
    index, entry in json_array(
      json_field(object, "programTypeInstantiations", path),
      path + ".programTypeInstantiations",
    ) {
    let entry_path = path +
      ".programTypeInstantiations[" +
      index.to_string() +
      "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(
        MalformedSnapshot,
        entry_path,
        "invalid program type instantiation",
      )
    }
    program_type_instantiations.push(
      (
        self.type_symbol(json_string(pair[0], entry_path), entry_path),
        self.program_type_symbol(json_string(pair[1], entry_path), entry_path),
      ),
    )
  }
  let logic_instantiations : Array[(@logic.LSymbol, @logic.LSymbol)] = []
  for
    index, entry in json_array(
      json_field(object, "logicInstantiations", path),
      path + ".logicInstantiations",
    ) {
    let entry_path = path + ".logicInstantiations[" + index.to_string() + "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(
        MalformedSnapshot,
        entry_path,
        "invalid module logic instantiation",
      )
    }
    logic_instantiations.push(
      (
        self.logic_symbol(json_string(pair[0], entry_path), entry_path),
        self.logic_symbol(json_string(pair[1], entry_path), entry_path),
      ),
    )
  }
  let proposition_instantiations : Array[(@logic.PrSymbol, @logic.PrSymbol)] = []
  for
    index, entry in json_array(
      json_field(object, "propositionInstantiations", path),
      path + ".propositionInstantiations",
    ) {
    let entry_path = path +
      ".propositionInstantiations[" +
      index.to_string() +
      "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(
        MalformedSnapshot,
        entry_path,
        "invalid module proposition instantiation",
      )
    }
    proposition_instantiations.push(
      (
        self.proposition_symbol(json_string(pair[0], entry_path), entry_path),
        self.proposition_symbol(json_string(pair[1], entry_path), entry_path),
      ),
    )
  }
  let proposition_kinds : Array[(@logic.PrSymbol, @logic.PropositionKind)] = []
  for
    index, entry in json_array(
      json_field(object, "propositionKinds", path),
      path + ".propositionKinds",
    ) {
    let entry_path = path + ".propositionKinds[" + index.to_string() + "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(
        MalformedSnapshot,
        entry_path,
        "invalid proposition-kind map",
      )
    }
    proposition_kinds.push(
      (
        self.proposition_symbol(json_string(pair[0], entry_path), entry_path),
        proposition_kind(pair[1], entry_path + "[1]"),
      ),
    )
  }
  json_expect_empty(
    json_field(object, "programVariableInstantiations", path),
    path + ".programVariableInstantiations",
  )
  let routine_instantiations : Array[(@mlw.RoutineSymbol, @mlw.RoutineSymbol)] = []
  for
    index, entry in json_array(
      json_field(object, "routineInstantiations", path),
      path + ".routineInstantiations",
    ) {
    let entry_path = path + ".routineInstantiations[" + index.to_string() + "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(
        MalformedSnapshot,
        entry_path,
        "invalid routine instantiation",
      )
    }
    routine_instantiations.push(
      (
        self.routine_symbol(json_string(pair[0], entry_path), entry_path),
        self.routine_symbol(json_string(pair[1], entry_path), entry_path),
      ),
    )
  }
  json_expect_empty(
    json_field(object, "exceptionInstantiations", path),
    path + ".exceptionInstantiations",
  )
  @mlw.ProgramCloneWitness::trusted_new(
    self.context.fresh_id(),
    self.theory_key(
      json_string(
        json_field(object, "sourceModule", path),
        path + ".sourceModule",
      ),
      path + ".sourceModule",
    ),
    type_instantiations,
    program_type_instantiations,
    logic_instantiations,
    proposition_instantiations,
    proposition_kinds,
    [],
    routine_instantiations,
    proposition_kind(
      json_field(object, "defaultPropositionKind", path),
      path + ".defaultPropositionKind",
    ),
    None,
  )
}

///|
fn SnapshotDecoder::decode_module_items(
  self : SnapshotDecoder,
  value : Json,
  path : String,
  ordinal : Ref[Int],
  prefix : ArrayView[Int],
) -> Array[@mlw.ModuleItem] raise {
  let result : Array[@mlw.ModuleItem] = []
  for index, item in json_array(value, path) {
    let item_path = path + "[" + index.to_string() + "]"
    let object = json_object(item, item_path)
    let item_ordinal = json_int(
      json_field(object, "ordinal", item_path),
      item_path + ".ordinal",
    )
    if item_ordinal != ordinal.val {
      fail_snapshot(MalformedSnapshot, item_path, "module item order drift")
    }
    ordinal.val = ordinal.val + 1
    let expected_path = prefix.to_owned()
    expected_path.push(index)
    let encoded_path = [
      for
        path_index, component in json_array(
          json_field(object, "ordinalPath", item_path),
          item_path + ".ordinalPath",
        ) => {
        json_int(
          component,
          item_path + ".ordinalPath[" + path_index.to_string() + "]",
        )
      }
    ]
    if encoded_path != expected_path {
      fail_snapshot(MalformedSnapshot, item_path, "module ordinal path drift")
    }
    let (tag, fields) = tagged(
      json_field(object, "node", item_path),
      item_path + ".node",
    )
    if tag == "Uscope" {
      require_tag_arity(fields, 2, item_path + ".node")
      ignore(bytes_from_json_hex(fields[1], item_path + ".node[1]"))
      for
        nested in self.decode_module_items(
          fields[2],
          item_path + ".node[2]",
          ordinal,
          expected_path,
        ) {
        result.push(nested)
      }
      continue
    }
    result.push(
      match tag {
        "Udecl" => {
          require_tag_arity(fields, 1, item_path + ".node")
          Udecl(
            self.decode_program_declaration(fields[1], item_path + ".node[1]"),
          )
        }
        "Uuse" => {
          require_tag_arity(fields, 1, item_path + ".node")
          Uuse(
            self.theory_key(
              json_string(fields[1], item_path + ".node[1]"),
              item_path + ".node[1]",
            ),
          )
        }
        "Uclone" => {
          require_tag_arity(fields, 1, item_path + ".node")
          Uclone(self.decode_program_clone(fields[1], item_path + ".node[1]"))
        }
        "Umeta" => {
          require_tag_arity(fields, 1, item_path + ".node")
          Umeta(self.decode_meta(fields[1], item_path + ".node[1]"))
        }
        _ =>
          fail_snapshot(
            UnsupportedSnapshotVariant,
            item_path,
            "unknown module item",
          )
      },
    )
  }
  result
}

///|
fn SnapshotDecoder::decode_modules(
  self : SnapshotDecoder,
  value : Json,
  theories : Map[String, @theory.Theory],
) -> Map[String, @mlw.Pmodule] raise {
  let modules : Map[String, @mlw.Pmodule] = Map([])
  for index, encoded in json_array(value, "$.modules") {
    let path = "$.modules[" + index.to_string() + "]"
    let object = json_object(encoded, path)
    let key_text = json_string(json_field(object, "key", path), path + ".key")
    if modules.contains(key_text) {
      fail_snapshot(MalformedSnapshot, path, "duplicate program module key")
    }
    let pure_key = json_string(
      json_field(object, "pureTheory", path),
      path + ".pureTheory",
    )
    guard theories.get(pure_key) is Some(pure_theory) else {
      fail_snapshot(
        UnknownReference,
        path + ".pureTheory",
        "program module references an unknown pure theory",
      )
    }
    modules[key_text] = @mlw.Pmodule::trusted_new(
      self.theory_key(key_text, path + ".key"),
      pure_theory,
      self.decode_module_items(
        json_field(object, "items", path),
        path + ".items",
        Ref(0),
        [],
      ),
      self.decode_program_namespace(
        json_field(object, "exportNamespace", path),
        path + ".exportNamespace",
      ),
    )
  }
  modules
}

///|
fn SnapshotDecoder::build_catalog(
  self : SnapshotDecoder,
) -> DriverSymbolCatalog raise SnapshotError {
  let catalog = DriverSymbolCatalog::new(self.context.fresh_id())
  for descriptor in self.descriptors {
    let symbol = match descriptor.tag {
      "TypeSymbol" =>
        DriverType(self.type_symbol(descriptor.locator, descriptor.path))
      "LogicSymbol" =>
        DriverLogic(self.logic_symbol(descriptor.locator, descriptor.path))
      "PropositionSymbol" =>
        DriverProposition(
          self.proposition_symbol(descriptor.locator, descriptor.path),
        )
      "ProgramTypeSymbol" =>
        DriverProgramType(
          self.program_type_symbol(descriptor.locator, descriptor.path),
        )
      "RoutineSymbol" =>
        DriverRoutine(self.routine_symbol(descriptor.locator, descriptor.path))
      _ => abort("catalog descriptor tag was validated")
    }
    catalog.insert(descriptor.key, descriptor.locator, symbol, descriptor.path)
  }
  catalog
}
