// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn SnapshotDecoder::theory_key(
  self : SnapshotDecoder,
  text : String,
  path : String,
) -> @theory.TheoryKey raise SnapshotError {
  match self.theory_keys.get(text) {
    Some(key) => key
    None => fail_snapshot(UnknownReference, path, "unknown theory/module key")
  }
}

///|
fn SnapshotDecoder::decode_theory_keys(
  self : SnapshotDecoder,
  theories : Json,
) -> Unit raise {
  for index, theory in json_array(theories, "$.theories") {
    let path = "$.theories[" + index.to_string() + "]"
    let object = json_object(theory, path)
    let text = json_string(json_field(object, "key", path), path + ".key")
    if self.theory_keys.contains(text) {
      fail_snapshot(MalformedSnapshot, path, "duplicate theory key")
    }
    let path_segments = [
      for
        segment_index, segment in json_array(
          json_field(object, "pathHex", path),
          path + ".pathHex",
        ) => {
        bytes_from_json_hex(
          segment,
          path + ".pathHex[" + segment_index.to_string() + "]",
        )
      }
    ]
    let name = semantic_name(json_field(object, "name", path), path + ".name")
    self.theory_keys[text] = @theory.TheoryKey::new(
      path_segments,
      name.view().name,
    )
  }
}

///|
fn proposition_kind(
  value : Json,
  path : String,
) -> @logic.PropositionKind raise SnapshotError {
  match json_string(value, path) {
    "Paxiom" => Paxiom
    "Plemma" => Plemma
    "Pgoal" => Pgoal
    _ =>
      fail_snapshot(
        UnsupportedSnapshotVariant,
        path,
        "unknown proposition kind",
      )
  }
}

///|
fn SnapshotDecoder::decode_declaration(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> @logic.Decl raise {
  let (tag, fields) = tagged(value, path)
  match tag {
    "Dtype" => {
      require_tag_arity(fields, 1, path)
      let symbol = self.type_symbol(
        json_string(fields[1], path + "[1]"),
        path + "[1]",
      )
      @logic.Decl::trusted_type_declaration(
        self.context,
        symbol.origin(),
        [symbol],
        symbol.origin().source_span(),
      )
    }
    "Ddata" => {
      require_tag_arity(fields, 1, path)
      let declarations : Array[@logic.DataDeclaration] = []
      for declaration_index, declaration in json_array(fields[1], path + "[1]") {
        let declaration_path = path +
          "[1][" +
          declaration_index.to_string() +
          "]"
        let declaration_fields = json_array(declaration, declaration_path)
        if declaration_fields.length() != 2 {
          fail_snapshot(
            MalformedSnapshot,
            declaration_path,
            "invalid data declaration",
          )
        }
        let type_symbol = self.type_symbol(
          json_string(declaration_fields[0], declaration_path + "[0]"),
          declaration_path + "[0]",
        )
        let constructors : Array[@logic.DataConstructor] = []
        for
          constructor_index, constructor_value in json_array(
            declaration_fields[1],
            declaration_path + "[1]",
          ) {
          let constructor_path = declaration_path +
            "[1][" +
            constructor_index.to_string() +
            "]"
          let constructor_fields = json_array(
            constructor_value, constructor_path,
          )
          if constructor_fields.length() != 2 {
            fail_snapshot(
              MalformedSnapshot,
              constructor_path,
              "invalid data constructor",
            )
          }
          let constructor_symbol = self.logic_symbol(
            json_string(constructor_fields[0], constructor_path + "[0]"),
            constructor_path + "[0]",
          )
          let projections : Array[@logic.LSymbol?] = []
          for
            projection_index, projection in json_array(
              constructor_fields[1],
              constructor_path + "[1]",
            ) {
            let projection_path = constructor_path +
              "[1][" +
              projection_index.to_string() +
              "]"
            projections.push(
              match projection {
                Null => None
                _ =>
                  Some(
                    self.logic_symbol(
                      json_string(projection, projection_path),
                      projection_path,
                    ),
                  )
              },
            )
          }
          constructors.push(
            @logic.DataConstructor::trusted_new(
              constructor_symbol,
              projections,
              constructor_symbol.view().origin.source_span(),
            ),
          )
        }
        declarations.push(
          @logic.DataDeclaration::trusted_new(
            type_symbol,
            constructors,
            type_symbol.origin().source_span(),
          ),
        )
      }
      if declarations.is_empty() {
        fail_snapshot(MalformedSnapshot, path, "empty data declaration")
      }
      let origin = declarations[0].view().type_symbol.origin()
      @logic.Decl::trusted_data(
        self.context,
        origin,
        declarations,
        origin.source_span(),
      )
    }
    "Dparam" => {
      require_tag_arity(fields, 1, path)
      let symbol = self.logic_symbol(
        json_string(fields[1], path + "[1]"),
        path + "[1]",
      )
      let origin = symbol.view().origin
      @logic.Decl::parameter(self.context, origin, symbol, origin.source_span())
    }
    "Dlogic" => {
      require_tag_arity(fields, 1, path)
      let definitions : Array[@logic.LogicDefinition] = []
      for definition_index, definition in json_array(fields[1], path + "[1]") {
        let definition_path = path + "[1][" + definition_index.to_string() + "]"
        let definition_fields = json_array(definition, definition_path)
        if definition_fields.length() != 3 {
          fail_snapshot(
            MalformedSnapshot,
            definition_path,
            "invalid logic definition",
          )
        }
        let symbol = self.logic_symbol(
          json_string(definition_fields[0], definition_path + "[0]"),
          definition_path + "[0]",
        )
        let locals : Map[Int, @logic.VSymbol] = Map([])
        let parameters : Array[@logic.VSymbol] = []
        for
          parameter_index, parameter in json_array(
            definition_fields[1],
            definition_path + "[1]",
          ) {
          let parameter_path = definition_path +
            "[1][" +
            parameter_index.to_string() +
            "]"
          let (id, variable) = self.decode_vsymbol(parameter, parameter_path)
          if locals.contains(id) {
            fail_snapshot(
              MalformedSnapshot,
              parameter_path,
              "duplicate parameter id",
            )
          }
          locals[id] = variable
          parameters.push(variable)
        }
        let no_program_variables : Map[Int, @logic.VSymbol] = Map([])
        definitions.push(
          @logic.LogicDefinition::trusted_recursive(
            self.context,
            symbol,
            parameters,
            self.decode_term(
              definition_fields[2],
              locals,
              no_program_variables,
              definition_path + "[2]",
            ),
            symbol.view().origin.source_span(),
          ),
        )
      }
      if definitions.is_empty() {
        fail_snapshot(MalformedSnapshot, path, "empty logic declaration")
      }
      let origin = definitions[0].view().symbol.view().origin
      @logic.Decl::trusted_logic(
        self.context,
        origin,
        definitions,
        origin.source_span(),
      )
    }
    "Dind.Ind" => {
      require_tag_arity(fields, 1, path)
      let declarations : Array[@logic.InductiveDeclaration] = []
      for declaration_index, declaration in json_array(fields[1], path + "[1]") {
        let declaration_path = path +
          "[1][" +
          declaration_index.to_string() +
          "]"
        let declaration_fields = json_array(declaration, declaration_path)
        if declaration_fields.length() != 2 {
          fail_snapshot(
            MalformedSnapshot,
            declaration_path,
            "invalid inductive declaration",
          )
        }
        let predicate = self.logic_symbol(
          json_string(declaration_fields[0], declaration_path + "[0]"),
          declaration_path + "[0]",
        )
        let cases : Array[@logic.InductiveCase] = []
        for
          case_index, case_ in json_array(
            declaration_fields[1],
            declaration_path + "[1]",
          ) {
          let case_path = declaration_path +
            "[1][" +
            case_index.to_string() +
            "]"
          let case_fields = json_array(case_, case_path)
          if case_fields.length() != 2 {
            fail_snapshot(
              MalformedSnapshot,
              case_path,
              "invalid inductive case",
            )
          }
          let proposition = self.proposition_symbol(
            json_string(case_fields[0], case_path + "[0]"),
            case_path + "[0]",
          )
          let no_variables : Map[Int, @logic.VSymbol] = Map([])
          cases.push(
            @logic.InductiveCase::trusted_new(
              self.context,
              proposition,
              self.decode_term(
                case_fields[1],
                no_variables,
                no_variables,
                case_path + "[1]",
              ),
              proposition.view().origin.source_span(),
            ),
          )
        }
        declarations.push(
          @logic.InductiveDeclaration::trusted_new(
            predicate,
            cases,
            predicate.view().origin.source_span(),
          ),
        )
      }
      if declarations.is_empty() {
        fail_snapshot(MalformedSnapshot, path, "empty inductive declaration")
      }
      let origin = declarations[0].view().predicate.view().origin
      @logic.Decl::trusted_inductive(
        self.context,
        origin,
        declarations,
        origin.source_span(),
      )
    }
    "Dprop" => {
      require_tag_arity(fields, 3, path)
      let proposition = self.proposition_symbol(
        json_string(fields[2], path + "[2]"),
        path + "[2]",
      )
      let no_variables : Map[Int, @logic.VSymbol] = Map([])
      let origin = proposition.view().origin
      @logic.Decl::proposition(
        self.context,
        origin,
        proposition_kind(fields[1], path + "[1]"),
        proposition,
        self.decode_term(fields[3], no_variables, no_variables, path + "[3]"),
        origin.source_span(),
      )
    }
    _ =>
      fail_snapshot(
        UnsupportedSnapshotVariant,
        path,
        "unknown declaration node",
      )
  }
}

///|
fn SnapshotDecoder::decode_meta_argument(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> @theory.MetaArgument raise {
  let (tag, fields) = tagged(value, path)
  require_tag_arity(fields, 1, path)
  match tag {
    "Type" => MetaType(self.decode_ty(fields[1], path + "[1]"))
    "TypeSymbol" =>
      MetaTypeSymbol(
        self.type_symbol(json_string(fields[1], path + "[1]"), path + "[1]"),
      )
    "LogicSymbol" =>
      MetaLogicSymbol(
        self.logic_symbol(json_string(fields[1], path + "[1]"), path + "[1]"),
      )
    "PropositionSymbol" =>
      MetaPropositionSymbol(
        self.proposition_symbol(
          json_string(fields[1], path + "[1]"),
          path + "[1]",
        ),
      )
    "String" => MetaString(bytes_from_json_hex(fields[1], path + "[1]"))
    "Integer" => MetaInteger(json_int(fields[1], path + "[1]").to_int64())
    "Identifier" => MetaIdentifier(semantic_name(fields[1], path + "[1]"))
    _ =>
      fail_snapshot(UnsupportedSnapshotVariant, path, "unknown meta argument")
  }
}

///|
fn SnapshotDecoder::decode_meta(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> @theory.Meta raise {
  let object = json_object(value, path)
  @theory.Meta::new(
    bytes_from_json_hex(json_field(object, "nameHex", path), path + ".nameHex"),
    [
      for
        index, argument in json_array(
          json_field(object, "arguments", path),
          path + ".arguments",
        ) => {
        self.decode_meta_argument(
          argument,
          path + ".arguments[" + index.to_string() + "]",
        )
      }
    ],
  )
}

///|
fn SnapshotDecoder::decode_namespace(
  self : SnapshotDecoder,
  value : Json,
  path : String,
) -> @theory.Namespace raise {
  let object = json_object(value, path)
  let mut result = @theory.Namespace::empty()
  for
    index, entry in json_array(
      json_field(object, "types", path),
      path + ".types",
    ) {
    let entry_path = path + ".types[" + index.to_string() + "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(
        MalformedSnapshot,
        entry_path,
        "invalid namespace type entry",
      )
    }
    result = result.add_type(
      bytes_from_json_hex(pair[0], entry_path + "[0]"),
      self.type_symbol(
        json_string(pair[1], entry_path + "[1]"),
        entry_path + "[1]",
      ),
      None,
    )
  }
  for
    index, entry in json_array(
      json_field(object, "logic", path),
      path + ".logic",
    ) {
    let entry_path = path + ".logic[" + index.to_string() + "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(
        MalformedSnapshot,
        entry_path,
        "invalid namespace logic entry",
      )
    }
    result = result.add_logic(
      bytes_from_json_hex(pair[0], entry_path + "[0]"),
      self.logic_symbol(
        json_string(pair[1], entry_path + "[1]"),
        entry_path + "[1]",
      ),
      None,
    )
  }
  for
    index, entry in json_array(
      json_field(object, "propositions", path),
      path + ".propositions",
    ) {
    let entry_path = path + ".propositions[" + index.to_string() + "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(
        MalformedSnapshot,
        entry_path,
        "invalid namespace proposition entry",
      )
    }
    result = result.add_proposition(
      bytes_from_json_hex(pair[0], entry_path + "[0]"),
      self.proposition_symbol(
        json_string(pair[1], entry_path + "[1]"),
        entry_path + "[1]",
      ),
      None,
    )
  }
  for
    index, entry in json_array(
      json_field(object, "subspaces", path),
      path + ".subspaces",
    ) {
    let entry_path = path + ".subspaces[" + index.to_string() + "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(MalformedSnapshot, entry_path, "invalid namespace subspace")
    }
    result = result.add_subspace(
      bytes_from_json_hex(pair[0], entry_path + "[0]"),
      self.decode_namespace(pair[1], entry_path + "[1]"),
      None,
    )
  }
  result
}

///|
fn SnapshotDecoder::decode_clone_witness(
  self : SnapshotDecoder,
  source_value : Json,
  ordinal_value : Json,
  map_value : Json,
  path : String,
) -> @theory.CloneWitness raise {
  let object = json_object(map_value, path + ".map")
  let type_instantiations : Array[@theory.CloneTypeInstantiation] = []
  for
    index, entry in json_array(
      json_field(object, "typeInstantiations", path),
      path + ".map.typeInstantiations",
    ) {
    let entry_path = path + ".map.typeInstantiations[" + index.to_string() + "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(MalformedSnapshot, entry_path, "invalid type instantiation")
    }
    type_instantiations.push(
      CloneType(
        self.type_symbol(json_string(pair[0], entry_path), entry_path),
        self.decode_ty(pair[1], entry_path + "[1]"),
      ),
    )
  }
  for
    index, entry in json_array(
      json_field(object, "typeSymbolInstantiations", path),
      path + ".map.typeSymbolInstantiations",
    ) {
    let entry_path = path +
      ".map.typeSymbolInstantiations[" +
      index.to_string() +
      "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(
        MalformedSnapshot,
        entry_path,
        "invalid type-symbol instantiation",
      )
    }
    type_instantiations.push(
      CloneTypeSymbol(
        self.type_symbol(json_string(pair[0], entry_path), entry_path),
        self.type_symbol(json_string(pair[1], entry_path), entry_path),
      ),
    )
  }
  let logic_instantiations : Array[(@logic.LSymbol, @logic.LSymbol)] = []
  for
    index, entry in json_array(
      json_field(object, "logicInstantiations", path),
      path + ".map.logicInstantiations",
    ) {
    let entry_path = path +
      ".map.logicInstantiations[" +
      index.to_string() +
      "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(
        MalformedSnapshot,
        entry_path,
        "invalid logic instantiation",
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
      path + ".map.propositionInstantiations",
    ) {
    let entry_path = path +
      ".map.propositionInstantiations[" +
      index.to_string() +
      "]"
    let pair = json_array(entry, entry_path)
    if pair.length() != 2 {
      fail_snapshot(
        MalformedSnapshot,
        entry_path,
        "invalid proposition instantiation",
      )
    }
    proposition_instantiations.push(
      (
        self.proposition_symbol(json_string(pair[0], entry_path), entry_path),
        self.proposition_symbol(json_string(pair[1], entry_path), entry_path),
      ),
    )
  }
  @theory.CloneWitness::trusted_new(
    self.context.fresh_id(),
    self.theory_key(
      json_string(source_value, path + ".source"),
      path + ".source",
    ),
    json_uint(ordinal_value, path + ".ordinal"),
    type_instantiations,
    logic_instantiations,
    proposition_instantiations,
    None,
  )
}

///|
fn SnapshotDecoder::decode_theories(
  self : SnapshotDecoder,
  value : Json,
) -> Map[String, @theory.Theory] raise {
  let theories : Map[String, @theory.Theory] = Map([])
  for index, encoded in json_array(value, "$.theories") {
    let path = "$.theories[" + index.to_string() + "]"
    let object = json_object(encoded, path)
    let key_text = json_string(json_field(object, "key", path), path + ".key")
    let items : Array[@theory.TheoryItem] = []
    for
      item_index, item in json_array(
        json_field(object, "items", path),
        path + ".items",
      ) {
      let item_path = path + ".items[" + item_index.to_string() + "]"
      let item_object = json_object(item, item_path)
      let ordinal = json_int(
        json_field(item_object, "ordinal", item_path),
        item_path + ".ordinal",
      )
      if ordinal != item_index {
        fail_snapshot(MalformedSnapshot, item_path, "theory item order drift")
      }
      let (tag, fields) = tagged(
        json_field(item_object, "node", item_path),
        item_path + ".node",
      )
      items.push(
        match tag {
          "Decl" => {
            require_tag_arity(fields, 1, item_path + ".node")
            TheoryDecl(
              self.decode_declaration(fields[1], item_path + ".node[1]"),
            )
          }
          "Use" => {
            require_tag_arity(fields, 1, item_path + ".node")
            TheoryUse(
              self.theory_key(
                json_string(fields[1], item_path + ".node[1]"),
                item_path + ".node[1]",
              ),
            )
          }
          "Clone" => {
            require_tag_arity(fields, 3, item_path + ".node")
            TheoryClone(
              self.decode_clone_witness(
                fields[1],
                fields[2],
                fields[3],
                item_path + ".node",
              ),
            )
          }
          "Meta" => {
            require_tag_arity(fields, 1, item_path + ".node")
            TheoryMeta(self.decode_meta(fields[1], item_path + ".node[1]"))
          }
          _ =>
            fail_snapshot(
              UnsupportedSnapshotVariant,
              item_path,
              "unknown theory item",
            )
        },
      )
    }
    theories[key_text] = @theory.Theory::trusted_snapshot(
      self.context,
      self.theory_key(key_text, path + ".key"),
      semantic_name(json_field(object, "name", path), path + ".name"),
      items,
      self.decode_namespace(
        json_field(object, "exportNamespace", path),
        path + ".exportNamespace",
      ),
      [],
      None,
    )
  }
  complete_theory_known_maps(theories)
}

///|
fn complete_theory_known_map(
  key : @theory.TheoryKey,
  raw : Map[@theory.TheoryKey, @theory.Theory],
  completed : Map[@theory.TheoryKey, @theory.Theory],
  visiting : Map[@theory.TheoryKey, Unit],
) -> @theory.Theory raise {
  if completed.get(key) is Some(theory) {
    return theory
  }
  if visiting.contains(key) {
    fail_snapshot(
      SemanticInvariantFailure,
      "$.theories",
      "trusted theory Use graph contains a cycle",
    )
  }
  guard raw.get(key) is Some(theory) else {
    fail_snapshot(
      UnknownReference,
      "$.theories",
      "trusted theory Use target is absent",
    )
  }
  visiting[key] = ()
  let used : Array[@theory.Theory] = []
  for item in theory.view().items {
    match item {
      TheoryUse(used_key) =>
        used.push(complete_theory_known_map(used_key, raw, completed, visiting))
      TheoryDecl(_) | TheoryClone(_) | TheoryMeta(_) => ()
    }
  }
  visiting.remove(key)
  let theory = theory.trusted_import_known(used, None)
  completed[key] = theory
  theory
}

///|
fn complete_theory_known_maps(
  theories : Map[String, @theory.Theory],
) -> Map[String, @theory.Theory] raise {
  let raw : Map[@theory.TheoryKey, @theory.Theory] = Map([])
  for entry in theories.to_array() {
    raw[entry.1.key()] = entry.1
  }
  let completed : Map[@theory.TheoryKey, @theory.Theory] = Map([])
  let visiting : Map[@theory.TheoryKey, Unit] = Map([])
  let result : Map[String, @theory.Theory] = Map([])
  for entry in theories.to_array() {
    result[entry.0] = complete_theory_known_map(
      entry.1.key(),
      raw,
      completed,
      visiting,
    )
  }
  result
}
