// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn canonical_theory_key(key : @theory.TheoryKey) -> CanonicalValue {
  let view = key.view()
  canonical_array([
    canonical_text(b"TheoryKey"),
    canonical_array([ for segment in view.path => canonical_hex(segment) ]),
    canonical_hex(view.name),
  ])
}

///|
fn canonical_semantic_name(name : @theory.SemanticName) -> CanonicalValue {
  let view = name.view()
  canonical_array([
    canonical_text(b"Origin.User"),
    canonical_hex(view.name),
    canonical_source_span_option(view.source_span),
    canonical_attributes(view.attributes),
  ])
}

///|
fn canonical_meta_argument(
  numbering : GlobalSymbolNumbering,
  argument : @theory.MetaArgument,
) -> CanonicalValue {
  match argument {
    MetaType(ty) =>
      canonical_array([
        canonical_text(b"MetaArgument.Type"),
        canonical_ty(numbering, ty),
      ])
    MetaTypeSymbol(symbol) =>
      canonical_array([
        canonical_text(b"MetaArgument.TypeSymbol"),
        canonical_type_identity(numbering, symbol.semantic_id()),
      ])
    MetaLogicSymbol(symbol) =>
      canonical_array([
        canonical_text(b"MetaArgument.LogicSymbol"),
        canonical_logic_identity(numbering, symbol.semantic_id()),
      ])
    MetaPropositionSymbol(symbol) =>
      canonical_array([
        canonical_text(b"MetaArgument.PropositionSymbol"),
        canonical_proposition_identity(numbering, symbol.semantic_id()),
      ])
    MetaString(value) =>
      canonical_array([
        canonical_text(b"MetaArgument.String"),
        canonical_hex(value),
      ])
    MetaInteger(value) =>
      canonical_array([canonical_text(b"MetaArgument.Integer"), Signed(value)])
    MetaIdentifier(value) =>
      canonical_array([
        canonical_text(b"MetaArgument.Identifier"),
        canonical_semantic_name(value),
      ])
  }
}

///|
fn canonical_meta(
  numbering : GlobalSymbolNumbering,
  meta : @theory.Meta,
) -> CanonicalValue {
  let view = meta.view()
  canonical_array([
    canonical_text(b"Meta"),
    canonical_hex(view.name),
    canonical_array(
      [
        for argument in view.arguments => {
          canonical_meta_argument(numbering, argument)
        }
      ],
    ),
  ])
}

///|
fn canonical_clone_type_instantiations(
  numbering : GlobalSymbolNumbering,
  entries : ArrayView[@theory.CloneTypeInstantiation],
) -> CanonicalValue {
  let encoded : Array[(CanonicalValue, CanonicalValue)] = []
  for entry in entries {
    match entry {
      CloneType(source, target) =>
        encoded.push(
          (
            canonical_type_identity(numbering, source.semantic_id()),
            canonical_array([
              canonical_text(b"Clone.Type"),
              canonical_ty(numbering, target),
            ]),
          ),
        )
      CloneTypeSymbol(source, target) =>
        encoded.push(
          (
            canonical_type_identity(numbering, source.semantic_id()),
            canonical_array([
              canonical_text(b"Clone.TypeSymbol"),
              canonical_type_identity(numbering, target.semantic_id()),
            ]),
          ),
        )
    }
  }
  canonical_semantic_map(encoded)
}

///|
fn canonical_clone_logic_instantiations(
  numbering : GlobalSymbolNumbering,
  entries : ArrayView[(@logic.LSymbol, @logic.LSymbol)],
) -> CanonicalValue {
  canonical_semantic_map(
    [
      for entry in entries => {
        (
          canonical_logic_identity(numbering, entry.0.semantic_id()),
          canonical_logic_identity(numbering, entry.1.semantic_id()),
        )
      }
    ],
  )
}

///|
fn canonical_clone_proposition_instantiations(
  numbering : GlobalSymbolNumbering,
  entries : ArrayView[(@logic.PrSymbol, @logic.PrSymbol)],
) -> CanonicalValue {
  canonical_semantic_map(
    [
      for entry in entries => {
        (
          canonical_proposition_identity(numbering, entry.0.semantic_id()),
          canonical_proposition_identity(numbering, entry.1.semantic_id()),
        )
      }
    ],
  )
}

///|
fn canonical_clone_witness(
  numbering : GlobalSymbolNumbering,
  witness : @theory.CloneWitness,
) -> CanonicalValue {
  let view = witness.view()
  canonical_array([
    canonical_text(b"CloneWitness"),
    canonical_theory_key(view.source),
    Unsigned(view.source_item_identity),
    canonical_clone_type_instantiations(numbering, view.type_instantiations),
    canonical_clone_logic_instantiations(numbering, view.logic_instantiations),
    canonical_clone_proposition_instantiations(
      numbering,
      view.proposition_instantiations,
    ),
  ])
}

///|
fn canonical_namespace(
  numbering : GlobalSymbolNumbering,
  namespace_value : @theory.Namespace,
) -> CanonicalValue {
  let view = namespace_value.view()
  canonical_array([
    canonical_text(b"Namespace"),
    canonical_semantic_map(
      [
        for entry in view.types => {
          (
            canonical_hex(entry.0),
            canonical_type_identity(numbering, entry.1.semantic_id()),
          )
        }
      ],
    ),
    canonical_semantic_map(
      [
        for entry in view.logic => {
          (
            canonical_hex(entry.0),
            canonical_logic_identity(numbering, entry.1.semantic_id()),
          )
        }
      ],
    ),
    canonical_semantic_map(
      [
        for entry in view.propositions => {
          (
            canonical_hex(entry.0),
            canonical_proposition_identity(numbering, entry.1.semantic_id()),
          )
        }
      ],
    ),
    canonical_semantic_map(
      [
        for entry in view.subspaces => {
          (canonical_hex(entry.0), canonical_namespace(numbering, entry.1))
        }
      ],
    ),
  ])
}

///|
fn canonical_theory_item(
  numbering : GlobalSymbolNumbering,
  item : @theory.TheoryItem,
) -> CanonicalValue {
  match item {
    TheoryDecl(declaration) =>
      canonical_array([
        canonical_text(b"TheoryItem.Decl"),
        canonical_decl(numbering, declaration),
      ])
    TheoryUse(source) =>
      canonical_array([
        canonical_text(b"TheoryItem.Use"),
        canonical_theory_key(source),
      ])
    TheoryClone(witness) =>
      canonical_array([
        canonical_text(b"TheoryItem.Clone"),
        canonical_clone_witness(numbering, witness),
      ])
    TheoryMeta(meta) =>
      canonical_array([
        canonical_text(b"TheoryItem.Meta"),
        canonical_meta(numbering, meta),
      ])
  }
}

///|
fn canonical_task_item(
  numbering : GlobalSymbolNumbering,
  item : @theory.TheoryItem,
) -> CanonicalValue {
  match item {
    TheoryDecl(declaration) =>
      canonical_array([
        canonical_text(b"TaskItem.Decl"),
        canonical_decl(numbering, declaration),
      ])
    TheoryUse(source) =>
      canonical_array([
        canonical_text(b"TaskItem.Use"),
        canonical_theory_key(source),
      ])
    TheoryClone(witness) =>
      canonical_array([
        canonical_text(b"TaskItem.Clone"),
        canonical_clone_witness(numbering, witness),
      ])
    TheoryMeta(meta) =>
      canonical_array([
        canonical_text(b"TaskItem.Meta"),
        canonical_meta(numbering, meta),
      ])
  }
}

///|
fn canonical_theory(
  numbering : GlobalSymbolNumbering,
  theory : @theory.Theory,
) -> CanonicalValue {
  let view = theory.view()
  canonical_array([
    canonical_text(b"Theory"),
    canonical_theory_key(view.key),
    canonical_semantic_name(view.name),
    canonical_array(
      [
        for item in view.items => canonical_theory_item(numbering, item)
      ],
    ),
    canonical_namespace(numbering, view.export_namespace),
  ])
}

///|
pub fn encode_theory(theory : @theory.Theory) -> CanonicalJson {
  encode_canonical_value(canonical_theory(GlobalSymbolNumbering::new(), theory))
}

///|
fn canonical_task(
  numbering : GlobalSymbolNumbering,
  task : @theory.Task,
) -> CanonicalValue {
  let view = task.view()
  canonical_array([
    canonical_text(b"Task"),
    canonical_array(
      [
        for item in view.items => canonical_task_item(numbering, item)
      ],
    ),
  ])
}

///|
pub fn encode_task(task : @theory.Task) -> CanonicalJson {
  encode_canonical_value(canonical_task(GlobalSymbolNumbering::new(), task))
}
