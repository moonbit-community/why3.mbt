// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn v3_semantic_name_origin(name : @theory.SemanticName) -> @identity.Origin {
  let view = name.view()
  @identity.Origin::user(view.name, view.source_span, view.attributes)
}

///|
fn v3_fresh_identifier(
  state : CanonicalV3State,
  origin : @identity.Origin,
) -> CanonicalValue {
  let (index, position) = state.reserve(V3Identifier)
  state.fill(
    V3Identifier,
    index,
    position,
    v3_product([
      v3_node(b"Ident.ident", [
        v3_bytes(origin.display_name()),
        v3_attributes(state, origin.attributes()),
        v3_source_span_option(origin.identifier_source_span()),
      ]),
      v3_origin(state, origin),
    ]),
  )
  v3_reference(V3Identifier, index)
}

///|
fn v3_meta_argument_type(
  argument_type : @theory.MetaArgumentType,
) -> CanonicalValue {
  let tag = match argument_type {
    MetaTypeArgument => b"Theory.meta_arg_type.MTty"
    MetaTypeSymbolArgument => b"Theory.meta_arg_type.MTtysymbol"
    MetaLogicSymbolArgument => b"Theory.meta_arg_type.MTlsymbol"
    MetaPropositionSymbolArgument => b"Theory.meta_arg_type.MTprsymbol"
    MetaStringArgument => b"Theory.meta_arg_type.MTstring"
    MetaIntegerArgument => b"Theory.meta_arg_type.MTint"
    MetaIdentifierArgument => b"Theory.meta_arg_type.MTid"
  }
  v3_node(tag, [v3_unit()])
}

///|
fn v3_meta_descriptor(meta : @theory.Meta) -> CanonicalValue {
  let view = meta.view()
  v3_node(b"Theory.meta", [
    v3_bytes(view.name),
    v3_sequence(
      [
        for argument_type in view.argument_types => {
          v3_meta_argument_type(argument_type)
        }
      ],
    ),
    v3_bool(view.exclusive),
  ])
}

///|
fn v3_meta_argument(
  state : CanonicalV3State,
  argument : @theory.MetaArgument,
) -> CanonicalValue {
  match argument {
    MetaType(ty) => v3_node(b"Theory.meta_arg.MAty", [v3_ty(state, ty)])
    MetaTypeSymbol(symbol) =>
      v3_node(b"Theory.meta_arg.MAts", [v3_type_symbol(state, symbol)])
    MetaLogicSymbol(symbol) =>
      v3_node(b"Theory.meta_arg.MAls", [v3_lsymbol(state, symbol)])
    MetaPropositionSymbol(symbol) =>
      v3_node(b"Theory.meta_arg.MApr", [v3_prsymbol(state, symbol)])
    MetaString(value) => v3_node(b"Theory.meta_arg.MAstr", [v3_bytes(value)])
    MetaInteger(value) => v3_node(b"Theory.meta_arg.MAint", [v3_int64(value)])
    MetaIdentifier(name) =>
      v3_node(b"Theory.meta_arg.MAid", [
        v3_fresh_identifier(state, v3_semantic_name_origin(name)),
      ])
  }
}

///|
fn v3_meta_application(
  state : CanonicalV3State,
  meta : @theory.Meta,
) -> CanonicalValue {
  let view = meta.view()
  v3_product([
    v3_meta_descriptor(meta),
    v3_sequence(
      [
        for argument in view.arguments => v3_meta_argument(state, argument)
      ],
    ),
  ])
}

///|
fn v3_symbol_map(
  state : CanonicalV3State,
  map : @theory.SymbolMap,
) -> CanonicalValue {
  let view = map.view()
  v3_node(b"Theory.symbol_map", [
    v3_map(
      [
        for entry in view.sm_ty => {
          (v3_type_symbol(state, entry.0), v3_ty(state, entry.1))
        }
      ],
    ),
    v3_map(
      [
        for entry in view.sm_ts => {
          (v3_type_symbol(state, entry.0), v3_type_symbol(state, entry.1))
        }
      ],
    ),
    v3_map(
      [
        for entry in view.sm_ls => {
          (v3_lsymbol(state, entry.0), v3_lsymbol(state, entry.1))
        }
      ],
    ),
    v3_map(
      [
        for entry in view.sm_pr => {
          (v3_prsymbol(state, entry.0), v3_prsymbol(state, entry.1))
        }
      ],
    ),
  ])
}

///|
fn v3_namespace(
  state : CanonicalV3State,
  theory_space : @theory.Namespace,
) -> CanonicalValue {
  let view = theory_space.view()
  v3_node(b"Theory.namespace", [
    v3_map(
      [
        for entry in view.types => {
          (v3_bytes(entry.0), v3_type_symbol(state, entry.1))
        }
      ],
    ),
    v3_map(
      [
        for entry in view.logic => {
          (v3_bytes(entry.0), v3_lsymbol(state, entry.1))
        }
      ],
    ),
    v3_map(v3_namespace_propositions(state, view.propositions)),
    v3_map(
      [
        for entry in view.subspaces => {
          (v3_bytes(entry.0), v3_namespace(state, entry.1))
        }
      ],
    ),
  ])
}

///|
fn v3_namespace_propositions(
  state : CanonicalV3State,
  propositions : ArrayView[(Bytes, @logic.PrSymbol)],
) -> Array[(CanonicalValue, CanonicalValue)] {
  let encoded : Array[(CanonicalValue, CanonicalValue)] = []
  for entry in propositions {
    if state.omit_generated_vcs &&
      v3_is_generated_vc_proposition(entry.1) &&
      !state.generated_type_vcs.contains(entry.1) {
      continue
    }
    encoded.push((v3_bytes(entry.0), v3_prsymbol(state, entry.1)))
  }
  encoded
}

///|
fn v3_declaration_defines_type_name(
  declaration : @logic.Decl,
  name : BytesView,
) -> Bool {
  match declaration.view() {
    Dtype(symbols) => symbols.any(symbol => symbol.view().name[:] == name)
    Ddata(declarations) =>
      declarations.any(declaration => {
        declaration.view().type_symbol.view().name[:] == name
      })
    Dparam(_) | Dlogic(_) | Dind(_, _) | Dprop(_, _, _) => false
  }
}

///|
fn v3_register_generated_type_vcs(
  state : CanonicalV3State,
  items : ArrayView[@theory.TheoryItem],
) -> Unit {
  if !state.retain_generated_type_vcs {
    return
  }
  let suffix = b"'vc"
  for index = 0; index + 1 < items.length(); index = index + 1 {
    guard items[index] is TheoryDecl(goal) &&
      goal.view() is Dprop(Pgoal, proposition, _) &&
      v3_is_generated_vc_proposition(proposition) &&
      items[index + 1] is TheoryDecl(following) else {
      continue
    }
    let name = proposition.view().name
    if name.length() > suffix.length() &&
      name.has_suffix(suffix) &&
      v3_declaration_defines_type_name(
        following,
        name[:name.length() - suffix.length()],
      ) {
      state.generated_type_vcs[proposition] = ()
    }
  }
}

///|
fn v3_theory_source(
  state : CanonicalV3State,
  owner : @theory.Theory,
  key : @theory.TheoryKey,
) -> CanonicalValue {
  if owner.key() == key {
    v3_theory(state, owner)
  } else {
    guard owner.clone_source(key) is Some(source) else {
      abort("canonical v3 requires the complete referenced theory graph")
    }
    v3_theory(state, source)
  }
}

///|
fn v3_task_source(
  state : CanonicalV3State,
  task : @theory.Task,
  key : @theory.TheoryKey,
) -> CanonicalValue {
  guard task.referenced_theory(key) is Some(source) else {
    abort("canonical v3 requires the complete Task dependency graph")
  }
  v3_theory(state, source)
}

///|
fn v3_theory_tdecl(
  state : CanonicalV3State,
  owner : @theory.Theory,
  item : @theory.TheoryItem,
) -> CanonicalValue {
  let (index, position) = state.reserve(V3TheoryDeclaration)
  let node = match item {
    TheoryDecl(declaration) =>
      v3_node(b"Theory.tdecl_node.Decl", [v3_decl(state, declaration)])
    TheoryUse(key) =>
      v3_node(b"Theory.tdecl_node.Use", [v3_theory_source(state, owner, key)])
    TheoryClone(witness) => {
      let view = witness.view()
      v3_node(b"Theory.tdecl_node.Clone", [
        v3_product([
          v3_theory_source(state, owner, view.source),
          v3_symbol_map(state, witness.symbol_map()),
        ]),
      ])
    }
    TheoryMeta(meta) =>
      v3_node(b"Theory.tdecl_node.Meta", [v3_meta_application(state, meta)])
  }
  state.fill(
    V3TheoryDeclaration,
    index,
    position,
    v3_node(b"Theory.tdecl", [node]),
  )
  v3_reference(V3TheoryDeclaration, index)
}

///|
fn v3_task_tdecl(
  state : CanonicalV3State,
  task : @theory.Task,
  item : @theory.TheoryItem,
) -> CanonicalValue {
  let (index, position) = state.reserve(V3TheoryDeclaration)
  let node = match item {
    TheoryDecl(declaration) =>
      v3_node(b"Theory.tdecl_node.Decl", [v3_decl(state, declaration)])
    TheoryUse(key) =>
      v3_node(b"Theory.tdecl_node.Use", [v3_task_source(state, task, key)])
    TheoryClone(witness) => {
      let view = witness.view()
      v3_node(b"Theory.tdecl_node.Clone", [
        v3_product([
          v3_task_source(state, task, view.source),
          v3_symbol_map(state, witness.symbol_map()),
        ]),
      ])
    }
    TheoryMeta(meta) =>
      v3_node(b"Theory.tdecl_node.Meta", [v3_meta_application(state, meta)])
  }
  state.fill(
    V3TheoryDeclaration,
    index,
    position,
    v3_node(b"Theory.tdecl", [node]),
  )
  v3_reference(V3TheoryDeclaration, index)
}

///|
fn v3_theory(
  state : CanonicalV3State,
  theory : @theory.Theory,
) -> CanonicalValue {
  let view = theory.view()
  match state.theory_indices.get(view.key) {
    Some(index) => v3_reference(V3Theory, index)
    None => {
      let (index, position) = state.reserve(V3Theory)
      state.theory_indices[view.key] = index
      v3_register_generated_type_vcs(state, view.items)
      state.fill(
        V3Theory,
        index,
        position,
        v3_node(b"Theory.theory", [
          v3_identifier(
            state,
            theory.context_anchor(),
            v3_semantic_name_origin(view.name),
          ),
          v3_sequence(
            [
              for segment in view.key.view().path => v3_bytes(segment)
            ],
          ),
          v3_theory_items(state, theory, view.items),
          v3_namespace(state, view.export_namespace),
        ]),
      )
      v3_reference(V3Theory, index)
    }
  }
}

///|
fn v3_theory_items(
  state : CanonicalV3State,
  theory : @theory.Theory,
  items : ArrayView[@theory.TheoryItem],
) -> CanonicalValue {
  let encoded : Array[CanonicalValue] = []
  for item in items {
    if state.omit_generated_vcs &&
      item is TheoryDecl(declaration) &&
      v3_is_generated_vc_declaration(declaration) &&
      !(declaration.view() is Dprop(Pgoal, proposition, _) &&
      state.generated_type_vcs.contains(proposition)) {
      continue
    }
    encoded.push(v3_theory_tdecl(state, theory, item))
  }
  v3_sequence(encoded)
}

///|
fn v3_task_head(
  state : CanonicalV3State,
  task : @theory.Task,
  head : @theory.TaskHead,
) -> CanonicalValue {
  let (index, position) = state.reserve(V3Task)
  let view = head.view()
  state.fill(
    V3Task,
    index,
    position,
    v3_node(b"Task.task_hd", [
      v3_task_tdecl(state, task, view.task_decl.view().td_node),
      match view.task_prev {
        None => v3_none()
        Some(previous) => v3_some(v3_task_head(state, task, previous))
      },
    ]),
  )
  v3_reference(V3Task, index)
}

///|
fn v3_task(state : CanonicalV3State, task : @theory.Task) -> CanonicalValue {
  guard task.head() is Some(head) else {
    abort("canonical v3 cannot encode an empty task")
  }
  v3_task_head(state, task, head)
}

///|
pub fn encode_theory(theory : @theory.Theory) -> CanonicalJson {
  let state = CanonicalV3State::new()
  state.finish([v3_theory(state, theory)])
}

///|
fn encode_theory_for_source(
  theory : @theory.Theory,
  selected_source_path : BytesView,
) -> CanonicalJson {
  let state = CanonicalV3State::new_for_source(selected_source_path)
  state.finish([v3_theory(state, theory)])
}

///|
pub fn encode_task(task : @theory.Task) -> CanonicalJson {
  let state = CanonicalV3State::new_omitting_generated_routine_vcs()
  state.finish([v3_task(state, task)])
}

///|
fn encode_task_for_source(
  task : @theory.Task,
  selected_source_path : BytesView,
) -> CanonicalJson {
  let state = CanonicalV3State::new_omitting_generated_routine_vcs_for_source(
    selected_source_path,
  )
  state.finish([v3_task(state, task)])
}
