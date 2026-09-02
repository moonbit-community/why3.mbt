// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn v3_program_type_declaration(
  state : CanonicalV3State,
  declaration : @mlw.ProgramTypeDeclaration,
) -> CanonicalValue {
  let view = declaration.view()
  v3_node(b"Pdecl.its_defn", [
    v3_program_type_symbol(state, view.symbol),
    v3_sequence([ for field in view.fields => v3_routine_symbol(state, field) ]),
    v3_sequence(
      [
        for constructor_symbol in view.constructors => {
          v3_routine_symbol(state, constructor_symbol)
        }
      ],
    ),
    v3_sequence(
      [
        for invariant in view.invariants => v3_term(state, [], invariant)
      ],
    ),
    match view.witness {
      None => v3_none()
      Some(witness) => v3_some(v3_expr(state, [], witness))
    },
  ])
}

///|
fn v3_program_computation(
  state : CanonicalV3State,
  computation : @mlw.ProgramComputation,
) -> CanonicalValue {
  if computation is Cexpression(expression) {
    return v3_cexp(state, [], expression)
  }
  let (index, position) = state.reserve(V3ComputationExpression)
  let cty = computation.cty()
  let node = match computation {
    Cany(_) => v3_node(b"Expr.cexp_node.Cany", [v3_unit()])
    Cfun(_, None) => v3_node(b"Expr.cexp_node.Cany", [v3_unit()])
    Cfun(_, Some(body)) =>
      v3_node(b"Expr.cexp_node.Cfun", [
        v3_expr(state, cty.view().arguments, body),
      ])
    Cexpression(_) => abort("handled above")
  }
  state.fill(
    V3ComputationExpression,
    index,
    position,
    v3_node(b"Expr.cexp", [node, v3_cty(state, cty)]),
  )
  v3_reference(V3ComputationExpression, index)
}

///|
fn v3_program_declaration_parts(
  declaration : @mlw.ProgramDeclaration,
) -> (Array[@logic.Decl], Array[@theory.Meta]) {
  match declaration {
    PDtype(_, pure, metas)
    | PDpure(pure, metas)
    | PDlet(_, _, pure, metas)
    | PDvar(_, _, pure, metas)
    | PDrec(_, pure, metas)
    | PDexn(_, pure, metas) => (pure, metas)
  }
}

///|
fn v3_program_declaration(
  state : CanonicalV3State,
  declaration : @mlw.ProgramDeclaration,
) -> CanonicalValue {
  let (index, position) = state.reserve(V3ProgramDeclaration)
  let node = match declaration {
    PDtype(declarations, _, _) =>
      v3_node(b"Pdecl.pdecl_node.PDtype", [
        v3_sequence(
          [
            for declaration in declarations => {
              v3_program_type_declaration(state, declaration)
            }
          ],
        ),
      ])
    PDpure(_, _) => v3_node(b"Pdecl.pdecl_node.PDpure", [v3_unit()])
    PDlet(symbol, computation, _, _) =>
      v3_node(b"Pdecl.pdecl_node.PDlet", [
        v3_node(b"Expr.let_defn.LDsym", [
          v3_product([
            v3_routine_symbol(state, symbol),
            v3_program_computation(state, computation),
          ]),
        ]),
      ])
    PDvar(variable, value, _, _) =>
      v3_node(b"Pdecl.pdecl_node.PDlet", [
        v3_node(b"Expr.let_defn.LDvar", [
          v3_product([
            v3_program_binder(state, [variable], variable),
            v3_expr(state, [], value),
          ]),
        ]),
      ])
    PDrec(definitions, _, _) =>
      v3_node(b"Pdecl.pdecl_node.PDlet", [
        v3_node(b"Expr.let_defn.LDrec", [
          v3_sequence(
            [
              for definition in definitions => {
                v3_recursive_definition(state, [], definition)
              }
            ],
          ),
        ]),
      ])
    PDexn(exception, _, _) =>
      v3_node(b"Pdecl.pdecl_node.PDexn", [v3_exception_symbol(state, exception)])
  }
  let (pure, metas) = v3_program_declaration_parts(declaration)
  state.fill(
    V3ProgramDeclaration,
    index,
    position,
    v3_node(b"Pdecl.pdecl", [
      node,
      v3_sequence(
        [
          for pure_declaration in pure => v3_decl(state, pure_declaration)
        ],
      ),
      v3_sequence([ for meta in metas => v3_meta_application(state, meta) ]),
    ]),
  )
  v3_reference(V3ProgramDeclaration, index)
}

///|
fn v3_program_symbol_variable(
  state : CanonicalV3State,
  variable : @mlw.PVariable,
) -> CanonicalValue {
  v3_node(b"Pmodule.prog_symbol.PV", [v3_pvariable(state, variable)])
}

///|
fn v3_program_symbol_routine(
  state : CanonicalV3State,
  routine : @mlw.RoutineSymbol,
) -> CanonicalValue {
  v3_node(b"Pmodule.prog_symbol.RS", [v3_routine_symbol(state, routine)])
}

///|
fn v3_program_symbol_overload(
  state : CanonicalV3State,
  routines : ArrayView[@mlw.RoutineSymbol],
) -> CanonicalValue {
  v3_node(b"Pmodule.prog_symbol.OO", [
    v3_set([ for routine in routines => v3_routine_symbol(state, routine) ]),
  ])
}

///|
fn v3_program_namespace(
  state : CanonicalV3State,
  program_space : @mlw.ProgramNamespace,
) -> CanonicalValue {
  let view = program_space.view()
  let program_entries : Array[(CanonicalValue, CanonicalValue)] = []
  for entry in view.variables {
    program_entries.push(
      (v3_bytes(entry.0), v3_program_symbol_variable(state, entry.1)),
    )
  }
  for entry in view.routine_overloads {
    program_entries.push(
      (v3_bytes(entry.0), v3_program_symbol_overload(state, entry.1)),
    )
  }
  for entry in view.routines {
    if !view.routine_overloads.any(overload => overload.0 == entry.0) {
      program_entries.push(
        (v3_bytes(entry.0), v3_program_symbol_routine(state, entry.1)),
      )
    }
  }
  v3_node(b"Pmodule.namespace", [
    v3_map(
      [
        for entry in view.types => {
          (v3_bytes(entry.0), v3_program_type_symbol(state, entry.1))
        }
      ],
    ),
    v3_map(program_entries),
    v3_map(
      [
        for entry in view.exceptions => {
          (v3_bytes(entry.0), v3_exception_symbol(state, entry.1))
        }
      ],
    ),
    v3_map(
      [
        for entry in view.subspaces => {
          (v3_bytes(entry.0), v3_program_namespace(state, entry.1))
        }
      ],
    ),
  ])
}

///|
fn v3_module_source(
  state : CanonicalV3State,
  owner : @mlw.Pmodule,
  key : @theory.TheoryKey,
) -> CanonicalValue {
  if owner.key() == key {
    v3_pmodule(state, owner)
  } else {
    guard owner.referenced_module(key) is Some(source) else {
      abort("canonical v3 requires the complete referenced module graph")
    }
    v3_pmodule(state, source)
  }
}

///|
fn v3_program_clone_witness(
  state : CanonicalV3State,
  owner : @mlw.Pmodule,
  witness : @mlw.ProgramCloneWitness,
) -> CanonicalValue {
  let view = witness.view()
  v3_node(b"Pmodule.mod_inst", [
    v3_module_source(state, owner, view.source),
    v3_map(
      [
        for entry in view.type_instantiations => {
          (v3_type_symbol(state, entry.0), v3_ity(state, entry.1))
        }
      ],
    ),
    v3_map(
      [
        for entry in view.program_type_instantiations => {
          (
            v3_type_symbol(state, entry.0),
            v3_program_type_symbol(state, entry.1),
          )
        }
      ],
    ),
    v3_map(
      [
        for entry in view.logic_instantiations => {
          (v3_lsymbol(state, entry.0), v3_lsymbol(state, entry.1))
        }
      ],
    ),
    v3_map(
      [
        for entry in view.proposition_instantiations => {
          (v3_prsymbol(state, entry.0), v3_prsymbol(state, entry.1))
        }
      ],
    ),
    v3_map(
      [
        for entry in view.proposition_kinds => {
          (v3_prsymbol(state, entry.0), v3_proposition_kind(entry.1))
        }
      ],
    ),
    v3_map(
      [
        for entry in view.program_variable_instantiations => {
          (v3_vsymbol(state, entry.0), v3_pvariable(state, entry.1))
        }
      ],
    ),
    v3_map(
      [
        for entry in view.routine_instantiations => {
          (v3_routine_symbol(state, entry.0), v3_routine_symbol(state, entry.1))
        }
      ],
    ),
    v3_map(
      [
        for entry in view.exception_instantiations => {
          (
            v3_exception_symbol(state, entry.0),
            v3_exception_symbol(state, entry.1),
          )
        }
      ],
    ),
    v3_proposition_kind(view.default_proposition_kind),
  ])
}

///|
fn v3_module_item(
  state : CanonicalV3State,
  owner : @mlw.Pmodule,
  item : @mlw.ModuleItem,
) -> CanonicalValue {
  match item {
    Udecl(declaration) =>
      v3_node(b"Pmodule.mod_unit.Udecl", [
        v3_program_declaration(state, declaration),
      ])
    Uuse(key) =>
      v3_node(b"Pmodule.mod_unit.Uuse", [v3_module_source(state, owner, key)])
    Uclone(witness) =>
      v3_node(b"Pmodule.mod_unit.Uclone", [
        v3_program_clone_witness(state, owner, witness),
      ])
    Umeta(meta) =>
      v3_node(b"Pmodule.mod_unit.Umeta", [v3_meta_application(state, meta)])
    Uscope(name, items) =>
      v3_node(b"Pmodule.mod_unit.Uscope", [
        v3_product([v3_bytes(name), v3_module_items(state, owner, items)]),
      ])
  }
}

///|
fn v3_module_items(
  state : CanonicalV3State,
  owner : @mlw.Pmodule,
  items : ArrayView[@mlw.ModuleItem],
) -> CanonicalValue {
  let encoded : Array[CanonicalValue] = []
  for item in items {
    if state.omit_generated_vcs &&
      item is Udecl(declaration) &&
      v3_is_generated_vc_program_declaration(declaration) {
      continue
    }
    encoded.push(v3_module_item(state, owner, item))
  }
  v3_sequence(encoded)
}

///|
fn v3_pmodule(
  state : CanonicalV3State,
  pmodule : @mlw.Pmodule,
) -> CanonicalValue {
  let view = pmodule.view()
  match state.module_indices.get(view.key) {
    Some(index) => v3_reference(V3Module, index)
    None => {
      let (index, position) = state.reserve(V3Module)
      state.module_indices[view.key] = index
      state.fill(
        V3Module,
        index,
        position,
        v3_node(b"Pmodule.pmodule", [
          v3_theory(state, view.pure_theory),
          v3_module_items(state, pmodule, view.items),
          v3_program_namespace(state, view.export_namespace),
        ]),
      )
      v3_reference(V3Module, index)
    }
  }
}

///|
pub fn encode_pmodule(pmodule : @mlw.Pmodule) -> CanonicalJson {
  let state = CanonicalV3State::new_omitting_generated_vcs()
  state.finish([v3_pmodule(state, pmodule)])
}

///|
fn encode_pmodule_for_source(
  pmodule : @mlw.Pmodule,
  selected_source_path : BytesView,
) -> CanonicalJson {
  let state = CanonicalV3State::new_omitting_generated_vcs_for_source(
    selected_source_path,
  )
  state.finish([v3_pmodule(state, pmodule)])
}
