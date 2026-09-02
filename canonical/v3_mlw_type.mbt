// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn v3_program_mask(mask : @mlw.ProgramMask) -> CanonicalValue {
  match mask {
    Visible => v3_node(b"Ity.mask.MaskVisible", [v3_unit()])
    Ghost => v3_node(b"Ity.mask.MaskGhost", [v3_unit()])
    Tuple(items) =>
      v3_node(b"Ity.mask.MaskTuple", [
        v3_sequence([ for item in items => v3_program_mask(item) ]),
      ])
  }
}

///|
fn v3_program_type_flag(flag : @mlw.ProgramTypeArgumentFlag) -> CanonicalValue {
  v3_node(b"Ity.its_flag", [
    v3_bool(flag.frozen),
    v3_bool(flag.exposed),
    v3_bool(flag.liable),
    v3_bool(flag.fixed),
    v3_bool(flag.visible),
  ])
}

///|
fn v3_program_type_definition(
  state : CanonicalV3State,
  definition : @mlw.ProgramTypeDefinition,
) -> CanonicalValue {
  match definition {
    ProgramNoDef => v3_node(b"Ty.type_def.NoDef", [v3_unit()])
    ProgramAlias(ity) => v3_node(b"Ty.type_def.Alias", [v3_ity(state, ity)])
    ProgramRange(lower, upper) =>
      v3_node(b"Ty.type_def.Range", [
        v3_product([
          v3_bigint_text(lower.to_string()),
          v3_bigint_text(upper.to_string()),
        ]),
      ])
    ProgramFloat(exponent_digits, significand_digits) =>
      v3_node(b"Ty.type_def.Float", [
        v3_product([v3_int(exponent_digits), v3_int(significand_digits)]),
      ])
  }
}

///|
fn v3_program_type_symbol(
  state : CanonicalV3State,
  symbol : @mlw.ProgramTypeSymbol,
) -> CanonicalValue {
  let kind = V3ProgramTypeSymbol
  let view = symbol.view()
  match state.semantic_index(kind, view.id) {
    Some(index) => v3_reference(kind, index)
    None => {
      let (index, position) = state.reserve(kind)
      state.remember_semantic_index(kind, view.id, index)
      let flags = view.flags
      state.fill(
        kind,
        index,
        position,
        v3_product([
          v3_node(b"Ity.itysymbol", [
            v3_type_symbol(state, view.logic_type),
            v3_bool(flags.nonfree),
            v3_bool(flags.private_),
            v3_bool(flags.mutable_),
            v3_bool(flags.fragile),
            v3_sequence(
              [
                for field in view.mutable_fields => v3_pvariable(state, field)
              ],
            ),
            v3_sequence(
              [
                for field in view.immutable_fields => v3_pvariable(state, field)
              ],
            ),
            v3_sequence(
              [
                for region in view.regions => v3_region(state, region)
              ],
            ),
            v3_sequence(
              [
                for flag in flags.argument_flags => v3_program_type_flag(flag)
              ],
            ),
            v3_sequence(
              [
                for flag in flags.region_flags => v3_program_type_flag(flag)
              ],
            ),
            v3_program_type_definition(state, view.definition),
          ]),
          v3_origin(state, view.origin),
        ]),
      )
      v3_reference(kind, index)
    }
  }
}

///|
fn v3_region(state : CanonicalV3State, region : @mlw.Region) -> CanonicalValue {
  let kind = V3Region
  let view = region.view()
  match state.semantic_index(kind, view.id) {
    Some(index) => v3_reference(kind, index)
    None => {
      let (index, position) = state.reserve(kind)
      state.remember_semantic_index(kind, view.id, index)
      state.fill(
        kind,
        index,
        position,
        v3_node(b"Ity.region", [
          v3_identifier(state, view.id, v3_semantic_name_origin(view.name)),
          v3_program_type_symbol(state, view.symbol),
          v3_sequence(
            [
              for argument in view.arguments => v3_ity(state, argument)
            ],
          ),
          v3_sequence([ for nested in view.regions => v3_ity(state, nested) ]),
        ]),
      )
      v3_reference(kind, index)
    }
  }
}

///|
fn v3_ity(state : CanonicalV3State, ity : @mlw.Ity) -> CanonicalValue {
  match state.ity_indices.get(ity) {
    Some(index) => v3_reference(V3Type, index)
    None => {
      let (index, position) = state.reserve(V3Type)
      state.ity_indices[ity] = index
      let node = match ity.view() {
        ItyVar(variable) =>
          v3_node(b"Ity.ity_node.Ityvar", [v3_tyvar_symbol(state, variable)])
        ItyApp(symbol, arguments, regions) =>
          v3_node(b"Ity.ity_node.Ityapp", [
            v3_product([
              v3_program_type_symbol(state, symbol),
              v3_sequence(
                [
                  for argument in arguments => v3_ity(state, argument)
                ],
              ),
              v3_sequence([ for region in regions => v3_ity(state, region) ]),
            ]),
          ])
        ItyReg(region) =>
          v3_node(b"Ity.ity_node.Ityreg", [v3_region(state, region)])
      }
      state.fill(V3Type, index, position, v3_node(b"Ity.ity", [node]))
      v3_reference(V3Type, index)
    }
  }
}

///|
fn v3_pvariable(
  state : CanonicalV3State,
  variable : @mlw.PVariable,
) -> CanonicalValue {
  let kind = V3ProgramVariable
  let view = variable.view()
  match state.semantic_index(kind, view.id) {
    Some(index) => v3_reference(kind, index)
    None => {
      let (index, position) = state.reserve(kind)
      state.remember_semantic_index(kind, view.id, index)
      state.fill(
        kind,
        index,
        position,
        v3_node(b"Ity.pvsymbol", [
          v3_vsymbol(state, view.pure_symbol),
          v3_ity(state, view.ity),
          v3_bool(view.ghost),
        ]),
      )
      v3_reference(kind, index)
    }
  }
}

///|
fn v3_exception_symbol(
  state : CanonicalV3State,
  symbol : @mlw.XSymbol,
) -> CanonicalValue {
  let kind = V3ExceptionSymbol
  let view = symbol.view()
  match state.semantic_index(kind, view.id) {
    Some(index) => v3_reference(kind, index)
    None => {
      let (index, position) = state.reserve(kind)
      state.remember_semantic_index(kind, view.id, index)
      state.fill(
        kind,
        index,
        position,
        v3_node(b"Ity.xsymbol", [
          v3_identifier(state, view.id, v3_semantic_name_origin(view.name)),
          v3_ity(state, view.ity),
          v3_program_mask(view.mask),
        ]),
      )
      v3_reference(kind, index)
    }
  }
}

///|
fn v3_bound_program_variable_index(
  bound : ArrayView[@mlw.PVariable],
  variable : @mlw.PVariable,
) -> UInt? {
  for index = bound.length() - 1; index >= 0; index = index - 1 {
    if bound[index] == variable {
      return Some((bound.length() - 1 - index).reinterpret_as_uint())
    }
  }
  None
}

///|
fn v3_extend_bound_program_variables(
  bound : ArrayView[@mlw.PVariable],
  variables : ArrayView[@mlw.PVariable],
) -> Array[@mlw.PVariable] {
  let result = bound.to_owned()
  result.push_iter(variables.iter())
  result
}

///|
fn v3_program_variable_reference(
  state : CanonicalV3State,
  bound : ArrayView[@mlw.PVariable],
  variable : @mlw.PVariable,
) -> CanonicalValue {
  match v3_bound_program_variable_index(bound, variable) {
    Some(index) => v3_de_bruijn(index)
    None => v3_pvariable(state, variable)
  }
}

///|
fn v3_program_binder(
  state : CanonicalV3State,
  bound : ArrayView[@mlw.PVariable],
  variable : @mlw.PVariable,
) -> CanonicalValue {
  let view = variable.view()
  match v3_bound_program_variable_index(bound, variable) {
    Some(index) =>
      v3_product([
        v3_de_bruijn(index),
        v3_ity(state, view.ity),
        v3_bool(view.ghost),
      ])
    None =>
      v3_product([
        v3_pvariable(state, variable),
        v3_ity(state, view.ity),
        v3_bool(view.ghost),
      ])
  }
}

///|
fn v3_program_termination(
  termination : @mlw.ProgramTermination,
) -> CanonicalValue {
  let tag = match termination {
    Total => b"Ity.oneway.Total"
    Partial => b"Ity.oneway.Partial"
    Diverges => b"Ity.oneway.Diverges"
  }
  v3_node(tag, [v3_unit()])
}

///|
fn v3_effect(
  state : CanonicalV3State,
  bound : ArrayView[@mlw.PVariable],
  effect : @mlw.Effect,
) -> CanonicalValue {
  let view = effect.view()
  v3_node(b"Ity.effect", [
    v3_set(
      [
        for variable in view.reads => {
          v3_program_variable_reference(state, bound, variable)
        }
      ],
    ),
    v3_map(
      [
        for write in view.writes => {
          let write_view = write.view()
          (
            v3_region(state, write_view.region),
            v3_set(
              [
                for field in write_view.fields => {
                  v3_program_variable_reference(state, bound, field)
                }
              ],
            ),
          )
        }
      ],
    ),
    v3_set([ for region in view.taints => v3_region(state, region) ]),
    v3_set([ for region in view.covers => v3_region(state, region) ]),
    v3_set([ for region in view.resets => v3_region(state, region) ]),
    v3_set(
      [
        for exception in view.raises => v3_exception_symbol(state, exception)
      ],
    ),
    v3_set([ for variable in view.spoils => v3_tyvar_symbol(state, variable) ]),
    v3_program_termination(view.termination),
    v3_bool(view.ghost),
  ])
}

///|
fn v3_ity_substitution(
  state : CanonicalV3State,
  substitution : @mlw.ItySubstitution,
) -> CanonicalValue {
  let view = substitution.view()
  v3_node(b"Ity.ity_subst", [
    v3_map(
      [
        for entry in view.type_variables => {
          (v3_tyvar_symbol(state, entry.0), v3_ity(state, entry.1))
        }
      ],
    ),
    v3_map(
      [
        for entry in view.regions => {
          (v3_region(state, entry.0), v3_ity(state, entry.1))
        }
      ],
    ),
  ])
}

///|
fn v3_cty_bound_symbols(
  variables : ArrayView[@mlw.PVariable],
) -> Array[@logic.VSymbol] {
  [
    for variable in variables => variable.view().pure_symbol
  ]
}

///|
fn v3_append_cty_program_variable(
  variables : Array[@mlw.PVariable],
  variable : @mlw.PVariable,
) -> Unit {
  if !variables.any(existing => existing == variable) {
    variables.push(variable)
  }
}

///|
fn v3_cty_program_variables(view : @mlw.CtyView) -> Array[@mlw.PVariable] {
  let variables : Array[@mlw.PVariable] = []
  for variable in view.arguments {
    v3_append_cty_program_variable(variables, variable)
  }
  let reads = view.effect.view().reads.to_owned()
  reads.sort_by((left, right) => {
    left.semantic_id().local_id().compare(right.semantic_id().local_id())
  })
  for variable in reads {
    v3_append_cty_program_variable(variables, variable)
  }
  let oldies = view.oldies.to_owned()
  oldies.sort_by((left, right) => {
    left.view().snapshot
    .semantic_id()
    .local_id()
    .compare(right.view().snapshot.semantic_id().local_id())
  })
  for oldie in oldies {
    let oldie = oldie.view()
    v3_append_cty_program_variable(variables, oldie.snapshot)
    v3_append_cty_program_variable(variables, oldie.original)
  }
  variables
}

///|
fn v3_cty(state : CanonicalV3State, cty : @mlw.Cty) -> CanonicalValue {
  let (index, position) = state.reserve(V3ComputationType)
  let view = cty.view()
  let bound_program = v3_cty_program_variables(view)
  let bound_pure = v3_cty_bound_symbols(bound_program)
  state.fill(
    V3ComputationType,
    index,
    position,
    v3_node(b"Ity.cty", [
      v3_sequence(
        [
          for argument in view.arguments => {
            v3_program_binder(state, bound_program, argument)
          }
        ],
      ),
      v3_sequence(
        [
          for precondition in view.preconditions => {
            v3_term(state, bound_pure, precondition)
          }
        ],
      ),
      v3_sequence(
        [
          for postcondition in view.postconditions => {
            let post = postcondition.view()
            v3_product([
              v3_ty(state, post.result.ty()),
              v3_term(
                state,
                v3_extend_bound_variables(bound_pure, [post.result]),
                post.formula,
              ),
            ])
          }
        ],
      ),
      v3_map(
        [
          for exceptional in view.exceptional_postconditions => {
            let exceptional_view = exceptional.view()
            (
              v3_exception_symbol(state, exceptional_view.exception),
              v3_sequence(
                [
                  for postcondition in exceptional_view.postconditions => {
                    let post = postcondition.view()
                    v3_product([
                      v3_ty(state, post.result.ty()),
                      v3_term(
                        state,
                        v3_extend_bound_variables(bound_pure, [post.result]),
                        post.formula,
                      ),
                    ])
                  }
                ],
              ),
            )
          }
        ],
      ),
      v3_map(
        [
          for oldie in view.oldies => {
            let oldie_view = oldie.view()
            (
              v3_program_variable_reference(
                state,
                bound_program,
                oldie_view.snapshot,
              ),
              v3_program_variable_reference(
                state,
                bound_program,
                oldie_view.original,
              ),
            )
          }
        ],
      ),
      v3_effect(state, bound_program, view.effect),
      v3_ity(state, view.result),
      v3_program_mask(view.mask),
      v3_ity_substitution(state, view.freeze),
    ]),
  )
  v3_reference(V3ComputationType, index)
}

///|
fn v3_routine_logic(
  state : CanonicalV3State,
  logic : @mlw.RoutineLogic,
) -> CanonicalValue {
  match logic {
    RLnone => v3_node(b"Expr.rs_logic.RLnone", [v3_unit()])
    RLpv(variable) =>
      v3_node(b"Expr.rs_logic.RLpv", [v3_pvariable(state, variable)])
    RLls(symbol) => v3_node(b"Expr.rs_logic.RLls", [v3_lsymbol(state, symbol)])
    RLlemma => v3_node(b"Expr.rs_logic.RLlemma", [v3_unit()])
  }
}

///|
fn v3_routine_symbol(
  state : CanonicalV3State,
  symbol : @mlw.RoutineSymbol,
) -> CanonicalValue {
  let kind = V3RoutineSymbol
  let view = symbol.view()
  match state.semantic_index(kind, view.id) {
    Some(index) => v3_reference(kind, index)
    None => {
      let (index, position) = state.reserve(kind)
      state.remember_semantic_index(kind, view.id, index)
      let identifier_id = match view.logic {
        RLls(logic) if view.origin == logic.view().origin => logic.semantic_id()
        RLpv(variable) if view.origin ==
          variable.view().pure_symbol.view().origin =>
          variable.view().pure_symbol.semantic_id()
        RLnone | RLlemma | RLls(_) | RLpv(_) => view.id
      }
      state.fill(
        kind,
        index,
        position,
        v3_product([
          v3_node(b"Expr.rsymbol", [
            v3_identifier(state, identifier_id, view.origin),
            v3_cty(state, view.cty),
            v3_routine_logic(state, view.logic),
            match view.field {
              None => v3_none()
              Some(field) => v3_some(v3_pvariable(state, field))
            },
          ]),
          v3_origin(state, view.origin),
        ]),
      )
      v3_reference(kind, index)
    }
  }
}

///|
pub fn encode_ity(ity : @mlw.Ity) -> CanonicalJson {
  let state = CanonicalV3State::new()
  state.finish([v3_ity(state, ity)])
}

///|
pub fn encode_program_type_symbol(
  symbol : @mlw.ProgramTypeSymbol,
) -> CanonicalJson {
  let state = CanonicalV3State::new()
  state.finish([v3_program_type_symbol(state, symbol)])
}

///|
pub fn encode_routine_symbol(symbol : @mlw.RoutineSymbol) -> CanonicalJson {
  let state = CanonicalV3State::new()
  state.finish([v3_routine_symbol(state, symbol)])
}
