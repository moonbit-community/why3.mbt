// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn canonical_program_type_argument_flag(
  flag : @mlw.ProgramTypeArgumentFlag,
) -> CanonicalValue {
  canonical_array([
    canonical_bool(flag.frozen),
    canonical_bool(flag.exposed),
    canonical_bool(flag.liable),
    canonical_bool(flag.fixed),
    canonical_bool(flag.visible),
  ])
}

///|
fn canonical_program_type_flags(
  flags : @mlw.ProgramTypeFlags,
) -> CanonicalValue {
  canonical_array([
    canonical_bool(flags.nonfree),
    canonical_bool(flags.private_),
    canonical_bool(flags.mutable_),
    canonical_bool(flags.fragile),
    canonical_array(
      [
        for flag in flags.argument_flags => {
          canonical_program_type_argument_flag(flag)
        }
      ],
    ),
    canonical_array(
      [
        for flag in flags.region_flags => {
          canonical_program_type_argument_flag(flag)
        }
      ],
    ),
  ])
}

///|
fn canonical_ity(
  numbering : GlobalSymbolNumbering,
  ity : @mlw.Ity,
) -> CanonicalValue raise {
  match ity.view() {
    ItyVar(variable) =>
      canonical_array([
        canonical_text(b"ItyVar"),
        canonical_type_identity(numbering, variable.semantic_id()),
      ])
    ItyApp(symbol, arguments) =>
      canonical_array([
        canonical_text(b"ItyApp"),
        canonical_program_identity(numbering, symbol.semantic_id()),
        canonical_array(
          [
            for argument in arguments => canonical_ity(numbering, argument)
          ],
        ),
        canonical_array([]),
        canonical_ty(numbering, ity.to_ty(None)),
      ])
  }
}

///|
fn canonical_program_type_definition(
  numbering : GlobalSymbolNumbering,
  definition : @mlw.ProgramTypeDefinition,
) -> CanonicalValue raise {
  match definition {
    ProgramNoDef => canonical_array([canonical_text(b"TypeDefinition.NoDef")])
    ProgramAlias(target) =>
      canonical_array([
        canonical_text(b"TypeDefinition.Alias"),
        canonical_ity(numbering, target),
      ])
    ProgramRange(lower, upper) =>
      canonical_array([
        canonical_text(b"TypeDefinition.Range"),
        Decimal(lower),
        Decimal(upper),
      ])
    ProgramFloat(exponent_digits, significand_digits) =>
      canonical_array([
        canonical_text(b"TypeDefinition.Float"),
        Signed(exponent_digits.to_int64()),
        Signed(significand_digits.to_int64()),
      ])
  }
}

///|
fn canonical_program_type_symbol(
  numbering : GlobalSymbolNumbering,
  symbol : @mlw.ProgramTypeSymbol,
) -> CanonicalValue raise {
  let view = symbol.view()
  canonical_array([
    canonical_text(b"ProgramTypeSymbol"),
    canonical_program_identity(numbering, view.id),
    canonical_type_identity(numbering, view.logic_type.semantic_id()),
    canonical_origin(view.origin),
    canonical_program_type_flags(view.flags),
    canonical_program_type_definition(numbering, view.definition),
  ])
}

///|
fn canonical_program_binder(
  numbering : GlobalSymbolNumbering,
  variable : @mlw.PVariable,
) -> CanonicalValue raise {
  let view = variable.view()
  canonical_array([
    canonical_ity(numbering, view.ity),
    canonical_bool(view.ghost),
  ])
}

///|
fn canonical_program_mask(mask : @mlw.ProgramMask) -> CanonicalValue {
  canonical_text(
    match mask {
      Visible => b"Visible"
      Ghost => b"Ghost"
    },
  )
}

///|
fn canonical_effect(
  numbering : GlobalSymbolNumbering,
  effect : @mlw.Effect,
) -> CanonicalValue {
  let view = effect.view()
  canonical_array([
    canonical_text(b"Effect"),
    canonical_array(
      [
        for variable in view.reads => {
          canonical_program_identity(numbering, variable.semantic_id())
        }
      ],
    ),
    canonical_array([]),
    canonical_array([]),
    canonical_array([]),
    canonical_array([]),
    canonical_array([]),
    canonical_array([]),
    canonical_text(b"Total"),
    canonical_bool(view.ghost),
  ])
}

///|
fn cty_bound_variables(
  variables : ArrayView[@mlw.PVariable],
) -> Array[@logic.VSymbol] {
  [
    for variable in variables => variable.view().pure_symbol
  ]
}

///|
fn canonical_cty(
  numbering : GlobalSymbolNumbering,
  cty : @mlw.Cty,
) -> CanonicalValue raise {
  let view = cty.view()
  let bound = cty_bound_variables(view.program_variables)
  let postconditions : Array[CanonicalValue] = []
  for postcondition in view.postconditions {
    let post = postcondition.view()
    let post_bound = extend_bound_variables(bound, [post.result])
    postconditions.push(
      canonical_array([
        canonical_ty(numbering, post.result.ty()),
        canonical_term(numbering, post_bound, post.formula),
      ]),
    )
  }
  canonical_array([
    canonical_text(b"Cty"),
    canonical_array(
      [
        for argument in view.arguments => {
          canonical_program_binder(numbering, argument)
        }
      ],
    ),
    canonical_array(
      [
        for precondition in view.preconditions => {
          canonical_term(numbering, bound, precondition)
        }
      ],
    ),
    canonical_array(postconditions),
    canonical_array([]),
    canonical_array([]),
    canonical_effect(numbering, view.effect),
    canonical_ity(numbering, view.result),
    canonical_program_mask(view.mask),
    canonical_array([]),
  ])
}

///|
fn canonical_routine_logic(
  numbering : GlobalSymbolNumbering,
  logic : @mlw.RoutineLogic,
) -> CanonicalValue {
  match logic {
    RLnone => canonical_array([canonical_text(b"none")])
    RLls(symbol) =>
      canonical_array([
        canonical_text(b"some"),
        canonical_logic_identity(numbering, symbol.semantic_id()),
      ])
  }
}

///|
fn canonical_program_variable_option(
  numbering : GlobalSymbolNumbering,
  field : @mlw.PVariable?,
) -> CanonicalValue {
  match field {
    None => canonical_array([canonical_text(b"none")])
    Some(value) =>
      canonical_array([
        canonical_text(b"some"),
        canonical_program_identity(numbering, value.semantic_id()),
      ])
  }
}

///|
fn canonical_routine_symbol(
  numbering : GlobalSymbolNumbering,
  symbol : @mlw.RoutineSymbol,
) -> CanonicalValue raise {
  let view = symbol.view()
  canonical_array([
    canonical_text(b"RoutineSymbol"),
    canonical_program_identity(numbering, view.id),
    canonical_hex(view.name),
    canonical_origin(view.origin),
    canonical_cty(numbering, view.cty),
    canonical_routine_logic(numbering, view.logic),
    canonical_program_variable_option(numbering, view.field),
  ])
}

///|
fn bound_program_variable_index(
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
fn canonical_program_variable_reference(
  numbering : GlobalSymbolNumbering,
  bound : ArrayView[@mlw.PVariable],
  variable : @mlw.PVariable,
) -> CanonicalValue {
  match bound_program_variable_index(bound, variable) {
    Some(index) => canonical_array([canonical_text(b"bound"), Unsigned(index)])
    None =>
      canonical_array([
        canonical_text(b"global"),
        canonical_program_identity(numbering, variable.semantic_id()),
      ])
  }
}

///|
fn extend_bound_program_variables(
  bound : ArrayView[@mlw.PVariable],
  variables : ArrayView[@mlw.PVariable],
) -> Array[@mlw.PVariable] {
  let extended = bound.to_owned()
  for variable in variables {
    extended.push(variable)
  }
  extended
}

///|
fn canonical_expr_node(
  numbering : GlobalSymbolNumbering,
  bound : ArrayView[@mlw.PVariable],
  expression : @mlw.Expr,
) -> CanonicalValue raise {
  match expression.view() {
    Evar(variable, ity) =>
      canonical_array([
        canonical_text(b"Evar"),
        canonical_program_variable_reference(numbering, bound, variable),
        canonical_ity(numbering, ity),
      ])
    Econst(constant, ity) =>
      canonical_array([
        canonical_text(b"Econst"),
        canonical_constant(constant),
        canonical_ity(numbering, ity),
      ])
    EpureApp(symbol, arguments, ity) =>
      canonical_array([
        canonical_text(b"EpureApp"),
        canonical_logic_identity(numbering, symbol.semantic_id()),
        canonical_array(
          [
            for argument in arguments => {
              canonical_program_variable_reference(numbering, bound, argument)
            }
          ],
        ),
        canonical_ity(numbering, ity),
      ])
    EroutineCall(symbol, arguments, ity) =>
      canonical_array([
        canonical_text(b"EroutineCall"),
        canonical_program_identity(numbering, symbol.semantic_id()),
        canonical_array(
          [
            for argument in arguments => {
              canonical_program_variable_reference(numbering, bound, argument)
            }
          ],
        ),
        canonical_ity(numbering, ity),
      ])
    Elet(binder, value, body, ity) => {
      let body_bound = extend_bound_program_variables(bound, [binder])
      canonical_array([
        canonical_text(b"Elet"),
        canonical_program_binder(numbering, binder),
        canonical_expr(numbering, bound, value),
        canonical_expr(numbering, body_bound, body),
        canonical_ity(numbering, ity),
      ])
    }
    Eif(condition, consequent, alternative, ity) =>
      canonical_array([
        canonical_text(b"Eif"),
        canonical_expr(numbering, bound, condition),
        canonical_expr(numbering, bound, consequent),
        canonical_expr(numbering, bound, alternative),
        canonical_ity(numbering, ity),
      ])
    Eassert(formula) =>
      canonical_array([
        canonical_text(b"Eassert"),
        canonical_term(
          numbering,
          [
            for variable in bound => variable.view().pure_symbol
          ],
          formula,
        ),
      ])
    Eassume(formula) =>
      canonical_array([
        canonical_text(b"Eassume"),
        canonical_term(
          numbering,
          [
            for variable in bound => variable.view().pure_symbol
          ],
          formula,
        ),
      ])
  }
}

///|
fn canonical_expr(
  numbering : GlobalSymbolNumbering,
  bound : ArrayView[@mlw.PVariable],
  expression : @mlw.Expr,
) -> CanonicalValue raise {
  canonical_array([
    canonical_text(b"ExprDecorated"),
    canonical_expr_node(numbering, bound, expression),
    canonical_origin(expression.origin()),
    canonical_attributes(expression.attributes()),
    canonical_effect(numbering, expression.effect()),
    canonical_program_mask(expression.mask()),
  ])
}

///|
fn canonical_program_type_declaration(
  numbering : GlobalSymbolNumbering,
  declaration : @mlw.ProgramTypeDeclaration,
) -> CanonicalValue raise {
  let view = declaration.view()
  canonical_array([
    canonical_program_type_symbol(numbering, view.symbol),
    canonical_array(
      [
        for field in view.fields => {
          canonical_program_identity(numbering, field.semantic_id())
        }
      ],
    ),
    canonical_array(
      [
        for constructor_value in view.constructors => {
          canonical_program_identity(numbering, constructor_value.semantic_id())
        }
      ],
    ),
    canonical_array(
      [
        for invariant in view.invariants => {
          canonical_term(numbering, [], invariant)
        }
      ],
    ),
  ])
}

///|
fn canonical_program_declaration(
  numbering : GlobalSymbolNumbering,
  declaration : @mlw.ProgramDeclaration,
) -> CanonicalValue raise {
  let pure_declarations = match declaration {
    PDtype(_, pure) | PDpure(pure) | PDlet(_, _, pure) => pure
  }
  let node = match declaration {
    PDtype(declarations, _) =>
      canonical_array([
        canonical_text(b"Pdecl.PDtype"),
        canonical_array(
          [
            for entry in declarations => {
              canonical_program_type_declaration(numbering, entry)
            }
          ],
        ),
      ])
    PDpure(_) => canonical_array([canonical_text(b"Pdecl.PDpure")])
    PDlet(symbol, computation, _) => {
      let (kind, projection) = match computation {
        Cany(cty) => (b"Cany", canonical_cty(numbering, cty))
        Cfun(cty, None) => (b"Cfun", canonical_cty(numbering, cty))
        Cfun(cty, Some(body)) => {
          let bound = cty.view().program_variables.to_owned()
          (
            b"Cfun",
            canonical_array([
              canonical_text(b"CfunProjection"),
              canonical_cty(numbering, cty),
              canonical_expr(numbering, bound, body),
            ]),
          )
        }
      }
      canonical_array([
        canonical_text(b"Pdecl.PDlet"),
        canonical_routine_symbol(numbering, symbol),
        canonical_text(kind),
        projection,
      ])
    }
  }
  canonical_array([
    canonical_text(b"Pdecl"),
    canonical_array([canonical_text(b"none")]),
    canonical_array(
      [
        for pure in pure_declarations => canonical_decl(numbering, pure)
      ],
    ),
    canonical_array([]),
    node,
  ])
}

///|
fn canonical_proposition_kind(kind : @logic.PropositionKind) -> CanonicalValue {
  canonical_text(
    match kind {
      Paxiom => b"Paxiom"
      Plemma => b"Plemma"
      Pgoal => b"Pgoal"
    },
  )
}

///|
fn canonical_program_clone_witness(
  numbering : GlobalSymbolNumbering,
  witness : @mlw.ProgramCloneWitness,
) -> CanonicalValue raise {
  let view = witness.view()
  canonical_array([
    canonical_theory_key(view.source),
    canonical_semantic_map(
      [
        for entry in view.type_instantiations => {
          (
            canonical_type_identity(numbering, entry.0.semantic_id()),
            canonical_ity(numbering, entry.1),
          )
        }
      ],
    ),
    canonical_semantic_map(
      [
        for entry in view.program_type_instantiations => {
          (
            canonical_type_identity(numbering, entry.0.semantic_id()),
            canonical_program_identity(numbering, entry.1.semantic_id()),
          )
        }
      ],
    ),
    canonical_clone_logic_instantiations(numbering, view.logic_instantiations),
    canonical_clone_proposition_instantiations(
      numbering,
      view.proposition_instantiations,
    ),
    canonical_semantic_map(
      [
        for entry in view.proposition_kinds => {
          (
            canonical_proposition_identity(numbering, entry.0.semantic_id()),
            canonical_proposition_kind(entry.1),
          )
        }
      ],
    ),
    canonical_semantic_map(
      [
        for entry in view.program_variable_instantiations => {
          (
            canonical_program_identity(numbering, entry.0.semantic_id()),
            canonical_program_identity(numbering, entry.1.semantic_id()),
          )
        }
      ],
    ),
    canonical_semantic_map(
      [
        for entry in view.routine_instantiations => {
          (
            canonical_program_identity(numbering, entry.0.semantic_id()),
            canonical_program_identity(numbering, entry.1.semantic_id()),
          )
        }
      ],
    ),
    canonical_proposition_kind(view.default_proposition_kind),
  ])
}

///|
fn canonical_program_namespace(
  numbering : GlobalSymbolNumbering,
  namespace_value : @mlw.ProgramNamespace,
) -> CanonicalValue {
  let view = namespace_value.view()
  canonical_array([
    canonical_text(b"ProgramNamespace"),
    canonical_semantic_map(
      [
        for entry in view.types => {
          (
            canonical_hex(entry.0),
            canonical_program_identity(numbering, entry.1.semantic_id()),
          )
        }
      ],
    ),
    canonical_semantic_map(
      [
        for entry in view.routines => {
          (
            canonical_hex(entry.0),
            canonical_program_identity(numbering, entry.1.semantic_id()),
          )
        }
      ],
    ),
    canonical_array([]),
    canonical_semantic_map(
      [
        for entry in view.subspaces => {
          (
            canonical_hex(entry.0),
            canonical_program_namespace(numbering, entry.1),
          )
        }
      ],
    ),
  ])
}

///|
fn canonical_pmodule_key(key : @theory.TheoryKey) -> CanonicalValue {
  let view = key.view()
  canonical_array([
    canonical_text(b"PmoduleKey"),
    canonical_array([ for segment in view.path => canonical_hex(segment) ]),
    canonical_hex(view.name),
  ])
}

///|
fn append_canonical_module_item(
  output : Array[CanonicalValue],
  numbering : GlobalSymbolNumbering,
  item : @mlw.ModuleItem,
) -> Unit raise {
  match item {
    Udecl(PDpure(declarations)) =>
      for declaration in declarations {
        output.push(
          canonical_array([
            canonical_text(b"PmoduleItem.PureDecl"),
            canonical_decl(numbering, declaration),
          ]),
        )
      }
    Udecl(declaration) =>
      output.push(
        canonical_array([
          canonical_text(b"PmoduleItem.ProgramDecl"),
          canonical_program_declaration(numbering, declaration),
        ]),
      )
    Uuse(source) =>
      output.push(
        canonical_array([
          canonical_text(b"PmoduleItem.Use"),
          canonical_pmodule_key(source),
        ]),
      )
    Uclone(witness) =>
      output.push(
        canonical_array([
          canonical_text(b"PmoduleItem.Clone"),
          canonical_program_clone_witness(numbering, witness),
        ]),
      )
    Umeta(meta) =>
      output.push(
        canonical_array([
          canonical_text(b"PmoduleItem.Meta"),
          canonical_meta(numbering, meta),
        ]),
      )
  }
}

///|
pub fn encode_ity(ity : @mlw.Ity) -> CanonicalJson raise {
  encode_canonical_value(canonical_ity(GlobalSymbolNumbering::new(), ity))
}

///|
pub fn encode_program_type_symbol(
  symbol : @mlw.ProgramTypeSymbol,
) -> CanonicalJson raise {
  encode_canonical_value(
    canonical_program_type_symbol(GlobalSymbolNumbering::new(), symbol),
  )
}

///|
pub fn encode_routine_symbol(
  symbol : @mlw.RoutineSymbol,
) -> CanonicalJson raise {
  encode_canonical_value(
    canonical_routine_symbol(GlobalSymbolNumbering::new(), symbol),
  )
}

///|
pub fn encode_expr(expression : @mlw.Expr) -> CanonicalJson raise {
  encode_canonical_value(
    canonical_expr(GlobalSymbolNumbering::new(), [], expression),
  )
}

///|
pub fn encode_pmodule(pmodule : @mlw.Pmodule) -> CanonicalJson raise {
  let numbering = GlobalSymbolNumbering::new()
  let view = pmodule.view()
  let items : Array[CanonicalValue] = []
  for item in view.items {
    append_canonical_module_item(items, numbering, item)
  }
  encode_canonical_value(
    canonical_array([
      canonical_text(b"Pmodule"),
      canonical_pmodule_key(view.key),
      canonical_theory(numbering, view.pure_theory),
      canonical_array(items),
      canonical_program_namespace(numbering, view.export_namespace),
    ]),
  )
}
