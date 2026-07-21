// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn canonical_logic_identity(
  numbering : GlobalSymbolNumbering,
  id : @identity.SemanticId,
) -> CanonicalValue {
  canonical_array([
    canonical_text(GlobalSymbolKind::Logic.canonical_name()),
    Unsigned(numbering.encounter(Logic, id)),
  ])
}

///|
fn canonical_program_identity(
  numbering : GlobalSymbolNumbering,
  id : @identity.SemanticId,
) -> CanonicalValue {
  canonical_array([
    canonical_text(GlobalSymbolKind::Program.canonical_name()),
    Unsigned(numbering.encounter(Program, id)),
  ])
}

///|
fn canonical_proposition_identity(
  numbering : GlobalSymbolNumbering,
  id : @identity.SemanticId,
) -> CanonicalValue {
  canonical_array([
    canonical_text(GlobalSymbolKind::Proposition.canonical_name()),
    Unsigned(numbering.encounter(Proposition, id)),
  ])
}

///|
fn canonical_ty_option(
  numbering : GlobalSymbolNumbering,
  ty : @logic.Ty?,
) -> CanonicalValue {
  match ty {
    None => canonical_array([canonical_text(b"none")])
    Some(value) =>
      canonical_array([canonical_text(b"some"), canonical_ty(numbering, value)])
  }
}

///|
fn canonical_origin_option(origin : @identity.Origin?) -> CanonicalValue {
  match origin {
    None => canonical_array([canonical_text(b"none")])
    Some(value) =>
      canonical_array([canonical_text(b"some"), canonical_origin(value)])
  }
}

///|
fn canonical_vsymbol(
  numbering : GlobalSymbolNumbering,
  symbol : @logic.VSymbol,
) -> CanonicalValue {
  let view = symbol.view()
  canonical_array([
    canonical_text(b"VSymbol"),
    canonical_program_identity(numbering, view.id),
    canonical_hex(view.name),
    canonical_origin(view.origin),
    canonical_ty(numbering, view.ty),
  ])
}

///|
fn canonical_lsymbol(
  numbering : GlobalSymbolNumbering,
  symbol : @logic.LSymbol,
) -> CanonicalValue {
  let view = symbol.view()
  canonical_array([
    canonical_text(b"LSymbol"),
    canonical_logic_identity(numbering, view.id),
    canonical_hex(view.name),
    canonical_origin(view.origin),
    canonical_array(
      [
        for parameter in view.type_parameters => {
          canonical_type_identity(numbering, parameter.semantic_id())
        }
      ],
    ),
    canonical_array(
      [
        for argument in view.argument_types => canonical_ty(numbering, argument)
      ],
    ),
    canonical_ty_option(numbering, view.result_type),
  ])
}

///|
fn canonical_prsymbol(
  numbering : GlobalSymbolNumbering,
  symbol : @logic.PrSymbol,
) -> CanonicalValue {
  let view = symbol.view()
  canonical_array([
    canonical_text(b"PrSymbol"),
    canonical_proposition_identity(numbering, view.id),
    canonical_hex(view.name),
    canonical_origin(view.origin),
  ])
}

///|
pub fn encode_vsymbol(symbol : @logic.VSymbol) -> CanonicalJson {
  encode_canonical_value(
    canonical_vsymbol(GlobalSymbolNumbering::new(), symbol),
  )
}

///|
pub fn encode_lsymbol(symbol : @logic.LSymbol) -> CanonicalJson {
  encode_canonical_value(
    canonical_lsymbol(GlobalSymbolNumbering::new(), symbol),
  )
}

///|
pub fn encode_prsymbol(symbol : @logic.PrSymbol) -> CanonicalJson {
  encode_canonical_value(
    canonical_prsymbol(GlobalSymbolNumbering::new(), symbol),
  )
}

///|
fn canonical_integer_literal_kind(
  kind : @logic.IntegerLiteralKind,
) -> CanonicalValue {
  canonical_text(
    match kind {
      IntegerUnknown => b"ILitUnk"
      IntegerDecimal => b"ILitDec"
      IntegerHexadecimal => b"ILitHex"
      IntegerOctal => b"ILitOct"
      IntegerBinary => b"ILitBin"
    },
  )
}

///|
fn canonical_real_literal_kind(kind : @logic.RealLiteralKind) -> CanonicalValue {
  match kind {
    RealUnknown => canonical_array([canonical_text(b"RLitUnk")])
    RealDecimal(exponent) =>
      canonical_array([canonical_text(b"RLitDec"), Signed(exponent)])
    RealHexadecimal(exponent) =>
      canonical_array([canonical_text(b"RLitHex"), Signed(exponent)])
  }
}

///|
fn canonical_constant(constant : @logic.Constant) -> CanonicalValue {
  match constant.view() {
    IntegerConstant(kind, value) =>
      canonical_array([
        canonical_text(b"ConstantInt"),
        canonical_integer_literal_kind(kind),
        Decimal(value),
      ])
    RealConstant(kind, value) =>
      canonical_array([
        canonical_text(b"ConstantReal"),
        canonical_real_literal_kind(kind),
        Decimal(value.significand()),
        Decimal(value.pow2()),
        Decimal(value.pow5()),
      ])
    StringConstant(value) =>
      canonical_array([canonical_text(b"ConstantString"), canonical_hex(value)])
  }
}

///|
pub fn encode_constant(constant : @logic.Constant) -> CanonicalJson {
  encode_canonical_value(canonical_constant(constant))
}

///|
fn bound_variable_index(
  bound : ArrayView[@logic.VSymbol],
  variable : @logic.VSymbol,
) -> UInt? {
  let mut position = bound.length() - 1
  let mut distance = 0
  while position >= 0 {
    if bound[position] == variable {
      return Some(distance.reinterpret_as_uint())
    }
    position = position - 1
    distance = distance + 1
  }
  None
}

///|
fn extend_bound_variables(
  bound : ArrayView[@logic.VSymbol],
  variables : ArrayView[@logic.VSymbol],
) -> Array[@logic.VSymbol] {
  let extended = bound.to_owned()
  for variable in variables {
    extended.push(variable)
  }
  extended
}

///|
fn canonical_variable_reference(
  numbering : GlobalSymbolNumbering,
  bound : ArrayView[@logic.VSymbol],
  variable : @logic.VSymbol,
) -> CanonicalValue {
  match bound_variable_index(bound, variable) {
    Some(index) => canonical_array([canonical_text(b"bound"), Unsigned(index)])
    None =>
      canonical_array([
        canonical_text(b"global"),
        canonical_vsymbol(numbering, variable),
      ])
  }
}

///|
fn canonical_pattern(
  numbering : GlobalSymbolNumbering,
  pattern : @logic.Pattern,
) -> CanonicalValue {
  match pattern.view() {
    Pwild(ty) =>
      canonical_array([canonical_text(b"Pwild"), canonical_ty(numbering, ty)])
    Pvar(variable) =>
      canonical_array([
        canonical_text(b"Pvar"),
        canonical_ty(numbering, variable.ty()),
      ])
    Papp(symbol, arguments, ty) =>
      canonical_array([
        canonical_text(b"Papp"),
        canonical_logic_identity(numbering, symbol.semantic_id()),
        canonical_array(
          [
            for argument in arguments => canonical_pattern(numbering, argument)
          ],
        ),
        canonical_ty(numbering, ty),
      ])
    Por(left, right, ty) =>
      canonical_array([
        canonical_text(b"Por"),
        canonical_pattern(numbering, left),
        canonical_pattern(numbering, right),
        canonical_ty(numbering, ty),
      ])
    Pas(inner, variable, _) =>
      canonical_array([
        canonical_text(b"Pas"),
        canonical_pattern(numbering, inner),
        canonical_ty(numbering, variable.ty()),
      ])
  }
}

///|
fn canonical_term_instantiation(
  numbering : GlobalSymbolNumbering,
  entries : ArrayView[(@logic.TyVarSymbol, @logic.Ty)],
) -> CanonicalValue {
  canonical_array(
    [
      for entry in entries => {
        canonical_array([
          canonical_type_identity(numbering, entry.0.semantic_id()),
          canonical_ty(numbering, entry.1),
        ])
      }
    ],
  )
}

///|
fn canonical_term_node(
  numbering : GlobalSymbolNumbering,
  bound : ArrayView[@logic.VSymbol],
  term : @logic.Term,
) -> CanonicalValue {
  match term.view() {
    Tvar(variable) =>
      canonical_array([
        canonical_text(b"Tvar"),
        canonical_variable_reference(numbering, bound, variable),
      ])
    Tconst(constant) => {
      guard term.ty() is Some(result_type) else {
        abort("validated constant term lost its result type")
      }
      canonical_array([
        canonical_text(b"Tconst"),
        canonical_constant(constant),
        canonical_ty(numbering, result_type),
      ])
    }
    Tapp(symbol, instantiation, arguments) =>
      canonical_array([
        canonical_text(b"Tapp"),
        canonical_logic_identity(numbering, symbol.semantic_id()),
        canonical_term_instantiation(numbering, instantiation),
        canonical_array(
          [
            for argument in arguments => {
              canonical_term(numbering, bound, argument)
            }
          ],
        ),
        canonical_ty_option(numbering, term.ty()),
      ])
    Tif(condition, then_branch, else_branch) =>
      canonical_array([
        canonical_text(b"Tif"),
        canonical_term(numbering, bound, condition),
        canonical_term(numbering, bound, then_branch),
        canonical_term(numbering, bound, else_branch),
        canonical_ty_option(numbering, term.ty()),
      ])
    Tlet(variable, value, body) => {
      let body_bound = extend_bound_variables(bound, [variable])
      canonical_array([
        canonical_text(b"Tlet"),
        canonical_term(numbering, bound, value),
        canonical_ty(numbering, variable.ty()),
        canonical_term(numbering, body_bound, body),
        canonical_ty_option(numbering, term.ty()),
      ])
    }
    Tcase(scrutinee, branches) => {
      let encoded_branches : Array[CanonicalValue] = []
      for branch in branches {
        let view = branch.view()
        let body_bound = extend_bound_variables(
          bound,
          view.pattern.bound_variables(),
        )
        encoded_branches.push(
          canonical_array([
            canonical_pattern(numbering, view.pattern),
            canonical_term(numbering, body_bound, view.body),
          ]),
        )
      }
      canonical_array([
        canonical_text(b"Tcase"),
        canonical_term(numbering, bound, scrutinee),
        canonical_array(encoded_branches),
        canonical_ty_option(numbering, term.ty()),
      ])
    }
    Teps(variable, body) => {
      let body_bound = extend_bound_variables(bound, [variable])
      guard term.ty() is Some(result_type) else {
        abort("validated epsilon term lost its result type")
      }
      canonical_array([
        canonical_text(b"Teps"),
        canonical_ty(numbering, variable.ty()),
        canonical_term(numbering, body_bound, body),
        canonical_ty(numbering, result_type),
      ])
    }
    Tquant(quantifier, binders, triggers, body) => {
      let body_bound = extend_bound_variables(bound, binders)
      let encoded_triggers : Array[CanonicalValue] = []
      for group in triggers {
        encoded_triggers.push(
          canonical_array(
            [
              for trigger in group => {
                canonical_term(numbering, body_bound, trigger)
              }
            ],
          ),
        )
      }
      canonical_array([
        canonical_text(
          match quantifier {
            ForallQuantifier => b"Tquant.Forall"
            ExistsQuantifier => b"Tquant.Exists"
          },
        ),
        canonical_array(
          [
            for binder in binders => canonical_ty(numbering, binder.ty())
          ],
        ),
        canonical_array(encoded_triggers),
        canonical_term(numbering, body_bound, body),
      ])
    }
    Tbinop(operator, left, right) =>
      canonical_array([
        canonical_text(
          match operator {
            And => b"Tbinop.And"
            Or => b"Tbinop.Or"
            Implies => b"Tbinop.Implies"
            Iff => b"Tbinop.Iff"
          },
        ),
        canonical_term(numbering, bound, left),
        canonical_term(numbering, bound, right),
      ])
    Tnot(inner) =>
      canonical_array([
        canonical_text(b"Tnot"),
        canonical_term(numbering, bound, inner),
      ])
    Ttrue => canonical_array([canonical_text(b"Ttrue")])
    Tfalse => canonical_array([canonical_text(b"Tfalse")])
  }
}

///|
fn canonical_term(
  numbering : GlobalSymbolNumbering,
  bound : ArrayView[@logic.VSymbol],
  term : @logic.Term,
) -> CanonicalValue {
  let node = canonical_term_node(numbering, bound, term)
  if term.origin() is None && term.attributes().is_empty() {
    node
  } else {
    canonical_array([
      canonical_text(b"TermDecorated"),
      node,
      canonical_origin_option(term.origin()),
      canonical_attributes(term.attributes()),
    ])
  }
}

///|
pub fn encode_term(term : @logic.Term) -> CanonicalJson {
  encode_canonical_value(canonical_term(GlobalSymbolNumbering::new(), [], term))
}

///|
fn canonical_logic_definition(
  numbering : GlobalSymbolNumbering,
  definition : @logic.LogicDefinition,
) -> CanonicalValue {
  let view = definition.view()
  let bound = extend_bound_variables([], view.parameters)
  canonical_array([
    canonical_lsymbol(numbering, view.symbol),
    canonical_array(
      [
        for parameter in view.parameters => {
          canonical_ty(numbering, parameter.ty())
        }
      ],
    ),
    canonical_term(numbering, bound, view.body),
  ])
}

///|
fn canonical_data_constructor(
  numbering : GlobalSymbolNumbering,
  data_constructor : @logic.DataConstructor,
) -> CanonicalValue {
  let view = data_constructor.view()
  canonical_array([
    canonical_lsymbol(numbering, view.symbol),
    canonical_array(
      [
        for projection in view.projections => {
          match projection {
            None => canonical_array([canonical_text(b"none")])
            Some(symbol) =>
              canonical_array([
                canonical_text(b"some"),
                canonical_lsymbol(numbering, symbol),
              ])
          }
        }
      ],
    ),
  ])
}

///|
fn canonical_data_declaration(
  numbering : GlobalSymbolNumbering,
  declaration : @logic.DataDeclaration,
) -> CanonicalValue {
  let view = declaration.view()
  canonical_array([
    canonical_type_symbol(numbering, view.type_symbol),
    canonical_array(
      [
        for data_constructor in view.constructors => {
          canonical_data_constructor(numbering, data_constructor)
        }
      ],
    ),
  ])
}

///|
fn canonical_inductive_case(
  numbering : GlobalSymbolNumbering,
  case_ : @logic.InductiveCase,
) -> CanonicalValue {
  let view = case_.view()
  canonical_array([
    canonical_prsymbol(numbering, view.proposition),
    canonical_term(numbering, [], view.formula),
  ])
}

///|
fn canonical_inductive_declaration(
  numbering : GlobalSymbolNumbering,
  declaration : @logic.InductiveDeclaration,
) -> CanonicalValue {
  let view = declaration.view()
  canonical_array([
    canonical_lsymbol(numbering, view.predicate),
    canonical_array(
      [
        for case_ in view.cases => canonical_inductive_case(numbering, case_)
      ],
    ),
  ])
}

///|
fn canonical_decl_dependency(
  numbering : GlobalSymbolNumbering,
  dependency : @logic.DeclDependency,
) -> CanonicalValue {
  match dependency {
    TypeDependency(symbol) => canonical_type_symbol(numbering, symbol)
    LogicDependency(symbol) => canonical_lsymbol(numbering, symbol)
    PropositionDependency(symbol) => canonical_prsymbol(numbering, symbol)
  }
}

///|
fn canonical_decl_node(
  numbering : GlobalSymbolNumbering,
  declaration : @logic.Decl,
) -> CanonicalValue {
  match declaration.view() {
    Dtype(symbols) =>
      canonical_array([
        canonical_text(b"Dtype"),
        canonical_array(
          [
            for symbol in symbols => canonical_type_symbol(numbering, symbol)
          ],
        ),
      ])
    Ddata(declarations) =>
      canonical_array([
        canonical_text(b"Ddata"),
        canonical_array(
          [
            for data_declaration in declarations => {
              canonical_data_declaration(numbering, data_declaration)
            }
          ],
        ),
      ])
    Dparam(symbol) =>
      canonical_array([
        canonical_text(b"Dparam"),
        canonical_lsymbol(numbering, symbol),
      ])
    Dlogic(definitions) =>
      canonical_array([
        canonical_text(b"Dlogic"),
        canonical_array(
          [
            for definition in definitions => {
              canonical_logic_definition(numbering, definition)
            }
          ],
        ),
      ])
    Dind(declarations) =>
      canonical_array([
        canonical_text(b"Dind.Ind"),
        canonical_array(
          [
            for inductive_declaration in declarations => {
              canonical_inductive_declaration(numbering, inductive_declaration)
            }
          ],
        ),
      ])
    Dprop(kind, symbol, formula) =>
      canonical_array([
        canonical_text(
          match kind {
            Paxiom => b"Dprop.Paxiom"
            Plemma => b"Dprop.Plemma"
            Pgoal => b"Dprop.Pgoal"
          },
        ),
        canonical_prsymbol(numbering, symbol),
        canonical_term(numbering, [], formula),
      ])
  }
}

///|
fn canonical_decl(
  numbering : GlobalSymbolNumbering,
  declaration : @logic.Decl,
) -> CanonicalValue {
  canonical_array([
    canonical_text(b"Decl"),
    canonical_origin(declaration.origin()),
    canonical_array(
      [
        for dependency in declaration.dependencies() => {
          canonical_decl_dependency(numbering, dependency)
        }
      ],
    ),
    canonical_decl_node(numbering, declaration),
  ])
}

///|
pub fn encode_decl(declaration : @logic.Decl) -> CanonicalJson {
  encode_canonical_value(
    canonical_decl(GlobalSymbolNumbering::new(), declaration),
  )
}
