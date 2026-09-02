// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn v3_tyvar_symbol(
  state : CanonicalV3State,
  symbol : @logic.TyVarSymbol,
) -> CanonicalValue {
  let kind = V3TypeVariable
  let id = symbol.semantic_id()
  match state.semantic_index(kind, id) {
    Some(index) => v3_reference(kind, index)
    None => {
      let (index, position) = state.reserve(kind)
      state.remember_semantic_index(kind, id, index)
      state.fill(
        kind,
        index,
        position,
        v3_node(b"Ty.tvsymbol", [
          // Type variables are binders. Their spelling, attributes and
          // location are deliberately absent from the semantic graph.
          v3_unit(),
        ]),
      )
      v3_reference(kind, index)
    }
  }
}

///|
fn v3_type_definition(
  state : CanonicalV3State,
  definition : @logic.TypeDefinitionView,
) -> CanonicalValue {
  match definition {
    NoDef => v3_node(b"Ty.type_def.NoDef", [v3_unit()])
    Alias(ty) => v3_node(b"Ty.type_def.Alias", [v3_ty(state, ty)])
    Range(lower, upper) =>
      v3_node(b"Ty.type_def.Range", [
        v3_product([
          v3_bigint_text(lower.to_string()),
          v3_bigint_text(upper.to_string()),
        ]),
      ])
    Float(exponent_digits, significand_digits) =>
      v3_node(b"Ty.type_def.Float", [
        v3_product([v3_int(exponent_digits), v3_int(significand_digits)]),
      ])
  }
}

///|
fn v3_type_symbol(
  state : CanonicalV3State,
  symbol : @logic.TypeSymbol,
) -> CanonicalValue {
  let kind = V3TypeSymbol
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
        v3_node(b"Ty.tysymbol", [
          v3_identifier(state, view.id, view.origin),
          v3_sequence(
            [
              for parameter in view.parameters => {
                v3_tyvar_symbol(state, parameter)
              }
            ],
          ),
          v3_type_definition(state, view.definition),
        ]),
      )
      v3_reference(kind, index)
    }
  }
}

///|
fn v3_ty(state : CanonicalV3State, ty : @logic.Ty) -> CanonicalValue {
  match state.type_indices.get(ty) {
    Some(index) => v3_reference(V3Type, index)
    None => {
      let (index, position) = state.reserve(V3Type)
      state.type_indices[ty] = index
      let node = match ty.view() {
        TyVar(variable) =>
          v3_node(b"Ty.ty_node.Tyvar", [v3_tyvar_symbol(state, variable)])
        TyApp(symbol, arguments) =>
          v3_node(b"Ty.ty_node.Tyapp", [
            v3_product([
              v3_type_symbol(state, symbol),
              v3_sequence(
                [
                  for argument in arguments => v3_ty(state, argument)
                ],
              ),
            ]),
          ])
      }
      state.fill(V3Type, index, position, v3_node(b"Ty.ty", [node]))
      v3_reference(V3Type, index)
    }
  }
}

///|
fn v3_vsymbol(
  state : CanonicalV3State,
  symbol : @logic.VSymbol,
) -> CanonicalValue {
  let kind = V3LogicVariable
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
        v3_node(b"Term.vsymbol", [
          v3_identifier(state, view.id, view.origin),
          v3_ty(state, view.ty),
        ]),
      )
      v3_reference(kind, index)
    }
  }
}

///|
fn v3_lsymbol(
  state : CanonicalV3State,
  symbol : @logic.LSymbol,
) -> CanonicalValue {
  let kind = V3LogicSymbol
  let view = symbol.view()
  match state.semantic_index(kind, view.id) {
    Some(index) => v3_reference(kind, index)
    None => {
      let (index, position) = state.reserve(kind)
      state.remember_semantic_index(kind, view.id, index)
      let (constructor_count, projection) = match view.role {
        Ordinary => (0, false)
        Constructor(count) => (count, false)
        Projection => (0, true)
      }
      state.fill(
        kind,
        index,
        position,
        v3_node(b"Term.lsymbol", [
          v3_identifier(state, view.id, view.origin),
          v3_sequence(
            [
              for argument in view.argument_types => v3_ty(state, argument)
            ],
          ),
          match view.result_type {
            None => v3_none()
            Some(result) => v3_some(v3_ty(state, result))
          },
          v3_int(constructor_count),
          v3_bool(projection),
        ]),
      )
      v3_reference(kind, index)
    }
  }
}

///|
fn v3_prsymbol(
  state : CanonicalV3State,
  symbol : @logic.PrSymbol,
) -> CanonicalValue {
  let kind = V3PropositionSymbol
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
        v3_node(b"Decl.prsymbol", [v3_identifier(state, view.id, view.origin)]),
      )
      v3_reference(kind, index)
    }
  }
}

///|
fn v3_integer_literal_kind(kind : @logic.IntLiteralKind) -> CanonicalValue {
  let tag = match kind {
    ILitUnk => b"Number.int_literal_kind.ILitUnk"
    ILitDec => b"Number.int_literal_kind.ILitDec"
    ILitHex => b"Number.int_literal_kind.ILitHex"
    ILitOct => b"Number.int_literal_kind.ILitOct"
    ILitBin => b"Number.int_literal_kind.ILitBin"
  }
  v3_node(tag, [v3_unit()])
}

///|
fn v3_real_literal_kind(kind : @logic.RealLiteralKind) -> CanonicalValue {
  match kind {
    RLitUnk => v3_node(b"Number.real_literal_kind.RLitUnk", [v3_unit()])
    RLitDec(exponent) =>
      v3_node(b"Number.real_literal_kind.RLitDec", [v3_int64(exponent)])
    RLitHex(exponent) =>
      v3_node(b"Number.real_literal_kind.RLitHex", [v3_int64(exponent)])
  }
}

///|
fn v3_constant(constant : @logic.Constant) -> CanonicalValue {
  match constant {
    ConstInt({ kind, value }) =>
      v3_node(b"Constant.constant.ConstInt", [
        v3_node(b"Number.int_constant", [
          v3_integer_literal_kind(kind),
          v3_bigint_text(value.to_string()),
        ]),
      ])
    ConstReal({ kind, value }) =>
      v3_node(b"Constant.constant.ConstReal", [
        v3_node(b"Number.real_constant", [
          v3_real_literal_kind(kind),
          v3_node(b"Number.real_value", [
            v3_bigint_text(value.significand().to_string()),
            v3_bigint_text(value.pow2().to_string()),
            v3_bigint_text(value.pow5().to_string()),
          ]),
        ]),
      ])
    ConstStr(value) => v3_node(b"Constant.constant.ConstStr", [v3_bytes(value)])
  }
}

///|
fn v3_bound_variable_index(
  bound : ArrayView[@logic.VSymbol],
  variable : @logic.VSymbol,
) -> UInt? {
  for index = bound.length() - 1; index >= 0; index = index - 1 {
    if bound[index] == variable {
      return Some((bound.length() - 1 - index).reinterpret_as_uint())
    }
  }
  None
}

///|
fn v3_extend_bound_variables(
  bound : ArrayView[@logic.VSymbol],
  variables : ArrayView[@logic.VSymbol],
) -> Array[@logic.VSymbol] {
  let result = bound.to_owned()
  result.push_iter(variables.iter())
  result
}

///|
fn v3_variable_reference(
  state : CanonicalV3State,
  bound : ArrayView[@logic.VSymbol],
  variable : @logic.VSymbol,
) -> CanonicalValue {
  match v3_bound_variable_index(bound, variable) {
    Some(index) => v3_de_bruijn(index)
    None => v3_vsymbol(state, variable)
  }
}

///|
fn v3_pattern_binder(
  state : CanonicalV3State,
  bound : ArrayView[@logic.VSymbol],
  variable : @logic.VSymbol,
) -> CanonicalValue {
  guard v3_bound_variable_index(bound, variable) is Some(index) else {
    abort("canonical v3 pattern binder is absent from its binding set")
  }
  v3_product([v3_de_bruijn(index), v3_ty(state, variable.ty())])
}

///|
fn v3_pattern(
  state : CanonicalV3State,
  bound : ArrayView[@logic.VSymbol],
  pattern : @logic.Pattern,
) -> CanonicalValue {
  let (index, position) = state.reserve(V3Pattern)
  let node = match pattern.view() {
    Pwild(_) => v3_node(b"Term.pattern_node.Pwild", [v3_unit()])
    Pvar(variable) =>
      v3_node(b"Term.pattern_node.Pvar", [
        v3_pattern_binder(state, bound, variable),
      ])
    Papp(symbol, arguments, _) =>
      v3_node(b"Term.pattern_node.Papp", [
        v3_product([
          v3_lsymbol(state, symbol),
          v3_sequence(
            [
              for argument in arguments => v3_pattern(state, bound, argument)
            ],
          ),
        ]),
      ])
    Por(left, right, _) =>
      v3_node(b"Term.pattern_node.Por", [
        v3_product([
          v3_pattern(state, bound, left),
          v3_pattern(state, bound, right),
        ]),
      ])
    Pas(inner, variable, _) =>
      v3_node(b"Term.pattern_node.Pas", [
        v3_product([
          v3_pattern(state, bound, inner),
          v3_pattern_binder(state, bound, variable),
        ]),
      ])
  }
  state.fill(
    V3Pattern,
    index,
    position,
    v3_node(b"Term.pattern", [node, v3_ty(state, pattern.ty())]),
  )
  v3_reference(V3Pattern, index)
}

///|
fn v3_quantifier(quantifier : @logic.Quantifier) -> CanonicalValue {
  match quantifier {
    ForallQuantifier => v3_node(b"Term.quant.Tforall", [v3_unit()])
    ExistsQuantifier => v3_node(b"Term.quant.Texists", [v3_unit()])
  }
}

///|
fn v3_binary_operator(operator : @logic.BinaryLogicOp) -> CanonicalValue {
  let tag = match operator {
    And => b"Term.binop.Tand"
    Or => b"Term.binop.Tor"
    Implies => b"Term.binop.Timplies"
    Iff => b"Term.binop.Tiff"
  }
  v3_node(tag, [v3_unit()])
}

///|
fn v3_term(
  state : CanonicalV3State,
  bound : ArrayView[@logic.VSymbol],
  term : @logic.Term,
) -> CanonicalValue {
  let (index, position) = state.reserve(V3Term)
  let node = match term.view() {
    Tvar(variable) =>
      v3_node(b"Term.term_node.Tvar", [
        v3_variable_reference(state, bound, variable),
      ])
    Tconst(constant) =>
      v3_node(b"Term.term_node.Tconst", [v3_constant(constant)])
    Tapp(symbol, _, arguments) =>
      v3_node(b"Term.term_node.Tapp", [
        v3_product([
          v3_lsymbol(state, symbol),
          v3_sequence(
            [
              for argument in arguments => v3_term(state, bound, argument)
            ],
          ),
        ]),
      ])
    Tif(condition, then_branch, else_branch) =>
      v3_node(b"Term.term_node.Tif", [
        v3_product([
          v3_term(state, bound, condition),
          v3_term(state, bound, then_branch),
          v3_term(state, bound, else_branch),
        ]),
      ])
    Tlet(variable, value, body) =>
      v3_node(b"Term.term_node.Tlet", [
        v3_product([
          v3_term(state, bound, value),
          v3_ty(state, variable.ty()),
          v3_term(state, v3_extend_bound_variables(bound, [variable]), body),
        ]),
      ])
    Tcase(scrutinee, branches) =>
      v3_node(b"Term.term_node.Tcase", [
        v3_product([
          v3_term(state, bound, scrutinee),
          v3_sequence(
            [
              for branch in branches => {
                let view = branch.view()
                let variables = view.pattern.bound_variables().to_owned()
                variables.sort_by((left, right) => {
                  left
                  .semantic_id()
                  .local_id()
                  .compare(right.semantic_id().local_id())
                })
                v3_product([
                  v3_pattern(state, variables, view.pattern),
                  v3_term(
                    state,
                    v3_extend_bound_variables(bound, variables),
                    view.body,
                  ),
                ])
              }
            ],
          ),
        ]),
      ])
    Teps(variable, body) =>
      v3_node(b"Term.term_node.Teps", [
        v3_product([
          v3_ty(state, variable.ty()),
          v3_term(state, v3_extend_bound_variables(bound, [variable]), body),
        ]),
      ])
    Tquant(quantifier, binders, triggers, body) => {
      let extended = v3_extend_bound_variables(bound, binders)
      v3_node(b"Term.term_node.Tquant", [
        v3_product([
          v3_quantifier(quantifier),
          v3_sequence([ for binder in binders => v3_ty(state, binder.ty()) ]),
          v3_sequence(
            [
              for trigger in triggers => {
                v3_sequence(
                  [
                    for item in trigger => v3_term(state, extended, item)
                  ],
                )
              }
            ],
          ),
          v3_term(state, extended, body),
        ]),
      ])
    }
    Tbinop(operator, left, right) =>
      v3_node(b"Term.term_node.Tbinop", [
        v3_product([
          v3_binary_operator(operator),
          v3_term(state, bound, left),
          v3_term(state, bound, right),
        ]),
      ])
    Tnot(inner) =>
      v3_node(b"Term.term_node.Tnot", [v3_term(state, bound, inner)])
    Ttrue => v3_node(b"Term.term_node.Ttrue", [v3_unit()])
    Tfalse => v3_node(b"Term.term_node.Tfalse", [v3_unit()])
  }
  let record = v3_node(b"Term.term", [
    node,
    match term.ty() {
      None => v3_none()
      Some(ty) => v3_some(v3_ty(state, ty))
    },
    v3_attributes(state, term.attributes()),
    v3_source_span_option(term.source_span()),
  ])
  state.fill(
    V3Term,
    index,
    position,
    v3_product([
      record,
      match term.origin() {
        None => v3_none()
        Some(origin) => v3_some(v3_origin(state, origin))
      },
    ]),
  )
  v3_reference(V3Term, index)
}

///|
fn v3_proposition_kind(kind : @logic.PropositionKind) -> CanonicalValue {
  let tag = match kind {
    Paxiom => b"Decl.prop_kind.Paxiom"
    Plemma => b"Decl.prop_kind.Plemma"
    Pgoal => b"Decl.prop_kind.Pgoal"
  }
  v3_node(tag, [v3_unit()])
}

///|
fn v3_inductive_sign(sign : @logic.InductiveSign) -> CanonicalValue {
  let tag = match sign {
    Ind => b"Decl.ind_sign.Ind"
    Coind => b"Decl.ind_sign.Coind"
  }
  v3_node(tag, [v3_unit()])
}

///|
fn v3_decl(
  state : CanonicalV3State,
  declaration : @logic.Decl,
) -> CanonicalValue {
  let (index, position) = state.reserve(V3Declaration)
  let node = match declaration.view() {
    Dtype(symbols) =>
      v3_node(b"Decl.decl_node.Dtype", [
        if symbols.length() == 1 {
          v3_type_symbol(state, symbols[0])
        } else {
          v3_sequence(
            [
              for symbol in symbols => v3_type_symbol(state, symbol)
            ],
          )
        },
      ])
    Ddata(declarations) =>
      v3_node(b"Decl.decl_node.Ddata", [
        v3_sequence(
          [
            for data in declarations => {
              let view = data.view()
              v3_product([
                v3_type_symbol(state, view.type_symbol),
                v3_sequence(
                  [
                    for data_constructor in view.constructors => {
                      let constructor_view = data_constructor.view()
                      v3_product([
                        v3_lsymbol(state, constructor_view.symbol),
                        v3_sequence(
                          [
                            for projection in constructor_view.projections => {
                              match projection {
                                None => v3_none()
                                Some(symbol) =>
                                  v3_some(v3_lsymbol(state, symbol))
                              }
                            }
                          ],
                        ),
                      ])
                    }
                  ],
                ),
              ])
            }
          ],
        ),
      ])
    Dparam(symbol) =>
      v3_node(b"Decl.decl_node.Dparam", [v3_lsymbol(state, symbol)])
    Dlogic(definitions) =>
      v3_node(b"Decl.decl_node.Dlogic", [
        v3_sequence(
          [
            for definition in definitions => {
              let view = definition.view()
              v3_product([
                v3_lsymbol(state, view.symbol),
                v3_sequence(
                  [
                    for parameter in view.parameters => {
                      v3_ty(state, parameter.ty())
                    }
                  ],
                ),
                v3_term(state, view.parameters, view.body),
              ])
            }
          ],
        ),
      ])
    Dind(sign, declarations) =>
      v3_node(b"Decl.decl_node.Dind", [
        v3_product([
          v3_inductive_sign(sign),
          v3_sequence(
            [
              for inductive in declarations => {
                let view = inductive.view()
                v3_product([
                  v3_lsymbol(state, view.predicate),
                  v3_sequence(
                    [
                      for case_ in view.cases => {
                        let case_view = case_.view()
                        v3_product([
                          v3_prsymbol(state, case_view.proposition),
                          v3_term(state, [], case_view.formula),
                        ])
                      }
                    ],
                  ),
                ])
              }
            ],
          ),
        ]),
      ])
    Dprop(kind, symbol, formula) =>
      v3_node(b"Decl.decl_node.Dprop", [
        v3_product([
          v3_proposition_kind(kind),
          v3_prsymbol(state, symbol),
          v3_term(state, [], formula),
        ]),
      ])
  }
  state.fill(
    V3Declaration,
    index,
    position,
    v3_product([
      v3_node(b"Decl.decl", [node]),
      v3_origin(state, declaration.origin()),
    ]),
  )
  v3_reference(V3Declaration, index)
}

///|
pub fn encode_ty(ty : @logic.Ty) -> CanonicalJson {
  let state = CanonicalV3State::new()
  state.finish([v3_ty(state, ty)])
}

///|
pub fn encode_type_symbol(symbol : @logic.TypeSymbol) -> CanonicalJson {
  let state = CanonicalV3State::new()
  state.finish([v3_type_symbol(state, symbol)])
}

///|
pub fn encode_vsymbol(symbol : @logic.VSymbol) -> CanonicalJson {
  let state = CanonicalV3State::new()
  state.finish([v3_vsymbol(state, symbol)])
}

///|
pub fn encode_lsymbol(symbol : @logic.LSymbol) -> CanonicalJson {
  let state = CanonicalV3State::new()
  state.finish([v3_lsymbol(state, symbol)])
}

///|
pub fn encode_prsymbol(symbol : @logic.PrSymbol) -> CanonicalJson {
  let state = CanonicalV3State::new()
  state.finish([v3_prsymbol(state, symbol)])
}

///|
pub fn encode_constant(constant : @logic.Constant) -> CanonicalJson {
  let state = CanonicalV3State::new()
  state.finish([v3_constant(constant)])
}

///|
pub fn encode_term(term : @logic.Term) -> CanonicalJson {
  let state = CanonicalV3State::new()
  state.finish([v3_term(state, [], term)])
}

///|
pub fn encode_decl(declaration : @logic.Decl) -> CanonicalJson {
  let state = CanonicalV3State::new()
  state.finish([v3_decl(state, declaration)])
}
