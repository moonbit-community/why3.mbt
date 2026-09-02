// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn v3_bound_program_pure_symbols(
  bound : ArrayView[@mlw.PVariable],
) -> Array[@logic.VSymbol] {
  [
    for variable in bound => variable.view().pure_symbol
  ]
}

///|
fn v3_pattern_ghost(failure : @mlw.PatternGhost) -> CanonicalValue {
  let tag = match failure {
    PGfail => b"Expr.pat_ghost.PGfail"
    PGlast => b"Expr.pat_ghost.PGlast"
    PGnone => b"Expr.pat_ghost.PGnone"
  }
  v3_node(tag, [v3_unit()])
}

///|
fn v3_program_pattern(
  state : CanonicalV3State,
  pattern : @mlw.ProgramPattern,
) -> CanonicalValue {
  let (index, position) = state.reserve(V3ProgramPattern)
  let view = pattern.view()
  let pure_variables = [
    for variable in view.variables => variable.view().pure_symbol
  ]
  state.fill(
    V3ProgramPattern,
    index,
    position,
    v3_node(b"Expr.prog_pattern", [
      v3_pattern(state, pure_variables, view.pattern),
      v3_ity(state, view.ity),
      v3_program_mask(view.mask),
      v3_pattern_ghost(view.failure),
    ]),
  )
  v3_reference(V3ProgramPattern, index)
}

///|
fn v3_program_variant(
  state : CanonicalV3State,
  bound : ArrayView[@mlw.PVariable],
  variant : @mlw.ProgramVariant,
) -> CanonicalValue {
  let view = variant.view()
  v3_product([
    v3_term(state, v3_bound_program_pure_symbols(bound), view.term),
    match view.relation {
      None => v3_none()
      Some(relation) => v3_some(v3_lsymbol(state, relation))
    },
  ])
}

///|
fn v3_cexp(
  state : CanonicalV3State,
  bound : ArrayView[@mlw.PVariable],
  computation : @mlw.Cexp,
) -> CanonicalValue {
  let (index, position) = state.reserve(V3ComputationExpression)
  let cty = computation.cty()
  let node = match computation.view() {
    Capp(symbol, arguments) =>
      v3_node(b"Expr.cexp_node.Capp", [
        v3_product([
          v3_routine_symbol(state, symbol),
          v3_sequence(
            [
              for argument in arguments => {
                v3_program_variable_reference(state, bound, argument)
              }
            ],
          ),
        ]),
      ])
    Cpur(symbol, arguments) =>
      v3_node(b"Expr.cexp_node.Cpur", [
        v3_product([
          v3_lsymbol(state, symbol),
          v3_sequence(
            [
              for argument in arguments => {
                v3_program_variable_reference(state, bound, argument)
              }
            ],
          ),
        ]),
      ])
    Cfun(body) =>
      v3_node(b"Expr.cexp_node.Cfun", [
        v3_expr(
          state,
          v3_extend_bound_program_variables(bound, cty.view().arguments),
          body,
        ),
      ])
    Cany => v3_node(b"Expr.cexp_node.Cany", [v3_unit()])
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
fn v3_assertion_kind(kind : @mlw.AssertionKind) -> CanonicalValue {
  let tag = match kind {
    Assert => b"Expr.assertion_kind.Assert"
    Assume => b"Expr.assertion_kind.Assume"
    Check => b"Expr.assertion_kind.Check"
  }
  v3_node(tag, [v3_unit()])
}

///|
fn v3_for_direction(direction : @mlw.ForDirection) -> CanonicalValue {
  let tag = match direction {
    To => b"Expr.for_direction.To"
    DownTo => b"Expr.for_direction.DownTo"
  }
  v3_node(tag, [v3_unit()])
}

///|
fn v3_recursive_definition(
  state : CanonicalV3State,
  bound : ArrayView[@mlw.PVariable],
  definition : @mlw.RecursiveDefinition,
) -> CanonicalValue {
  let view = definition.view()
  v3_node(b"Expr.rec_defn", [
    v3_routine_symbol(state, view.symbol),
    v3_routine_symbol(state, view.internal_symbol),
    v3_cexp(state, bound, view.function_),
    v3_sequence(
      [
        for variant in view.variants => {
          v3_program_variant(state, bound, variant)
        }
      ],
    ),
  ])
}

///|
fn v3_let_definition(
  state : CanonicalV3State,
  bound : ArrayView[@mlw.PVariable],
  definition : @mlw.LetDefinition,
) -> CanonicalValue {
  match definition.view() {
    LDvar(variable, value) =>
      v3_node(b"Expr.let_defn.LDvar", [
        v3_product([
          v3_program_binder(state, [variable], variable),
          v3_expr(state, bound, value),
        ]),
      ])
    LDsym(symbol, computation) =>
      v3_node(b"Expr.let_defn.LDsym", [
        v3_product([
          v3_routine_symbol(state, symbol),
          v3_cexp(state, bound, computation),
        ]),
      ])
    LDrec(definitions) =>
      v3_node(b"Expr.let_defn.LDrec", [
        v3_sequence(
          [
            for definition in definitions => {
              v3_recursive_definition(state, bound, definition)
            }
          ],
        ),
      ])
  }
}

///|
fn v3_expr(
  state : CanonicalV3State,
  bound : ArrayView[@mlw.PVariable],
  expression : @mlw.Expr,
) -> CanonicalValue {
  let (index, position) = state.reserve(V3Expression)
  let node = match expression.view() {
    Evar(variable) =>
      v3_node(b"Expr.expr_node.Evar", [
        v3_program_variable_reference(state, bound, variable),
      ])
    Econst(constant) =>
      v3_node(b"Expr.expr_node.Econst", [v3_constant(constant)])
    Eexec(computation, cty) =>
      v3_node(b"Expr.expr_node.Eexec", [
        v3_product([v3_cexp(state, bound, computation), v3_cty(state, cty)]),
      ])
    Eassign(assignments) =>
      v3_node(b"Expr.expr_node.Eassign", [
        v3_sequence(
          [
            for assignment in assignments => {
              let view = assignment.view()
              v3_product([
                v3_program_variable_reference(state, bound, view.region),
                v3_routine_symbol(state, view.field),
                v3_program_variable_reference(state, bound, view.value),
              ])
            }
          ],
        ),
      ])
    Elet(definition, body) => {
      let body_bound = match definition.view() {
        LDvar(variable, _) =>
          v3_extend_bound_program_variables(bound, [variable])
        LDsym(_, _) | LDrec(_) => bound.to_owned()
      }
      v3_node(b"Expr.expr_node.Elet", [
        v3_product([
          v3_let_definition(state, bound, definition),
          v3_expr(state, body_bound, body),
        ]),
      ])
    }
    Eif(condition, consequent, alternative) =>
      v3_node(b"Expr.expr_node.Eif", [
        v3_product([
          v3_expr(state, bound, condition),
          v3_expr(state, bound, consequent),
          v3_expr(state, bound, alternative),
        ]),
      ])
    Ematch(scrutinee, regular, exceptional) =>
      v3_node(b"Expr.expr_node.Ematch", [
        v3_product([
          v3_expr(state, bound, scrutinee),
          v3_sequence(
            [
              for branch in regular => {
                let view = branch.view()
                let variables = view.pattern.view().variables
                v3_product([
                  v3_program_pattern(state, view.pattern),
                  v3_expr(
                    state,
                    v3_extend_bound_program_variables(bound, variables),
                    view.body,
                  ),
                ])
              }
            ],
          ),
          v3_map(
            [
              for branch in exceptional => {
                let view = branch.view()
                (
                  v3_exception_symbol(state, view.exception),
                  v3_product([
                    v3_sequence(
                      [
                        for variable in view.variables => {
                          v3_program_binder(state, view.variables, variable)
                        }
                      ],
                    ),
                    v3_expr(
                      state,
                      v3_extend_bound_program_variables(bound, view.variables),
                      view.body,
                    ),
                  ]),
                )
              }
            ],
          ),
        ]),
      ])
    Ewhile(condition, invariants, variants, body) =>
      v3_node(b"Expr.expr_node.Ewhile", [
        v3_product([
          v3_expr(state, bound, condition),
          v3_sequence(
            [
              for invariant in invariants => {
                v3_term(state, v3_bound_program_pure_symbols(bound), invariant)
              }
            ],
          ),
          v3_sequence(
            [
              for variant in variants => {
                v3_program_variant(state, bound, variant)
              }
            ],
          ),
          v3_expr(state, bound, body),
        ]),
      ])
    Efor(variable, bounds, internal, invariants, body) => {
      let bounds_view = bounds.view()
      let loop_bound = v3_extend_bound_program_variables(bound, [
        variable, internal,
      ])
      v3_node(b"Expr.expr_node.Efor", [
        v3_product([
          v3_program_binder(state, [variable], variable),
          v3_program_variable_reference(state, bound, bounds_view.first),
          v3_for_direction(bounds_view.direction),
          v3_program_variable_reference(state, bound, bounds_view.last),
          v3_program_binder(state, [internal], internal),
          v3_sequence(
            [
              for invariant in invariants => {
                v3_term(
                  state,
                  v3_bound_program_pure_symbols(loop_bound),
                  invariant,
                )
              }
            ],
          ),
          v3_expr(state, loop_bound, body),
        ]),
      ])
    }
    Eraise(exception, payload) =>
      v3_node(b"Expr.expr_node.Eraise", [
        v3_product([
          v3_exception_symbol(state, exception),
          v3_expr(state, bound, payload),
        ]),
      ])
    Eexn(exception, body) =>
      v3_node(b"Expr.expr_node.Eexn", [
        v3_product([
          v3_exception_symbol(state, exception),
          v3_expr(state, bound, body),
        ]),
      ])
    Eassert(kind, formula) =>
      v3_node(b"Expr.expr_node.Eassert", [
        v3_product([
          v3_assertion_kind(kind),
          v3_term(state, v3_bound_program_pure_symbols(bound), formula),
        ]),
      ])
    Eghost(body) =>
      v3_node(b"Expr.expr_node.Eghost", [v3_expr(state, bound, body)])
    Epure(term) =>
      v3_node(b"Expr.expr_node.Epure", [
        v3_term(state, v3_bound_program_pure_symbols(bound), term),
      ])
    Eabsurd => v3_node(b"Expr.expr_node.Eabsurd", [v3_unit()])
  }
  let origin = expression.origin()
  state.fill(
    V3Expression,
    index,
    position,
    v3_product([
      v3_node(b"Expr.expr", [
        node,
        v3_ity(state, expression.ity()),
        v3_program_mask(expression.mask()),
        v3_effect(state, bound, expression.effect()),
        v3_attributes(state, expression.attributes()),
        v3_source_span_option(origin.source_span()),
      ]),
      v3_origin(state, origin),
    ]),
  )
  v3_reference(V3Expression, index)
}

///|
pub fn encode_expr(expression : @mlw.Expr) -> CanonicalJson {
  let state = CanonicalV3State::new()
  state.finish([v3_expr(state, [], expression)])
}
