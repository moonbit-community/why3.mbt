// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
fn type_invariant_fields(
  declaration : @mlw.ProgramTypeDeclaration,
) -> Array[@mlw.PVariable] {
  declaration.view().fields.map(field => {
    guard field.view().field is Some(variable) else {
      abort("validated type invariant projection lost its field")
    }
    variable
  })
}

///|
fn explained_type_invariants(
  invariants : ArrayView[@logic.Term],
) -> @logic.Term raise {
  asymmetric_conjunction(
    invariants.map(invariant => {
      vc_explanation(invariant, [], b"expl:type invariant")
    }),
  )
}

///|
fn type_invariant_existence_formula(
  declaration : @mlw.ProgramTypeDeclaration,
) -> @logic.Term raise {
  let view = declaration.view()
  exists_simplified(
    type_invariant_fields(declaration).map(field => field.view().pure_symbol),
    explained_type_invariants(view.invariants),
  )
}

///|
fn type_invariant_witness_formula(
  environment : VcEnvironment,
  declaration : @mlw.ProgramTypeDeclaration,
  witness : @mlw.Expr,
) -> @logic.Term raise {
  let span = witness.origin().source_span()
  let fields = type_invariant_fields(declaration)
  let values : Array[@mlw.PVariable] = []
  let mut substitution = @logic.TermSubstitution::new()
  for field in fields {
    let view = field.view()
    let value = @mlw.PVariable::trusted_new(
      environment.context,
      view.name,
      view.ity,
      view.ghost,
      span,
    )
    values.push(value)
    substitution = substitution.bind(
      view.pure_symbol,
      @logic.Term::variable(value.view().pure_symbol),
      span,
    )
  }
  guard witness.ity().to_ty(span).view() is TyApp(tuple_type, _) &&
    environment.known.find_constructors(tuple_type, span) is [tuple_declaration] else {
    abort("type-invariant witness result is not a tuple")
  }
  let tuple = tuple_declaration.view().symbol
  let pattern = @logic.Pattern::app(
    tuple,
    values.map(value => @logic.Pattern::variable(value.view().pure_symbol)),
    witness.ity().to_ty(span),
    span,
  )
  let formula = explained_type_invariants(
    declaration.view().invariants.map(invariant => {
      substitution.apply(environment.context, invariant, span)
    }),
  )
  let result = proxy_variable(environment.context, witness)
  wp_kode(
    environment,
    kseq(
      lower_expression(environment, witness, result, []),
      0,
      kmode(EfficientSp, kcase(result, [(pattern, kstop(formula))])),
    ),
    [],
  )
}

///|
fn value_type_invariant_premise(
  environment : VcEnvironment,
  value : @logic.Term,
  attributes : ArrayView[Bytes],
) -> @logic.Term raise {
  conjunction(
    typeinv_require_values(environment, [value]).map(marker => {
      push_stop(marker, attributes, b"expl:type invariant")
    }),
  )
}

///|
fn variables_type_invariant_premise(
  environment : VcEnvironment,
  variables : ArrayView[@mlw.PVariable],
) -> @logic.Term raise {
  conjunction(
    typeinv_require_values(environment, variables.map(pvariable_term)).map(marker => {
      push_stop(marker, [], b"expl:type invariant")
    }),
  )
}
