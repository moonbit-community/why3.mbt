// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn vc_identifier_attributes(routine : @mlw.RoutineSymbol) -> Array[Bytes] {
  let view = routine.view()
  let attributes = view.origin.attributes().to_owned()
  if !has_explanation(attributes) {
    attributes.push(append_bytes(b"expl:VC for ", view.name))
  }
  attributes
}

///|
fn make_vc_declaration(
  environment : VcEnvironment,
  routine : @mlw.RoutineSymbol,
  formula : @logic.Term,
) -> @logic.Decl raise {
  let routine_view = routine.view()
  let goal_name = append_bytes(routine_view.name, b"'vc")
  let span = routine_view.origin.source_span()
  let origin = @identity.Origin::user(
    goal_name,
    span,
    vc_identifier_attributes(routine),
  )
  let proposition = @logic.PrSymbol::new(environment.context, goal_name, origin)
  let closed = forall_simplified(formula.free_variables(), formula)
  let simplified = eval_match_minimal(environment, closed)
  @logic.Decl::proposition(
    environment.context,
    origin,
    Pgoal,
    proposition,
    simplified,
    span,
  )
}

///|
pub fn generate_routine_vc(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
  routine : @mlw.RoutineSymbol,
  cty : @mlw.Cty,
  body : @mlw.Expr,
) -> @logic.Decl? raise {
  let environment = VcEnvironment::new(context, pmodule)
  let formula = routine_vc_formula(environment, cty, body)
  if is_structurally_trivial(formula) &&
    !contains_attribute(formula, annotation_attribute) {
    None
  } else {
    Some(make_vc_declaration(environment, routine, formula))
  }
}

///|
pub fn generate_module(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
) -> @mlw.Pmodule raise {
  let view = pmodule.view()
  if !context.contains(pmodule.context_anchor()) {
    fail_vc(
      ContextMismatch,
      None,
      "VC generator and program module belong to different contexts",
    )
  }
  let declarations : Array[@logic.Decl] = []
  let items : Array[@mlw.ModuleItem] = []
  for item in view.items {
    match item {
      Udecl(PDlet(routine, Cfun(cty, Some(body)), _)) => {
        match generate_routine_vc(context, pmodule, routine, cty, body) {
          Some(declaration) => {
            declarations.push(declaration)
            items.push(Udecl(PDpure([declaration])))
          }
          None => ()
        }
        items.push(item)
      }
      _ => items.push(item)
    }
  }
  if declarations.is_empty() {
    return pmodule
  }
  @mlw.Pmodule::trusted_new(
    view.key,
    view.pure_theory.append_declarations(context, declarations, None),
    items,
    view.export_namespace,
  )
}
