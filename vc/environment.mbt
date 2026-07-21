// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
priv struct VcEnvironment {
  context : @identity.CompilationContext
  equality : @logic.LSymbol
  boolean_true : @logic.Term
  boolean_false : @logic.Term
  unit_value : @logic.Term
}

///|
fn VcEnvironment::new(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
) -> VcEnvironment raise {
  if !context.contains(pmodule.context_anchor()) {
    fail_vc(
      ContextMismatch,
      None,
      "VC generator and program module belong to different contexts",
    )
  }
  let pure_space = pmodule.pure_theory().export_namespace()
  let bool_type = @logic.Ty::app(
    pure_space.find_type([b"bool"], None),
    [],
    None,
  )
  let boolean_true = @logic.Term::elaborated_apply(
    pure_space.find_logic([b"True"], None),
    [],
    Some(bool_type),
    None,
  )
  let boolean_false = @logic.Term::elaborated_apply(
    pure_space.find_logic([b"False"], None),
    [],
    Some(bool_type),
    None,
  )
  let unit_type = @logic.Ty::app(
    pure_space.find_type([b"unit"], None),
    [],
    None,
  )
  let unit_value = @logic.Term::elaborated_apply(
    pure_space.find_logic([b"Tuple0"], None),
    [],
    Some(unit_type),
    None,
  )
  {
    context,
    equality: pure_space.find_logic([b"infix ="], None),
    boolean_true,
    boolean_false,
    unit_value,
  }
}

///|
fn VcEnvironment::boolean_test(
  self : VcEnvironment,
  variable : @mlw.PVariable,
) -> @logic.Term raise {
  @logic.Term::elaborated_apply(
    self.equality,
    [@logic.Term::variable(variable.view().pure_symbol), self.boolean_true],
    None,
    None,
  )
}
