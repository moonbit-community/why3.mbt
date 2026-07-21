// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub fn counterexamples_dependent_intros(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.counterexamples_dependent_intros(context, task)
}

///|
pub fn inline_trivial(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.inline_trivial(context, task)
}

///|
pub fn eliminate_builtin(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.eliminate_builtin(context, task)
}

///|
pub fn remove_unused_keep_constants(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.remove_unused_keep_constants(context, task)
}

///|
pub fn detect_polymorphism(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.detect_polymorphism(context, task)
}

///|
pub fn eliminate_definition_conditionally(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.eliminate_definition_conditionally(context, task)
}

///|
pub fn eliminate_inductive(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.eliminate_inductive(context, task)
}

///|
pub fn eliminate_epsilon(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.eliminate_epsilon(context, task)
}

///|
pub fn eliminate_literal(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.eliminate_literal(context, task)
}

///|
pub fn simplify_formula(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.simplify_formula(context, task)
}

///|
pub fn prepare_for_counterexmp(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.prepare_for_counterexmp(context, task)
}

///|
pub fn eliminate_projections_sums(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.eliminate_projections_sums(context, task)
}

///|
pub fn discriminate_monomorphise_goal(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.discriminate_monomorphise_goal(context, task)
}

///|
pub fn discriminate_if_poly(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.discriminate_if_poly(context, task)
}

///|
pub fn eliminate_algebraic_if_poly(
  profile : @z3.Z3Profile,
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.eliminate_algebraic_if_poly(
    context,
    task,
    profile.builtin_type(BuiltinInteger),
    profile.builtin_type(BuiltinReal),
    profile.builtin_type(BuiltinString),
  )
}

///|
pub fn encoding_monomorphise_goal(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.encoding_monomorphise_goal(context, task)
}

///|
pub fn encoding_select_kept(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.encoding_select_kept(context, task)
}

///|
pub fn encoding_keep_field_types(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.encoding_keep_field_types(context, task)
}

///|
pub fn encoding_twin(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.encoding_twin(context, task)
}

///|
pub fn encoding_guards(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.encoding_guards(context, task)
}

///|
pub fn encoding_smt_if_poly(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise @transform.TransformError {
  @transform.encoding_smt_if_poly(context, task)
}
