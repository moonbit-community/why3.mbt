// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn map_catalog_error(
  diagnostic : @stdlib.BindDiagnostic,
  path : String,
) -> @z3.BindError {
  let kind = match diagnostic.kind {
    MissingSymbol => @z3.MissingSymbol
    SymbolDigestMismatch => @z3.SymbolDigestMismatch
    SymbolKindMismatch => @z3.SymbolKindMismatch
    CatalogContextMismatch => @z3.ContextMismatch
  }
  @z3.BindError({ kind, path, message: diagnostic.message })
}

///|
pub fn bind_z3_profile(
  environment : @stdlib.FrozenEnvironment,
  context : @identity.CompilationContext,
) -> @z3.Z3Profile raise @z3.BindError {
  let spec = @z3.z3_static_spec()
  let catalog = environment.driver_catalog()
  catalog.validate_context(context) catch {
    @stdlib.BindError(diagnostic) =>
      raise map_catalog_error(diagnostic, "$.resolver")
  }
  let entries : Array[(@identity.SnapshotSymbolKey, @z3.ResolvedDriverSymbol)] = []
  for index, key in spec.required_keys() {
    let path = "$.requiredKeys[" + index.to_string() + "]"
    let symbol = match key.view().symbol_kind {
      Type =>
        @z3.ResolvedType(catalog.resolve_type(key)) catch {
          @stdlib.BindError(diagnostic) =>
            raise map_catalog_error(diagnostic, path)
        }
      Logic =>
        @z3.ResolvedLogic(catalog.resolve_logic(key)) catch {
          @stdlib.BindError(diagnostic) =>
            raise map_catalog_error(diagnostic, path)
        }
      Proposition =>
        @z3.ResolvedProposition(catalog.resolve_proposition(key)) catch {
          @stdlib.BindError(diagnostic) =>
            raise map_catalog_error(diagnostic, path)
        }
      Program | Region =>
        raise @z3.BindError({
          kind: @z3.SymbolKindMismatch,
          path,
          message: "Z3 logic profile cannot bind a program or region symbol",
        })
    }
    entries.push((key, symbol))
  }
  let resolver = @z3.DriverSymbolResolver::new(
    catalog.context_anchor(),
    entries,
  )
  @z3.bind_profile(spec, resolver, context)
}

///|
pub fn update_z3_task(
  profile : @z3.Z3Profile,
  task : @theory.Task,
) -> @theory.Task raise @z3.BindError {
  profile.driver_update(task)
}

///|
/// Applies the pinned Why3 1.7.2 `z3_487` preparation sequence. Composite
/// transforms are kept as explicit calls so this entry point has the same
/// stage boundaries as the differential trace.
pub fn prepare_z3_task(
  profile : @z3.Z3Profile,
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise {
  let task = update_z3_task(profile, task)
  let task = counterexamples_dependent_intros(context, task)
  let task = inline_trivial(context, task)
  let task = eliminate_builtin(context, task)
  let task = remove_unused_keep_constants(context, task)
  let task = detect_polymorphism(context, task)
  let task = eliminate_definition_conditionally(context, task)
  let task = eliminate_inductive(context, task)
  let task = eliminate_epsilon(context, task)
  let task = eliminate_literal(context, task)
  let task = simplify_formula(context, task)
  let task = prepare_for_counterexmp(context, task)
  let task = eliminate_projections_sums(context, task)
  let task = discriminate_monomorphise_goal(context, task)
  let task = discriminate_if_poly(context, task)
  let task = eliminate_algebraic_if_poly(profile, context, task)
  let task = encoding_monomorphise_goal(context, task)
  let task = encoding_select_kept(context, task)
  let task = encoding_keep_field_types(context, task)
  let task = encoding_twin(context, task)
  let task = encoding_guards(context, task)
  encoding_smt_if_poly(context, task)
}

///|
pub fn print_prepared_z3_task(
  profile : @z3.Z3Profile,
  task : @theory.Task,
) -> @smtv2.SmtQuery raise {
  @smtv2.print_task(profile.printer_query(task), task)
}

///|
pub fn prepare_and_print_z3_task(
  profile : @z3.Z3Profile,
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @smtv2.SmtQuery raise {
  print_prepared_z3_task(profile, prepare_z3_task(profile, context, task))
}
