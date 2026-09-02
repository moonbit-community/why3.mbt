// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
fn[A] driver_bind_error(
  kind : @z3.BindErrorKind,
  path : String,
  message : String,
) -> A raise @z3.BindError {
  raise @z3.BindError({ kind, path, message })
}

///|
fn driver_theory_key(
  text : BytesView,
  path : String,
) -> @theory.TheoryKey raise @z3.BindError {
  let segments : Array[Bytes] = []
  let mut start = 0
  for index, byte in text {
    if byte == b'.' {
      if index == start {
        driver_bind_error(
          @z3.InvalidProfile,
          path,
          "driver theory key contains an empty segment",
        )
      }
      segments.push(text[start:index].to_owned())
      start = index + 1
    }
  }
  if start == text.length() {
    driver_bind_error(
      @z3.InvalidProfile,
      path,
      "driver theory key has an empty suffix",
    )
  }
  let name = text[start:].to_owned()
  @theory.TheoryKey::new(segments, name) catch {
    _ =>
      driver_bind_error(
        @z3.InvalidProfile,
        path,
        "driver theory key is invalid",
      )
  }
}

///|
fn source_driver_theory(
  environment : @environment.Environment,
  key : @theory.TheoryKey,
  path : String,
) -> @theory.Theory raise @z3.BindError {
  let already_loaded = Some(environment.resolve_theory(key, None)) catch {
    _ => None
  }
  match already_loaded {
    Some(theory) => theory
    None => {
      let view = key.view()
      environment.read_theory(
        @env.LibraryPath::new(view.path),
        view.name,
        @elab.load_mlw_library,
        None,
      ) catch {
        _ =>
          driver_bind_error(
            @z3.MissingSymbol,
            path,
            "driver theory could not be loaded from the pinned standard library",
          )
      }
    }
  }
}

///|
fn source_declaration_symbols(
  declaration : @logic.Decl,
) -> Array[@z3.ResolvedDriverSymbol] {
  let symbols : Array[@z3.ResolvedDriverSymbol] = []
  match declaration.view() {
    Dtype(types) =>
      for symbol in types {
        symbols.push(@z3.ResolvedType(symbol))
      }
    Ddata(declarations) =>
      for declaration in declarations {
        let view = declaration.view()
        symbols.push(@z3.ResolvedType(view.type_symbol))
        for constructor_symbol in view.constructors {
          let constructor_view = constructor_symbol.view()
          symbols.push(@z3.ResolvedLogic(constructor_view.symbol))
          for projection in constructor_view.projections {
            if projection is Some(symbol) {
              symbols.push(@z3.ResolvedLogic(symbol))
            }
          }
        }
      }
    Dparam(symbol) => symbols.push(@z3.ResolvedLogic(symbol))
    Dlogic(definitions) =>
      for definition in definitions {
        symbols.push(@z3.ResolvedLogic(definition.view().symbol))
      }
    Dind(_, declarations) =>
      for declaration in declarations {
        let view = declaration.view()
        symbols.push(@z3.ResolvedLogic(view.predicate))
        for case_ in view.cases {
          symbols.push(@z3.ResolvedProposition(case_.view().proposition))
        }
      }
    Dprop(_, proposition, _) =>
      symbols.push(@z3.ResolvedProposition(proposition))
  }
  symbols
}

///|
fn source_driver_symbol(
  environment : @environment.Environment,
  key : @identity.SourceSymbolKey,
  path : String,
) -> @z3.ResolvedDriverSymbol raise @z3.BindError {
  let view = key.view()
  let theory_key = driver_theory_key(view.theory_key, path + ".theoryKey")
  let theory = source_driver_theory(environment, theory_key, path)
  let mut declaration : @logic.Decl? = None
  for index, item in theory.view().items {
    if index.reinterpret_as_uint() == view.theory_item_ordinal {
      if item is TheoryDecl(found) {
        declaration = Some(found)
      }
      break
    }
  }
  guard declaration is Some(declaration) else {
    let shapes : Array[String] = []
    for item in theory.view().items {
      shapes.push(
        match item {
          TheoryUse(key) => "use:" + key.view().name.to_string()
          TheoryClone(_) => "clone"
          TheoryMeta(_) => "meta"
          TheoryDecl(declaration) =>
            match declaration.view() {
              Dtype(_) => "decl:type"
              Ddata(_) => "decl:data"
              Dparam(_) => "decl:param"
              Dlogic(_) => "decl:logic"
              Dind(_, _) => "decl:ind"
              Dprop(_, _, _) => "decl:prop"
            }
        },
      )
    }
    driver_bind_error(
      @z3.MissingSymbol,
      path,
      "driver locator item " +
      view.theory_item_ordinal.to_string() +
      " does not select a source declaration in " +
      view.theory_key.to_string() +
      " (item count " +
      theory.view().items.length().to_string() +
      "; " +
      shapes.join(",") +
      ")",
    )
  }
  let symbols = source_declaration_symbols(declaration)
  for index, symbol in symbols {
    if index.reinterpret_as_uint() == view.declaration_inner_ordinal {
      return symbol
    }
  }
  driver_bind_error(
    @z3.MissingSymbol,
    path,
    "driver locator inner ordinal is absent from the source declaration",
  )
}

///|
pub fn bind_z3_profile(
  environment : @environment.Environment,
  context : @identity.CompilationContext,
) -> @z3.Z3Profile raise @z3.BindError {
  if !context.contains(environment.context_anchor()) {
    driver_bind_error(
      @z3.ContextMismatch,
      "$.environment",
      "driver environment belongs to another compilation context",
    )
  }
  let spec = @z3.z3_static_spec()
  let entries : Array[(@identity.SourceSymbolKey, @z3.ResolvedDriverSymbol)] = []
  for index, key in spec.required_keys() {
    let path = "$.requiredKeys[" + index.to_string() + "]"
    let symbol = source_driver_symbol(environment, key, path)
    match (key.view().symbol_kind, symbol) {
      (Type, @z3.ResolvedType(_))
      | (Logic, @z3.ResolvedLogic(_))
      | (Proposition, @z3.ResolvedProposition(_)) => ()
      _ =>
        driver_bind_error(
          @z3.SymbolKindMismatch,
          path,
          "driver locator resolved to a different source symbol kind",
        )
    }
    entries.push((key, symbol))
  }
  let resolver = @z3.DriverSymbolResolver::from_source(
    environment.context_anchor(),
    entries,
  )
  @z3.bind_profile(spec, resolver, context)
}

///|
pub fn update_z3_task(
  profile : @z3.Z3Profile,
  task : @theory.Task,
) -> @theory.Task raise @z3.BindError {
  @transform.begin_declaration_cache_goal(task)
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
fn apply_named_user_transform(
  profile : @z3.Z3Profile,
  context : @identity.CompilationContext,
  task : @theory.Task,
  name : BytesView,
) -> @theory.Task raise @transform.TransformError {
  match name {
    b"counterexamples_dependent_intros" =>
      counterexamples_dependent_intros(context, task)
    b"inline_trivial" => inline_trivial(context, task)
    b"eliminate_builtin" => eliminate_builtin(context, task)
    b"remove_unused_keep_constants" =>
      remove_unused_keep_constants(context, task)
    b"detect_polymorphism" => detect_polymorphism(context, task)
    b"eliminate_definition_conditionally" =>
      eliminate_definition_conditionally(context, task)
    b"eliminate_inductive" => eliminate_inductive(context, task)
    b"eliminate_epsilon" => eliminate_epsilon(context, task)
    b"eliminate_literal" => eliminate_literal(context, task)
    b"simplify_formula" => simplify_formula(context, task)
    b"prepare_for_counterexmp" => prepare_for_counterexmp(context, task)
    b"eliminate_projections_sums" => eliminate_projections_sums(context, task)
    b"discriminate_if_poly" => discriminate_if_poly(context, task)
    b"eliminate_algebraic_if_poly" =>
      eliminate_algebraic_if_poly(profile, context, task)
    b"encoding_smt_if_poly" => encoding_smt_if_poly(context, task)
    _ =>
      raise @transform.TransformError({
        kind: @transform.UnsupportedStructure,
        stage: @identity.DriverUpdate,
        message: "unknown user transform",
      })
  }
}

///|
fn add_user_metas(
  task : @theory.Task,
  metas : ArrayView[@theory.Meta],
) -> @theory.Task raise @theory.TheoryError {
  if metas.is_empty() {
    return task
  }
  let items = task.view().items.to_owned()
  guard items.pop() is Some(goal) else {
    raise @theory.TheoryError({
      kind: @theory.MissingGoal,
      span: None,
      message: "cannot add a meta to an empty task",
    })
  }
  for meta in metas {
    items.push(TheoryMeta(meta))
  }
  items.push(goal)
  @theory.Task::trusted_new_with_dependencies(
    task.context_anchor(),
    items,
    task.dependency_theories(),
    None,
  )
}

///|
fn prepare_z3_task_with_user_options(
  profile : @z3.Z3Profile,
  context : @identity.CompilationContext,
  task : @theory.Task,
  transforms : ArrayView[Bytes],
  metas : ArrayView[@theory.Meta],
  request_model : Bool,
) -> @theory.Task raise {
  let requested_metas = metas.to_owned()
  if request_model &&
    !requested_metas.any(meta => meta.view().name == b"get_counterexmp") {
    requested_metas.push(@theory.Meta::exclusive(b"get_counterexmp", []))
  }
  let mut task = add_user_metas(task, requested_metas)
  for transform in transforms {
    task = apply_named_user_transform(profile, context, task, transform)
  }
  prepare_z3_task(profile, context, task)
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
