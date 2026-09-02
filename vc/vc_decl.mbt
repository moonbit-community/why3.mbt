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
fn make_named_vc_declaration(
  environment : VcEnvironment,
  name : BytesView,
  source_origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  formula : @logic.Term,
) -> @logic.Decl raise {
  let goal_name = append_bytes(name, b"'vc")
  let span = source_origin.source_span()
  let origin = @identity.Origin::user(goal_name, span, attributes)
  let proposition = @logic.PrSymbol::new(environment.context, goal_name, origin)
  let free_variables = formula.free_variables()
  free_variables.sort_by((left, right) => {
    left.semantic_id().local_id().compare(right.semantic_id().local_id())
  })
  let closed = forall_simplified(free_variables, formula)
  let invariant_safe = typeinv_inject(environment, closed)
  let simplified = if environment.evaluate_matches {
    eval_match(environment, environment.keep_trace, invariant_safe)
  } else {
    invariant_safe
  }
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
fn make_vc_declaration(
  environment : VcEnvironment,
  routine : @mlw.RoutineSymbol,
  formula : @logic.Term,
) -> @logic.Decl raise {
  let view = routine.view()
  make_named_vc_declaration(
    environment,
    view.name,
    view.origin,
    vc_identifier_attributes(routine),
    formula,
  )
}

///|
fn type_vc_identifier_attributes(
  declaration : @mlw.ProgramTypeDeclaration,
) -> Array[Bytes] {
  let symbol = declaration.view().symbol.view().logic_type.view()
  let attributes = symbol.origin.attributes().to_owned()
  if !has_explanation(attributes) {
    attributes.push(append_bytes(b"expl:VC for ", symbol.name))
  }
  attributes
}

///|
fn make_type_vc_declaration(
  environment : VcEnvironment,
  declaration : @mlw.ProgramTypeDeclaration,
  formula : @logic.Term,
) -> @logic.Decl raise {
  let symbol = declaration.view().symbol.view().logic_type.view()
  make_named_vc_declaration(
    environment,
    symbol.name,
    symbol.origin,
    type_vc_identifier_attributes(declaration),
    formula,
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
  generate_routine_vc_with_options(
    context,
    pmodule,
    routine,
    cty,
    body,
    VcOptions::classical(),
  )
}

///|
pub fn generate_routine_vc_with_options(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
  routine : @mlw.RoutineSymbol,
  cty : @mlw.Cty,
  body : @mlw.Expr,
  options : VcOptions,
) -> @logic.Decl? raise {
  let environment = VcEnvironment::new(context, pmodule)
  generate_routine_vc_in_environment(environment, routine, cty, body, options)
}

///|
fn generate_routine_vc_in_environment(
  environment : VcEnvironment,
  routine : @mlw.RoutineSymbol,
  cty : @mlw.Cty,
  body : @mlw.Expr,
  options : VcOptions,
) -> @logic.Decl? raise {
  environment.configure_options(options, Some(body))
  let formula = routine_vc_formula(environment, cty, body, options.vc_mode())
  if is_structurally_trivial(formula) &&
    !contains_attribute(formula, annotation_attribute) {
    None
  } else {
    Some(make_vc_declaration(environment, routine, formula))
  }
}

///|
fn generate_type_vc(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
  declaration : @mlw.ProgramTypeDeclaration,
  options : VcOptions,
) -> @logic.Decl? raise {
  let view = declaration.view()
  if view.witness is None && view.invariants.is_empty() {
    return None
  }
  let environment = VcEnvironment::new(context, pmodule)
  environment.configure_options(options, None)
  let formula = match view.witness {
    Some(witness) =>
      type_invariant_witness_formula(environment, declaration, witness)
    None => type_invariant_existence_formula(declaration)
  }
  if is_structurally_trivial(formula) &&
    !contains_attribute(formula, annotation_attribute) {
    None
  } else {
    Some(make_type_vc_declaration(environment, declaration, formula))
  }
}

///|
fn generate_recursive_routine_vc(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
  definitions : ArrayView[@mlw.RecursiveDefinition],
  definition : @mlw.RecursiveDefinition,
  options : VcOptions,
) -> @logic.Decl? raise {
  let view = definition.view()
  guard view.function_.view() is Cfun(body) else { return None }
  let environment = VcEnvironment::new(context, pmodule)
  environment.configure_recursive_context(definitions, definition)
  generate_routine_vc_in_environment(
    environment,
    view.symbol,
    view.function_.cty(),
    body,
    options,
  )
}

///|
pub fn generate_module_with_support(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
  integer_theory : @theory.Theory,
  well_founded_theory : @theory.Theory,
) -> @mlw.Pmodule raise {
  generate_module_with_support_and_options(
    context,
    pmodule,
    integer_theory,
    well_founded_theory,
    VcOptions::classical(),
  )
}

///|
pub fn generate_module_with_support_and_options(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
  integer_theory : @theory.Theory,
  well_founded_theory : @theory.Theory,
  options : VcOptions,
) -> @mlw.Pmodule raise {
  let view = pmodule.view()
  let supported_theory = view.pure_theory
    .append_hidden_use(context, integer_theory, None)
    .append_hidden_use(context, well_founded_theory, None)
  generate_module_with_options(
    context,
    @mlw.Pmodule::trusted_new_with_dependencies(
      view.key,
      supported_theory,
      view.items,
      view.export_namespace,
      view.dependencies,
    ),
    options,
  )
}

///|
pub fn generate_routine_module_with_support_and_options(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
  integer_theory : @theory.Theory,
  well_founded_theory : @theory.Theory,
  options : VcOptions,
) -> @mlw.Pmodule raise {
  let view = pmodule.view()
  let supported_theory = view.pure_theory
    .append_hidden_use(context, integer_theory, None)
    .append_hidden_use(context, well_founded_theory, None)
  generate_selected_module_with_options(
    context,
    @mlw.Pmodule::trusted_new_with_dependencies(
      view.key,
      supported_theory,
      view.items,
      view.export_namespace,
      view.dependencies,
    ),
    options,
    false,
    true,
  )
}

///|
pub fn generate_type_module(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
) -> @mlw.Pmodule raise {
  generate_selected_module_with_options(
    context,
    pmodule,
    VcOptions::classical(),
    true,
    false,
  )
}

///|
pub fn generate_module(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
) -> @mlw.Pmodule raise {
  generate_module_with_options(context, pmodule, VcOptions::classical())
}

///|
priv struct ProgramVcBoundary {
  item_boundary : Int
  namespace_path : Array[Bytes]
}

///|
priv struct ProgramVcBoundaries {
  routines : Map[@mlw.RoutineSymbol, ProgramVcBoundary]
  types : Map[@mlw.ProgramTypeSymbol, ProgramVcBoundary]
}

///|
priv struct ProgramVcBoundaryScanner {
  theory_items : ArrayView[@theory.TheoryItem]
  mut cursor : Int
  boundaries : ProgramVcBoundaries
}

///|
fn declarations_have_same_identity(
  left : @logic.Decl,
  right : @logic.Decl,
) -> Bool {
  let left_symbols = left.introduced_symbols()
  let right_symbols = right.introduced_symbols()
  if left_symbols.length() != right_symbols.length() {
    return false
  }
  for index, symbol in left_symbols {
    if symbol != right_symbols[index] {
      return false
    }
  }
  true
}

///|
fn ProgramVcBoundaryScanner::consume_declaration(
  self : ProgramVcBoundaryScanner,
  declaration : @logic.Decl,
) -> Unit raise VcError {
  for index = self.cursor; index < self.theory_items.length(); index = index + 1 {
    if self.theory_items[index] is TheoryDecl(candidate) &&
      declarations_have_same_identity(candidate, declaration) {
      self.cursor = index + 1
      return
    }
  }
  fail_vc(
    InvariantFailure,
    None,
    "program declaration lost its pure-theory boundary",
  )
}

///|
fn ProgramVcBoundaryScanner::consume_meta(
  self : ProgramVcBoundaryScanner,
  meta : @theory.Meta,
) -> Unit raise VcError {
  let name = meta.view().name
  for index = self.cursor; index < self.theory_items.length(); index = index + 1 {
    if self.theory_items[index] is TheoryMeta(candidate) &&
      candidate.view().name == name {
      self.cursor = index + 1
      return
    }
  }
  fail_vc(
    InvariantFailure,
    None,
    "program declaration lost its pure-theory meta boundary",
  )
}

///|
fn ProgramVcBoundaryScanner::consume_use(
  self : ProgramVcBoundaryScanner,
  key : @theory.TheoryKey,
) -> Unit {
  for index = self.cursor; index < self.theory_items.length(); index = index + 1 {
    if self.theory_items[index] is TheoryUse(candidate) && candidate == key {
      self.cursor = index + 1
      return
    }
  }
  // Repeated module uses are retained in the program item stream even when
  // the pure theory has already deduplicated the corresponding use item.
}

///|
fn ProgramVcBoundaryScanner::consume_clone(
  self : ProgramVcBoundaryScanner,
  witness : @mlw.ProgramCloneWitness,
) -> Unit raise VcError {
  let source = witness.view().source
  for index = self.cursor; index < self.theory_items.length(); index = index + 1 {
    if self.theory_items[index] is TheoryClone(candidate) {
      let view = candidate.view()
      if view.source == source &&
        view.source_item_identity == index.reinterpret_as_uint() {
        self.cursor = index + 1
        return
      }
    }
  }
  fail_vc(InvariantFailure, None, "program clone lost its pure-theory boundary")
}

///|
fn ProgramVcBoundaryScanner::scan_declaration(
  self : ProgramVcBoundaryScanner,
  declaration : @mlw.ProgramDeclaration,
  namespace_path : ArrayView[Bytes],
) -> Unit raise VcError {
  let boundary : ProgramVcBoundary = {
    item_boundary: self.cursor,
    namespace_path: namespace_path.to_owned(),
  }
  match declaration {
    PDtype(declarations, _, _) =>
      for entry in declarations {
        self.boundaries.types[entry.view().symbol] = boundary
      }
    PDlet(symbol, _, _, _) => self.boundaries.routines[symbol] = boundary
    PDrec(definitions, _, _) =>
      for definition in definitions {
        self.boundaries.routines[definition.view().symbol] = boundary
      }
    PDpure(_, _) | PDvar(_, _, _, _) | PDexn(_, _, _) => ()
  }
  for pure in declaration.pure_declarations() {
    self.consume_declaration(pure)
  }
  for meta in declaration.metas() {
    self.consume_meta(meta)
  }
}

///|
fn ProgramVcBoundaryScanner::scan_items(
  self : ProgramVcBoundaryScanner,
  items : ArrayView[@mlw.ModuleItem],
  namespace_path : ArrayView[Bytes],
) -> Unit raise VcError {
  for item in items {
    match item {
      Udecl(declaration) => self.scan_declaration(declaration, namespace_path)
      Uuse(key) => self.consume_use(key)
      Uclone(witness) => self.consume_clone(witness)
      Umeta(meta) => self.consume_meta(meta)
      Uscope(name, nested) => {
        let nested_path = namespace_path.to_owned()
        nested_path.push(name)
        self.scan_items(nested, nested_path)
      }
    }
  }
}

///|
fn program_vc_boundaries(
  pmodule : @mlw.Pmodule,
) -> ProgramVcBoundaries raise VcError {
  let boundaries : ProgramVcBoundaries = { routines: Map([]), types: Map([]) }
  let view = pmodule.view()
  let scanner : ProgramVcBoundaryScanner = {
    theory_items: view.pure_theory.view().items,
    cursor: 0,
    boundaries,
  }
  scanner.scan_items(view.items, [])
  boundaries
}

///|
pub fn generate_module_with_options(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
  options : VcOptions,
) -> @mlw.Pmodule raise {
  generate_selected_module_with_options(context, pmodule, options, true, true)
}

///|
fn generate_selected_module_with_options(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
  options : VcOptions,
  generate_types : Bool,
  generate_routines : Bool,
) -> @mlw.Pmodule raise {
  let view = pmodule.view()
  if !context.contains(pmodule.context_anchor()) {
    fail_vc(
      ContextMismatch,
      None,
      "VC generator and program module belong to different contexts",
    )
  }
  let clone_insertions : Array[(Int, Array[Bytes], Array[@logic.Decl])] = []
  let suppressed_routines : Map[@mlw.RoutineSymbol, Unit] = Map([])
  let suppressed_types : Map[@mlw.ProgramTypeSymbol, Unit] = Map([])
  let boundaries = program_vc_boundaries(pmodule)
  collect_clone_vc_controls(view.items, suppressed_routines, suppressed_types)
  let items = generate_module_items(
    context,
    pmodule,
    view.items,
    options,
    suppressed_routines,
    suppressed_types,
    boundaries,
    clone_insertions,
    [],
    generate_types,
    generate_routines,
  )
  if clone_insertions.is_empty() {
    return pmodule
  }
  let ordered_theory = view.pure_theory.insert_declarations_at_item_boundaries(
    context,
    clone_insertions,
    None,
  )
  @mlw.Pmodule::trusted_new_with_dependencies(
    view.key,
    ordered_theory,
    items,
    view.export_namespace,
    view.dependencies,
  )
}

///|
fn append_vc_insertion(
  insertions : Array[(Int, Array[Bytes], Array[@logic.Decl])],
  boundary : ProgramVcBoundary,
  declaration : @logic.Decl,
) -> Unit {
  for insertion in insertions {
    if insertion.0 == boundary.item_boundary &&
      insertion.1 == boundary.namespace_path {
      insertion.2.push(declaration)
      return
    }
  }
  insertions.push(
    (boundary.item_boundary, boundary.namespace_path, [declaration]),
  )
}

///|
fn collect_clone_vc_controls(
  items : ArrayView[@mlw.ModuleItem],
  suppressed_routines : Map[@mlw.RoutineSymbol, Unit],
  suppressed_types : Map[@mlw.ProgramTypeSymbol, Unit],
) -> Unit {
  for item in items {
    match item {
      Uclone(witness) => {
        for routine in witness.vc_suppressed_routines() {
          suppressed_routines[routine] = ()
        }
        for symbol in witness.vc_suppressed_types() {
          suppressed_types[symbol] = ()
        }
      }
      Uscope(_, nested) =>
        collect_clone_vc_controls(nested, suppressed_routines, suppressed_types)
      Udecl(_) | Uuse(_) | Umeta(_) => ()
    }
  }
}

///|
fn has_existing_type_vc(
  items : ArrayView[@mlw.ModuleItem],
  type_declaration : @mlw.ProgramTypeDeclaration,
) -> Bool {
  let type_symbol = type_declaration.view().symbol.view().logic_type.view()
  let goal_name = append_bytes(type_symbol.name, b"'vc")
  let source_span = type_symbol.origin.source_span()
  for item in items {
    if item is Udecl(PDpure(declarations, _)) {
      for declaration in declarations {
        if declaration.view() is Dprop(Pgoal, proposition, _) {
          let proposition_view = proposition.view()
          if proposition_view.name == goal_name &&
            proposition_view.origin.source_span() == source_span {
            return true
          }
        }
      }
    }
  }
  false
}

///|
fn generate_module_items(
  context : @identity.CompilationContext,
  pmodule : @mlw.Pmodule,
  source : ArrayView[@mlw.ModuleItem],
  options : VcOptions,
  suppressed_routines : Map[@mlw.RoutineSymbol, Unit],
  suppressed_types : Map[@mlw.ProgramTypeSymbol, Unit],
  boundaries : ProgramVcBoundaries,
  clone_insertions : Array[(Int, Array[Bytes], Array[@logic.Decl])],
  namespace_path : ArrayView[Bytes],
  generate_types : Bool,
  generate_routines : Bool,
) -> Array[@mlw.ModuleItem] raise {
  let items : Array[@mlw.ModuleItem] = []
  for item in source {
    match item {
      Udecl(PDtype(type_declarations, _, _)) => {
        if generate_types {
          for type_declaration in type_declarations {
            if suppressed_types.contains(type_declaration.view().symbol) ||
              has_existing_type_vc(source, type_declaration) {
              continue
            }
            match
              generate_type_vc(context, pmodule, type_declaration, options) {
              Some(declaration) => {
                guard boundaries.types.get(type_declaration.view().symbol)
                  is Some(boundary) else {
                  fail_vc(
                    InvariantFailure,
                    None,
                    "program type VC lost its pure-theory boundary",
                  )
                }
                append_vc_insertion(clone_insertions, boundary, declaration)
                items.push(Udecl(PDpure([declaration], [])))
              }
              None => ()
            }
          }
        }
        items.push(item)
      }
      Udecl(PDlet(routine, Cfun(cty, Some(body)), _, _)) => {
        if generate_routines && !suppressed_routines.contains(routine) {
          match
            generate_routine_vc_with_options(
              context, pmodule, routine, cty, body, options,
            ) {
            Some(declaration) => {
              guard boundaries.routines.get(routine) is Some(boundary) else {
                fail_vc(
                  InvariantFailure,
                  None,
                  "routine VC lost its pure-theory boundary",
                )
              }
              append_vc_insertion(clone_insertions, boundary, declaration)
              items.push(Udecl(PDpure([declaration], [])))
            }
            None => ()
          }
        }
        items.push(item)
      }
      Udecl(PDrec(definitions, _, _)) => {
        if generate_routines {
          for definition in definitions {
            if suppressed_routines.contains(definition.view().symbol) {
              continue
            }
            match
              generate_recursive_routine_vc(
                context, pmodule, definitions, definition, options,
              ) {
              Some(declaration) => {
                let routine = definition.view().symbol
                guard boundaries.routines.get(routine) is Some(boundary) else {
                  fail_vc(
                    InvariantFailure,
                    None,
                    "recursive routine VC lost its pure-theory boundary",
                  )
                }
                append_vc_insertion(clone_insertions, boundary, declaration)
                items.push(Udecl(PDpure([declaration], [])))
              }
              None => ()
            }
          }
        }
        items.push(item)
      }
      Uclone(witness) => {
        if generate_routines {
          for refinement in witness.vc_refinements() {
            match
              generate_routine_vc_with_options(
                context,
                pmodule,
                refinement.0,
                refinement.1,
                refinement.2,
                options,
              ) {
              Some(declaration) => {
                let clone_boundary : ProgramVcBoundary = {
                  item_boundary: refinement.3,
                  namespace_path: namespace_path.to_owned(),
                }
                append_vc_insertion(
                  clone_insertions, clone_boundary, declaration,
                )
                items.push(Udecl(PDpure([declaration], [])))
              }
              None => ()
            }
          }
        }
        items.push(item)
      }
      Uscope(name, nested) => {
        let nested_path = namespace_path.to_owned()
        nested_path.push(name)
        items.push(
          Uscope(
            name,
            generate_module_items(
              context, pmodule, nested, options, suppressed_routines, suppressed_types,
              boundaries, clone_insertions, nested_path, generate_types, generate_routines,
            ),
          ),
        )
      }
      _ => items.push(item)
    }
  }
  items
}
