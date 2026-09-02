// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
priv struct RecursiveEntryVariant {
  initial : @logic.Term
  relation : @logic.LSymbol?
}

///|
priv struct RecursiveVcTarget {
  internal_symbol : @mlw.RoutineSymbol
  decrease_symbol : @logic.LSymbol
  variants : Array[@mlw.ProgramVariant]
  entry_variants : Array[RecursiveEntryVariant]
}

///|
priv struct RecursiveVcContext {
  targets : Array[RecursiveVcTarget]
  current_variants : Array[RecursiveEntryVariant]
  current_variant_oldies : Array[@mlw.OldSnapshot]
}

///|
priv struct VcEnvironment {
  context : @identity.CompilationContext
  known : @logic.KnownMap
  pure_theory : @theory.Theory
  program_space : @mlw.ProgramNamespace
  equality : @logic.LSymbol
  boolean_true : @logic.Term
  boolean_false : @logic.Term
  unit_value : @logic.Term
  integer_le : @logic.LSymbol?
  integer_lt : @logic.LSymbol?
  integer_ge : @logic.LSymbol?
  integer_gt : @logic.LSymbol?
  integer_plus : @logic.LSymbol?
  integer_minus : @logic.LSymbol?
  accessibility : @logic.LSymbol?
  well_founded : @logic.LSymbol?
  function_type : @logic.TypeSymbol?
  higher_order_apply : @logic.LSymbol?
  validity : @logic.LSymbol
  mut divergent : Bool
  mut keep_trace : Bool
  mut evaluate_matches : Bool
  mut recursive_targets : Array[RecursiveVcTarget]
  mut current_variants : Array[RecursiveEntryVariant]
  mut current_variant_oldies : Array[@mlw.OldSnapshot]
  mut next_exception : Int
}

///|
fn imported_theory(
  pmodule : @mlw.Pmodule,
  path : ArrayView[Bytes],
  name : BytesView,
) -> @theory.Theory? {
  for theory in pmodule.pure_theory().used_theories() {
    let key = theory.key().view()
    if key.path == path && key.name[:] == name {
      return Some(theory)
    }
  }
  None
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
  let integer_symbols = match imported_theory(pmodule, [b"int"], b"Int") {
    Some(theory) => {
      let imported_space = theory.export_namespace()
      (
        Some(imported_space.find_logic([b"infix <="], None)),
        Some(imported_space.find_logic([b"infix <"], None)),
        Some(imported_space.find_logic([b"infix >="], None)),
        Some(imported_space.find_logic([b"infix >"], None)),
        Some(imported_space.find_logic([b"infix +"], None)),
        Some(imported_space.find_logic([b"infix -"], None)),
      )
    }
    None => (None, None, None, None, None, None)
  }
  let well_founded_symbols = match
    imported_theory(pmodule, [b"why3", b"WellFounded"], b"WellFounded") {
    Some(theory) => {
      let imported_space = theory.export_namespace()
      (
        Some(imported_space.find_logic([b"acc"], None)),
        Some(imported_space.find_logic([b"well_founded"], None)),
        Some(imported_space.find_type([b"infix ->"], None)),
        Some(imported_space.find_logic([b"infix @"], None)),
      )
    }
    None => (None, None, None, None)
  }
  let validity_origin = @identity.Origin::generated(
    @identity.Wp,
    b"valid",
    None,
    [],
  )
  let validity_parameter = @logic.TyVarSymbol::new(
    context, b"a", validity_origin,
  )
  let validity = @logic.LSymbol::new_predicate(
    context,
    b"valid",
    validity_origin,
    [@logic.Ty::variable(validity_parameter)],
    None,
  )
  {
    context,
    known: pmodule.pure_known(),
    pure_theory: pmodule.pure_theory(),
    program_space: pmodule.export_namespace(),
    equality: pure_space.find_logic([b"infix ="], None),
    boolean_true,
    boolean_false,
    unit_value,
    integer_le: integer_symbols.0,
    integer_lt: integer_symbols.1,
    integer_ge: integer_symbols.2,
    integer_gt: integer_symbols.3,
    integer_plus: integer_symbols.4,
    integer_minus: integer_symbols.5,
    accessibility: well_founded_symbols.0,
    well_founded: well_founded_symbols.1,
    function_type: well_founded_symbols.2,
    higher_order_apply: well_founded_symbols.3,
    validity,
    divergent: false,
    keep_trace: true,
    evaluate_matches: true,
    recursive_targets: [],
    current_variants: [],
    current_variant_oldies: [],
    next_exception: 0,
  }
}

///|
fn VcEnvironment::configure_options(
  self : VcEnvironment,
  options : VcOptions,
  body : @mlw.Expr?,
) -> Unit {
  self.keep_trace = options.keeps_trace() &&
    !(match body {
      Some(expression) =>
        expression
        .attributes()
        .any(attribute => attribute == b"vc:do_not_keep_trace")
      None => false
    })
  self.evaluate_matches = options.evaluates_matches()
}

///|
fn VcEnvironment::recursive_context(self : VcEnvironment) -> RecursiveVcContext {
  {
    targets: self.recursive_targets.copy(),
    current_variants: self.current_variants.copy(),
    current_variant_oldies: self.current_variant_oldies.copy(),
  }
}

///|
fn VcEnvironment::restore_recursive_context(
  self : VcEnvironment,
  context : RecursiveVcContext,
) -> Unit {
  self.recursive_targets = context.targets
  self.current_variants = context.current_variants
  self.current_variant_oldies = context.current_variant_oldies
}

///|
fn VcEnvironment::configure_recursive_context(
  self : VcEnvironment,
  definitions : ArrayView[@mlw.RecursiveDefinition],
  current : @mlw.RecursiveDefinition,
) -> Unit raise {
  let cty = current.view().function_.cty().view()
  let candidates = cty.arguments.to_owned() + cty.effect.view().reads.to_owned()
  let variants = current.view().variants
  let oldified : Array[@mlw.PVariable] = []
  for candidate in candidates {
    let view = candidate.view()
    if !view.ity.is_pure() &&
      !oldified.any(existing => existing == candidate) &&
      variants.any(variant => {
        variant.view().term
        .free_variables()
        .any(symbol => symbol == view.pure_symbol)
      }) {
      oldified.push(candidate)
    }
  }
  oldified.sort_by((left, right) => {
    right.view().pure_symbol
    .semantic_id()
    .local_id()
    .compare(left.view().pure_symbol.semantic_id().local_id())
  })
  let current_variant_oldies : Array[@mlw.OldSnapshot] = []
  let mut substitution = @logic.TermSubstitution::new()
  for original in oldified {
    let span = variants[0].view().term.source_span()
    let snapshot = original.trusted_old_snapshot(self.context, span)
    current_variant_oldies.push(@mlw.OldSnapshot::new(snapshot, original, span))
    substitution = substitution.bind(
      original.view().pure_symbol,
      @logic.Term::variable(snapshot.view().pure_symbol),
      span,
    )
  }
  let current_variants = variants.map(variant => {
    let view = variant.view()
    guard view.term.ty() is Some(_) else {
      abort("validated recursive variant lost its value type")
    }
    {
      initial: if current_variant_oldies.is_empty() {
        view.term
      } else {
        substitution.apply(self.context, view.term, view.term.source_span())
      },
      relation: view.relation,
    }
  })
  let targets = self.recursive_targets.copy()
  for definition in definitions {
    let view = definition.view()
    guard view.internal_symbol.view().cty.view().preconditions is [decrease, ..] &&
      decrease.view() is Tapp(decrease_symbol, _, _) else {
      fail_vc(
        InvariantFailure,
        None,
        "recursive internal symbol lost its decrease predicate",
      )
    }
    targets.push({
      internal_symbol: view.internal_symbol,
      decrease_symbol,
      variants: view.variants.to_owned(),
      entry_variants: current_variants.copy(),
    })
  }
  self.recursive_targets = targets
  self.current_variants = current_variants
  self.current_variant_oldies = current_variant_oldies
}

///|
fn VcEnvironment::fresh_exception_index(self : VcEnvironment) -> Int {
  self.next_exception = self.next_exception + 1
  self.next_exception
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
