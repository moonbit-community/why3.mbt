// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv struct ProgramLocal {
  variable : @mlw.PVariable
  delayed : DLocal
  reference : Bool
}

///|
priv struct ProgramParameterSource {
  span : @parser.Span
  ident : @parser.Ident?
  ghost : Bool
  ty : @parser.Pty?
  inferred_ity : @mlw.Ity?
}

///|
/// A routine contract is deliberately retained after parameter typing.  The
/// pre-state scope is sufficient for requires; each ensures branch extends a
/// fresh copy with its result symbol only after the result type is known.
priv struct PendingSpec {
  source : @parser.Spec
  arguments : Array[@mlw.PVariable]
  parameter_scope : Array[(Bytes, ProgramLocal)]
  logic_mappings : Array[(Bytes, ProgramLocal)]
  oldies : Array[@mlw.OldSnapshot]
  at_values : Array[DAtValue]
  at_labels : Array[Bytes]
}

///|
priv struct ProgramDecoration {
  location : @identity.SourceSpan
  attributes : Array[Bytes]
}

///|
priv struct ProgramTyping {
  context : @identity.CompilationContext
  environment : @environment.Environment
  library_path : Array[Bytes]
  file_modules : Array[(Bytes, @mlw.Pmodule)]
  pure : PureTyping
  mut at_values : Array[DAtValue]
  mut at_labels : Array[Bytes]
  mut at_program_variables : Array[@mlw.PVariable]
  snapshot_placeholders : Array[
    (@logic.VSymbol, @mlw.PVariable, @mlw.PVariable),
  ]
  mut snapshot_replacements : Array[(@logic.VSymbol, @mlw.PVariable)]
  mut ghost_context : Bool
}

///|
fn ProgramTyping::new(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  library_path? : ArrayView[Bytes] = [],
  file_theories? : ArrayView[(Bytes, @theory.Theory)] = [],
  file_modules? : ArrayView[(Bytes, @mlw.Pmodule)] = [],
) -> ProgramTyping {
  {
    context,
    environment,
    library_path: library_path.to_owned(),
    file_modules: file_modules.to_owned(),
    pure: PureTyping::new(context, environment, library_path~, file_theories~),
    at_values: [],
    at_labels: [],
    at_program_variables: [],
    snapshot_placeholders: [],
    snapshot_replacements: [],
    ghost_context: false,
  }
}

///|
fn program_origin(decoration : ProgramDecoration) -> @identity.Origin {
  @identity.Origin::user(b"", Some(decoration.location), [])
}

///|
fn default_program_decoration(expression : @parser.Expr) -> ProgramDecoration {
  { location: source_span(expression.span), attributes: [] }
}

///|
fn find_program_local(
  locals : ArrayView[(Bytes, ProgramLocal)],
  name : BytesView,
) -> ProgramLocal? {
  for index = locals.length() - 1; index >= 0; index = index - 1 {
    if locals[index].0[:] == name {
      return Some(locals[index].1)
    }
  }
  None
}

///|
fn program_logic_scope(
  locals : ArrayView[(Bytes, ProgramLocal)],
) -> (Array[(Bytes, DLocal)], Array[(Int, @logic.VSymbol)]) {
  let bindings : Array[(Bytes, DLocal)] = []
  let values : Array[(Int, @logic.VSymbol)] = []
  for entry in locals {
    bindings.push((entry.0, entry.1.delayed))
    values.push((entry.1.delayed.id, entry.1.variable.view().pure_symbol))
  }
  (bindings, values)
}

///|
fn ProgramTyping::program_logic_mappings(
  self : ProgramTyping,
  program_space : @mlw.ProgramNamespace,
  fallback_span : @parser.Span,
) -> Array[(Bytes, ProgramLocal)] raise {
  let mappings : Array[(Bytes, ProgramLocal)] = []
  for entry in program_space.view().routines {
    guard entry.1.view().logic is RLpv(variable) else { continue }
    if !mappings.any(existing => existing.1.variable == variable) {
      mappings.push(
        (entry.0, self.program_local_from_variable(variable, fallback_span)),
      )
    }
  }
  mappings
}

///|
fn program_spec_logic_scope(
  pending : PendingSpec,
) -> (Array[(Bytes, DLocal)], Array[(Int, @logic.VSymbol)]) {
  let locals = pending.logic_mappings.copy()
  locals.push_iter(pending.parameter_scope.iter())
  program_logic_scope(locals)
}

///|
fn program_spec_variables(
  pending : PendingSpec,
  snapshots : ArrayView[@mlw.PVariable],
) -> Array[@mlw.PVariable] {
  let locals = pending.logic_mappings.copy()
  locals.push_iter(pending.parameter_scope.iter())
  program_variables(locals, snapshots~)
}

///|
fn program_formula_reads(
  locals : ArrayView[(Bytes, ProgramLocal)],
  formula : @logic.Term,
  snapshots? : ArrayView[@mlw.PVariable] = [],
) -> Array[@mlw.PVariable] {
  let free = formula.free_variables()
  let reads = [
    for entry in locals if free.any(variable => {
      variable == entry.1.variable.view().pure_symbol
    }) => entry.1.variable
  ]
  for snapshot in snapshots {
    if free.any(variable => variable == snapshot.view().pure_symbol) &&
      !reads.any(existing => existing == snapshot) {
      reads.push(snapshot)
    }
  }
  reads
}

///|
fn program_variables(
  locals : ArrayView[(Bytes, ProgramLocal)],
  snapshots? : ArrayView[@mlw.PVariable] = [],
) -> Array[@mlw.PVariable] {
  let variables = [ for entry in locals => entry.1.variable ]
  for snapshot in snapshots {
    if !variables.any(existing => existing == snapshot) {
      variables.push(snapshot)
    }
  }
  variables
}

///|
fn semantic_program_mask(mask : @parser.Mask) -> @mlw.ProgramMask {
  match mask {
    MaskVisible => @mlw.Visible
    MaskGhost => @mlw.Ghost
    MaskTuple(items) => @mlw.Tuple(items.map(semantic_program_mask))
  }
}

///|
fn program_ity_is_reference(ity : @mlw.Ity) -> Bool {
  match ity.view() {
    ItyVar(_) => false
    ItyApp(symbol, _, _) => symbol.view().logic_type.name() == b"ref"
    ItyReg(region) => region.view().symbol.view().logic_type.name() == b"ref"
  }
}

///|
fn program_ity_reference_content(ity : @mlw.Ity) -> @mlw.Ity? {
  match ity.view() {
    ItyApp(symbol, [content], _) if symbol.view().logic_type.name() == b"ref" =>
      Some(content)
    ItyReg(region) if region.view().symbol.view().logic_type.name() == b"ref" =>
      match region.view().arguments {
        [content] => Some(content)
        _ => None
      }
    _ => None
  }
}

///|
fn program_ity_is_default_numeric(ity : @mlw.Ity) -> Bool {
  match ity.view() {
    ItyApp(symbol, _, _) => {
      let name = symbol.view().logic_type.name()
      name == b"int" || name == b"real"
    }
    ItyVar(_) | ItyReg(_) => false
  }
}

///|
fn ProgramTyping::type_program_invariant(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  invariant : @parser.Invariant,
  fallback_span : @parser.Span,
  logical_override? : (@mlw.PVariable, @mlw.PVariable)? = None,
) -> Array[@logic.Term] raise {
  let expanded = self.program_logic_mappings(program_space, fallback_span)
  expanded.push_iter(locals.iter())
  let (logic_locals, logic_values) = program_logic_scope(expanded)
  if logical_override is Some((source, replacement)) {
    let source_symbol = source.view().pure_symbol
    let replacement_type = self.pure.delayed.known(
      replacement.view().ity.to_ty(None),
      None,
    )
    let mut source_local_id = -1
    for entry in locals {
      if entry.1.variable == source {
        source_local_id = entry.1.delayed.id
        break
      }
    }
    for index = 0; index < logic_locals.length(); index = index + 1 {
      if logic_locals[index].1.id == source_local_id {
        logic_locals[index] = (
          logic_locals[index].0,
          { ..logic_locals[index].1, ty: replacement_type },
        )
      }
    }
    for index = 0; index < logic_values.length(); index = index + 1 {
      if logic_values[index].1 == source_symbol {
        logic_values[index] = (
          logic_values[index].0,
          replacement.view().pure_symbol,
        )
      }
    }
  }
  [
    for formula in invariant.terms => {
      self.pure.formula(
        pure_space,
        logic_locals,
        logic_values,
        formula,
        at_values=self.at_values,
        at_labels=self.at_labels,
        at_resolver=entry => self.materialize_at_value(entry),
      )
    }
  ]
}

///|
fn ProgramTyping::type_program_variants(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  variants : @parser.Variant,
  fallback_span : @parser.Span,
) -> Array[@mlw.ProgramVariant] raise {
  let expanded = self.program_logic_mappings(program_space, fallback_span)
  expanded.push_iter(locals.iter())
  let (logic_locals, logic_values) = program_logic_scope(expanded)
  [
    for item in variants.items => {
      let delayed = self.pure.type_term(pure_space, logic_locals, item.0)
      guard delayed.result_type is Some(result_type) else {
        @logic.fail_type(
          TypeMismatch,
          Some(source_span(item.0.span)),
          "termination variant must be a value term",
        )
      }
      let term = self.pure.value(
        pure_space,
        logic_locals,
        logic_values,
        item.0,
        result_type,
        at_values=self.at_values,
        at_labels=self.at_labels,
        at_resolver=entry => self.materialize_at_value(entry),
      )
      let relation = match item.1 {
        Some(relation) =>
          Some(
            pure_space.find_logic(
              qualid_segments(relation),
              Some(qualid_span(relation)),
            ),
          )
        None => None
      }
      @mlw.ProgramVariant::new(term, relation, Some(source_span(item.0.span)))
    }
  ]
}

///|
fn ProgramTyping::program_ity(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  source : @parser.Pty,
  span : @identity.SourceSpan?,
) -> @mlw.Ity raise {
  match source {
    PTpure(nested) =>
      return self.program_ity(pure_space, program_space, nested, span).purify()
    PTparen(nested) =>
      return self.program_ity(pure_space, program_space, nested, span)
    PTscope(scope, nested) => {
      let scope_span = Some(qualid_span(scope))
      return self.program_ity(
        pure_space.open_scope(qualid_segments(scope), scope_span),
        program_space.open_scope(qualid_segments(scope), scope_span),
        nested,
        span,
      )
    }
    PTtuple([]) => {
      let unit_symbol = pure_space.find_type([b"unit"], span)
      return @mlw.Ity::from_ty(
        program_space,
        @logic.Ty::app(unit_symbol, [], span),
        span,
      )
    }
    PTtuple(arguments) =>
      return @mlw.Ity::app(
        program_space.find_type([tuple_type_name(arguments.length())], span),
        arguments.map(argument => {
          self.program_ity(pure_space, program_space, argument, span)
        }),
        span,
      )
    PTref(arguments) =>
      return @mlw.Ity::instantiate(
        program_space.find_type([b"ref"], span),
        arguments.map(argument => {
          self.program_ity(pure_space, program_space, argument, span)
        }),
        [],
        span,
      )
    PTarrow(parameter, result) =>
      return @mlw.Ity::app(
        program_space.find_type([b"infix ->"], span),
        [
          self.program_ity(pure_space, program_space, parameter, span),
          self.program_ity(pure_space, program_space, result, span),
        ],
        span,
      )
    _ => ()
  }
  let delayed = self.pure.dty_of_pty(pure_space, source)
  let ty = self.pure.delayed.finalize_pure(delayed, span)
  @mlw.Ity::from_ty(program_space, ty, span)
}

///|
fn anonymous_semantic_name(
  name : BytesView,
  span : @parser.Span,
  attributes : ArrayView[Bytes],
) -> @theory.SemanticName {
  @theory.SemanticName::new(name, attributes, Some(source_span(span)))
}

///|
fn ProgramTyping::make_program_local(
  self : ProgramTyping,
  ident : @parser.Ident?,
  fallback_span : @parser.Span,
  ity : @mlw.Ity,
  ghost : Bool,
) -> ProgramLocal raise {
  let name = match ident {
    Some(ident) => semantic_name(ident)
    None => anonymous_semantic_name(b"_", fallback_span, [])
  }
  let variable = @mlw.PVariable::trusted_new(
    self.context,
    name,
    ity,
    ghost,
    Some(source_span(fallback_span)),
  )
  let delayed = self.pure.make_local(
    ident,
    fallback_span,
    self.pure.delayed.known(ity.to_ty(Some(source_span(fallback_span))), None),
  )
  let reference = match ident {
    Some(ident) => ident_has_reference_marker(ident)
    None => false
  }
  if reference && !program_ity_is_reference(ity) {
    @logic.fail_type(
      TypeMismatch,
      Some(source_span(fallback_span)),
      "reference marker requires a reference-typed program variable",
    )
  }
  { variable, delayed, reference }
}

///|
fn ProgramTyping::register_snapshot_placeholder(
  self : ProgramTyping,
  snapshot : @mlw.PVariable,
  original : @mlw.PVariable,
) -> Unit {
  let symbol = snapshot.view().pure_symbol
  if !self.snapshot_placeholders.any(entry => entry.0 == symbol) {
    self.snapshot_placeholders.push((symbol, snapshot, original))
  }
}

///|
fn ProgramTyping::snapshot_replacement(
  self : ProgramTyping,
  placeholder : @logic.VSymbol,
) -> @mlw.PVariable? {
  for entry in self.snapshot_replacements {
    if entry.0 == placeholder {
      return Some(entry.1)
    }
  }
  None
}

///|
fn ProgramTyping::materialize_at_value(
  self : ProgramTyping,
  entry : DAtValue,
) -> @logic.VSymbol raise {
  match self.snapshot_replacement(entry.value) {
    Some(snapshot) => return snapshot.view().pure_symbol
    None => ()
  }
  for placeholder in self.snapshot_placeholders {
    if placeholder.0 == entry.value {
      let view = placeholder.1.view()
      let snapshot = @mlw.PVariable::trusted_new(
        self.context,
        view.name,
        view.ity,
        view.ghost,
        view.name.view().source_span,
      )
      self.snapshot_replacements.push((entry.value, snapshot))
      return snapshot.view().pure_symbol
    }
  }
  entry.value
}

///|
fn ProgramTyping::materialized_snapshot(
  self : ProgramTyping,
  snapshot : @mlw.PVariable,
) -> @mlw.PVariable {
  match self.snapshot_replacement(snapshot.view().pure_symbol) {
    Some(replacement) => replacement
    None => snapshot
  }
}

///|
fn ProgramTyping::materialized_snapshots(
  self : ProgramTyping,
  snapshots : ArrayView[@mlw.PVariable],
) -> Array[@mlw.PVariable] {
  [
    for snapshot in snapshots => self.materialized_snapshot(snapshot)
  ]
}

///|
fn ProgramTyping::materialized_oldies(
  self : ProgramTyping,
  oldies : ArrayView[@mlw.OldSnapshot],
) -> Array[@mlw.OldSnapshot] raise {
  [
    for oldie in oldies => {
      let view = oldie.view()
      @mlw.OldSnapshot::new(
        self.materialized_snapshot(view.snapshot),
        view.original,
        None,
      )
    }
  ]
}

///|
fn ProgramTyping::program_local_from_variable(
  self : ProgramTyping,
  variable : @mlw.PVariable,
  fallback_span : @parser.Span,
) -> ProgramLocal raise {
  let span = Some(source_span(fallback_span))
  let name = variable.view().name.view()
  let reference = name.attributes.any(attribute => {
    attribute == b"mlw:reference_var"
  })
  let ident = @parser.Ident::{
    name: name.name,
    attributes: name.attributes.map(attribute => @parser.Text(attribute)),
    span: fallback_span,
  }
  let delayed = self.pure.make_local(
    Some(ident),
    fallback_span,
    self.pure.delayed.known(variable.view().ity.to_ty(span), span),
  )
  { variable, delayed, reference }
}

///|
fn ProgramTyping::visible_program_locals(
  self : ProgramTyping,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  fallback_span : @parser.Span,
) -> Array[(Bytes, ProgramLocal)] raise {
  let visible : Array[(Bytes, ProgramLocal)] = []
  for entry in program_space.view().variables {
    if !visible.any(binding => binding.1.variable == entry.1) {
      visible.push(
        (entry.0, self.program_local_from_variable(entry.1, fallback_span)),
      )
    }
  }
  for entry in locals {
    if !visible.any(binding => binding.1.variable == entry.1.variable) {
      visible.push(entry)
    }
  }
  visible
}

///|
fn ProgramTyping::extend_pattern_locals(
  self : ProgramTyping,
  locals : ArrayView[(Bytes, ProgramLocal)],
  pattern : @mlw.ProgramPattern,
  fallback_span : @parser.Span,
) -> Array[(Bytes, ProgramLocal)] raise {
  let nested = locals.to_owned()
  for variable in pattern.view().variables {
    nested.push(
      (
        variable.view().name.view().name,
        self.program_local_from_variable(variable, fallback_span),
      ),
    )
  }
  nested
}

///|
fn[A] ProgramTyping::program_record_layout(
  self : ProgramTyping,
  program_space : @mlw.ProgramNamespace,
  fields : ArrayView[(@parser.QualId, A)],
  span : @identity.SourceSpan?,
) -> (@mlw.RoutineSymbol, Array[@mlw.RoutineSymbol], Map[@mlw.PVariable, A]) raise {
  ignore(self)
  if fields.is_empty() {
    @logic.fail_type(
      BadRecordField,
      span,
      "program record requires at least one field",
    )
  }
  let values : Map[@mlw.PVariable, A] = Map([])
  let mut owner : @mlw.ProgramTypeSymbol? = None
  let first_path = qualid_segments(fields[0].0)
  for entry in fields {
    let routine = program_space.find_routine(
      qualid_segments(entry.0),
      Some(qualid_span(entry.0)),
    )
    let routine_view = routine.view()
    guard routine_view.field is Some(field) else {
      @logic.fail_type(
        BadRecordField,
        Some(qualid_span(entry.0)),
        "program record name is not a field",
      )
    }
    let cty = routine_view.cty.view()
    guard cty.arguments is [argument] &&
      program_ity_head_symbol(argument.view().ity) is Some(candidate) else {
      @logic.fail_type(
        BadRecordField,
        Some(qualid_span(entry.0)),
        "program record field has an invalid projection signature",
      )
    }
    match owner {
      None => owner = Some(candidate)
      Some(existing) =>
        if existing != candidate {
          @logic.fail_type(
            BadRecordField,
            Some(qualid_span(entry.0)),
            "program record fields belong to different record types",
          )
        }
    }
    if values.contains(field) {
      @logic.fail_type(
        DuplicateRecordField,
        Some(qualid_span(entry.0)),
        "program record field is specified more than once",
      )
    }
    values[field] = entry.1
  }
  guard owner is Some(owner) else {
    abort("nonempty program record lost its owner type")
  }
  let constructor_path : Array[Bytes] = []
  for index = 0; index + 1 < first_path.length(); index = index + 1 {
    constructor_path.push(first_path[index])
  }
  let constructor_name = @buffer.Buffer()
  constructor_name.write_bytes(owner.view().logic_type.name())
  constructor_name.write_bytes(b"'mk")
  constructor_path.push(constructor_name.to_bytes())
  let constructor_routine = program_space.find_routine(constructor_path, span)
  if program_ity_head_symbol(constructor_routine.view().cty.view().result) !=
    Some(owner) {
    @logic.fail_type(
      BadRecordType,
      span,
      "program record constructor belongs to a different record type",
    )
  }
  let projections = constructor_routine.view().cty.view().arguments.map(field => {
    program_space.find_projection_by_field(field, span)
  })
  (constructor_routine, projections, values)
}

///|
fn ProgramTyping::program_prepattern(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  pattern : @parser.Pattern,
  inherited_ghost? : Bool = false,
) -> @mlw.PrePattern raise {
  ignore(self)
  match pattern.desc {
    Pwild => @mlw.PPwild
    Pvar(ident) => @mlw.PPvar(semantic_name(ident), inherited_ghost)
    Papp(constructor_path, arguments) =>
      @mlw.PPapp(
        program_space.find_routine(
          qualid_segments(constructor_path),
          Some(qualid_span(constructor_path)),
        ),
        arguments.map(argument => {
          self.program_prepattern(
            pure_space,
            program_space,
            argument,
            inherited_ghost~,
          )
        }),
      )
    Pas(inner, ident, ghost) =>
      @mlw.PPas(
        self.program_prepattern(
          pure_space,
          program_space,
          inner,
          inherited_ghost~,
        ),
        semantic_name(ident),
        inherited_ghost || ghost,
      )
    Por(left, right) =>
      @mlw.PPor(
        self.program_prepattern(
          pure_space,
          program_space,
          left,
          inherited_ghost~,
        ),
        self.program_prepattern(
          pure_space,
          program_space,
          right,
          inherited_ghost~,
        ),
      )
    Pscope(scope, inner) => {
      let scope_span = Some(qualid_span(scope))
      self.program_prepattern(
        pure_space.open_scope(qualid_segments(scope), scope_span),
        program_space.open_scope(qualid_segments(scope), scope_span),
        inner,
        inherited_ghost~,
      )
    }
    Pparen(inner) | Pcast(inner, _) =>
      self.program_prepattern(
        pure_space,
        program_space,
        inner,
        inherited_ghost~,
      )
    Pghost(inner) =>
      self.program_prepattern(
        pure_space,
        program_space,
        inner,
        inherited_ghost=true,
      )
    Ptuple(arguments) =>
      @mlw.PPapp(
        program_space.find_routine(
          [tuple_constructor_name(arguments.length())],
          Some(source_span(pattern.span)),
        ),
        arguments.map(argument => {
          self.program_prepattern(
            pure_space,
            program_space,
            argument,
            inherited_ghost~,
          )
        }),
      )
    Prec(fields) => {
      let semantic_span = Some(source_span(pattern.span))
      let (constructor_routine, projections, values) = self.program_record_layout(
        program_space, fields, semantic_span,
      )
      let arguments : Array[@mlw.PrePattern] = []
      for projection in projections {
        guard projection.view().field is Some(field) else {
          @logic.fail_type(
            BadRecordField,
            semantic_span,
            "program record projection has no field",
          )
        }
        match values.get(field) {
          Some(field_pattern) =>
            arguments.push(
              self.program_prepattern(
                pure_space,
                program_space,
                field_pattern,
                inherited_ghost~,
              ),
            )
          None => arguments.push(@mlw.PPwild)
        }
      }
      @mlw.PPapp(constructor_routine, arguments)
    }
  }
}

///|
fn ProgramTyping::prepare_spec(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  parameters : ArrayView[ProgramParameterSource],
  spec : @parser.Spec,
  inherited_ghost : Bool,
  fallback_span : @parser.Span,
  outer_scope? : ArrayView[(Bytes, ProgramLocal)] = [],
  reused_arguments? : ArrayView[@mlw.PVariable]? = None,
) -> PendingSpec raise {
  if reused_arguments is Some(reused) && reused.length() != parameters.length() {
    abort("reused routine signature has a different parameter arity")
  }
  let arguments : Array[@mlw.PVariable] = []
  let parameter_scope = outer_scope.to_owned()
  let parameter_names : Array[Bytes] = []
  for index, parameter in parameters {
    let span = Some(source_span(parameter.span))
    let binding = match reused_arguments {
      Some(reused) =>
        self.program_local_from_variable(reused[index], parameter.span)
      None => {
        let ity = match parameter.ty {
          Some(ty) => self.program_ity(pure_space, program_space, ty, span)
          None =>
            match parameter.inferred_ity {
              Some(ity) => ity
              None =>
                fail_invalid_input(
                  InvalidBinder,
                  ProgramTyping,
                  span,
                  "program parameters require explicit types or a function-valued context",
                )
            }
        }
        self.make_program_local(
          parameter.ident,
          parameter.span,
          ity,
          inherited_ghost || parameter.ghost,
        )
      }
    }
    arguments.push(binding.variable)
    if parameter.ident is Some(ident) {
      if parameter_names.any(name => name == ident.name) {
        @logic.fail_type(
          DuplicateBinder,
          Some(source_span(ident.span)),
          "program routine repeats a parameter name",
        )
      }
      parameter_names.push(ident.name)
      parameter_scope.push((ident.name, binding))
    }
  }
  let oldies : Array[@mlw.OldSnapshot] = []
  let at_values = self.at_values.copy()
  let at_labels = self.at_labels.copy()
  if !at_labels.any(label => label == b"'Old") {
    at_labels.push(b"'Old")
  }
  for entry in parameter_scope {
    let original = entry.1.variable
    if !original.view().ity.is_pure() {
      let snapshot = @mlw.PVariable::trusted_new(
        self.context,
        original.view().name,
        original.view().ity.purify(),
        true,
        original.view().name.view().source_span,
      )
      self.register_snapshot_placeholder(snapshot, original)
      oldies.push(@mlw.OldSnapshot::new(snapshot, original, None))
      at_values.push({
        local_id: entry.1.delayed.id,
        label: b"'Old",
        value: snapshot.view().pure_symbol,
      })
    }
  }
  {
    source: spec,
    arguments,
    parameter_scope,
    logic_mappings: self.program_logic_mappings(program_space, fallback_span),
    oldies,
    at_values,
    at_labels,
  }
}

///|
fn validate_program_spec_shape(
  spec : @parser.Spec,
  recursive? : Bool = false,
) -> Unit raise ElabError {
  if !recursive && !spec.variant.items.is_empty() {
    fail_invalid_input(
      InvalidSpecification,
      ProgramTyping,
      None,
      "termination variants require a recursive routine",
    )
  }
  if recursive && !spec.aliases.is_empty() {
    fail_invalid_input(
      InvalidSpecification,
      ProgramTyping,
      None,
      "recursive routines may not declare region aliases",
    )
  }
}

///|
fn same_program_variable_set(
  left : ArrayView[@mlw.PVariable],
  right : ArrayView[@mlw.PVariable],
) -> Bool {
  left.length() == right.length() &&
  left.all(value => right.any(candidate => candidate == value))
}

///|
fn same_program_exception_set(
  left : ArrayView[@mlw.XSymbol],
  right : ArrayView[@mlw.XSymbol],
) -> Bool {
  left.length() == right.length() &&
  left.all(value => right.any(candidate => candidate == value))
}

///|
fn program_write_target_covered(
  actual_region : @mlw.Region,
  actual_field : @mlw.PVariable?,
  allowed_region : @mlw.Region,
  allowed_field : @mlw.PVariable?,
  span : @identity.SourceSpan?,
) -> Bool raise {
  if actual_region == allowed_region {
    return match (actual_field, allowed_field) {
      (_, None) => true
      (Some(actual), Some(allowed)) => actual == allowed
      (None, Some(_)) => false
    }
  }
  let allowed_type = match allowed_field {
    Some(field) => allowed_region.member_ity(field, span)
    None => @mlw.Ity::region(allowed_region)
  }
  allowed_type.reachable_regions().any(region => region == actual_region)
}

///|
fn program_write_target_allowed(
  actual_region : @mlw.Region,
  actual_field : @mlw.PVariable?,
  allowed : ArrayView[@mlw.EffectWrite],
  span : @identity.SourceSpan?,
) -> Bool raise {
  for write in allowed {
    let view = write.view()
    if view.fields.is_empty() {
      if program_write_target_covered(
          actual_region,
          actual_field,
          view.region,
          None,
          span,
        ) {
        return true
      }
    } else {
      for field in view.fields {
        if program_write_target_covered(
            actual_region,
            actual_field,
            view.region,
            Some(field),
            span,
          ) {
          return true
        }
      }
    }
  }
  false
}

///|
fn program_writes_covered(
  actual : ArrayView[@mlw.EffectWrite],
  allowed : ArrayView[@mlw.EffectWrite],
  span : @identity.SourceSpan?,
) -> Bool raise {
  for write in actual {
    let view = write.view()
    if view.fields.is_empty() {
      if !program_write_target_allowed(view.region, None, allowed, span) {
        @logic.fail_type(
          TypeMismatch,
          span,
          "routine produces an unlisted whole-region write on \{view.region.view().name.view().name}",
        )
      }
    } else {
      for field in view.fields {
        if !program_write_target_allowed(
            view.region,
            Some(field),
            allowed,
            span,
          ) {
          @logic.fail_type(
            TypeMismatch,
            span,
            "routine produces an unlisted write on \{view.region.view().name.view().name}.\{field.view().name.view().name}",
          )
        }
      }
    }
  }
  true
}

///|
fn program_write_target_observed(
  allowed_region : @mlw.Region,
  allowed_field : @mlw.PVariable?,
  actual : ArrayView[@mlw.EffectWrite],
  span : @identity.SourceSpan?,
) -> Bool raise {
  for write in actual {
    let view = write.view()
    if view.fields.is_empty() {
      if program_write_target_covered(
          view.region,
          None,
          allowed_region,
          allowed_field,
          span,
        ) {
        return true
      }
    } else {
      for field in view.fields {
        if program_write_target_covered(
            view.region,
            Some(field),
            allowed_region,
            allowed_field,
            span,
          ) {
          return true
        }
      }
    }
  }
  false
}

///|
fn program_writes_observed(
  specified : ArrayView[@mlw.EffectWrite],
  actual : ArrayView[@mlw.EffectWrite],
  span : @identity.SourceSpan?,
) -> Bool raise {
  for write in specified {
    let view = write.view()
    if view.fields.is_empty() {
      if !program_write_target_observed(view.region, None, actual, span) {
        return false
      }
    } else {
      for field in view.fields {
        if !program_write_target_observed(
            view.region,
            Some(field),
            actual,
            span,
          ) {
          return false
        }
      }
    }
  }
  true
}

///|
fn diagnostic_program_writes(writes : ArrayView[@mlw.EffectWrite]) -> String {
  writes
  .map(write => {
    let view = write.view()
    let fields = view.fields.map(field => {
      field.view().name.view().name.to_string()
    })
    "rho#\{view.region.semantic_id().local_id()}:[\{fields.join(",")}]"
  })
  .join(";")
}

///|
fn validate_checked_program_effect(
  actual : @mlw.Effect,
  specified : @mlw.Effect,
  arguments : ArrayView[@mlw.PVariable],
  oldies : ArrayView[@mlw.OldSnapshot],
  span : @identity.SourceSpan?,
) -> Unit raise {
  let actual_view = actual.view()
  let specified_view = specified.view()
  let actual_reads = [
    for read in actual_view.reads if !arguments.any(argument => argument == read) &&
    !oldies.any(oldie => oldie.view().snapshot == read) => read
  ]
  let specified_reads = [
    for read in specified_view.reads if !arguments.any(argument => {
      argument == read
    }) &&
    !oldies.any(oldie => oldie.view().snapshot == read) => read
  ]
  if !same_program_variable_set(actual_reads, specified_reads) {
    @logic.fail_type(
      TypeMismatch,
      span,
      "routine reads differ from its checked reads clause",
    )
  }
  if !program_writes_observed(specified_view.writes, actual_view.writes, span) {
    @logic.fail_type(
      TypeMismatch,
      span,
      "routine writes differ from its checked writes clause (specified \{diagnostic_program_writes(specified_view.writes)}; actual \{diagnostic_program_writes(actual_view.writes)})",
    )
  }
  if !program_writes_covered(actual_view.writes, specified_view.writes, span) {
    @logic.fail_type(
      TypeMismatch,
      span,
      "routine produces an unlisted write effect",
    )
  }
  if !same_program_exception_set(actual_view.raises, specified_view.raises) {
    @logic.fail_type(
      TypeMismatch,
      span,
      "routine raises differ from its checked exceptional contract",
    )
  }
  if actual_view.termination != specified_view.termination {
    @logic.fail_type(
      TypeMismatch,
      span,
      "routine termination differs from its checked effect contract",
    )
  }
}

///|
fn ProgramTyping::type_preconditions(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  pending : PendingSpec,
) -> Array[@logic.Term] raise {
  let (locals, values) = program_spec_logic_scope(pending)
  [
    for condition in pending.source.preconditions => {
      let mut formula = self.pure.formula(
        pure_space,
        locals,
        values,
        condition,
        at_values=pending.at_values,
        at_labels=pending.at_labels,
        at_resolver=entry => self.materialize_at_value(entry),
      )
      // Why3 first finalizes `old` against this routine's entry snapshot and
      // then rebases a local routine's precondition to the immediately
      // surrounding entry snapshot. Keeping those two allocations distinct is
      // observable through identity-ordered semantic sets.
      let free = formula.free_variables()
      let mut substitution = @logic.TermSubstitution::new()
      for index, entry in pending.at_values {
        let current_snapshot = pending.oldies.any(oldie => {
          oldie.view().snapshot.view().pure_symbol == entry.value
        })
        if !current_snapshot {
          continue
        }
        guard self.snapshot_replacement(entry.value) is Some(current) &&
          free.any(variable => variable == current.view().pure_symbol) else {
          continue
        }
        let mut inherited : DAtValue? = None
        for previous_index = index - 1
            previous_index >= 0
            previous_index = previous_index - 1 {
          let previous = pending.at_values[previous_index]
          if previous.local_id == entry.local_id &&
            previous.label == entry.label {
            inherited = Some(previous)
            break
          }
        }
        match inherited {
          Some(previous) => {
            let replacement = self.materialize_at_value(previous)
            substitution = substitution.bind(
              current.view().pure_symbol,
              @logic.Term::variable(replacement),
              Some(source_span(condition.span)),
            )
          }
          None => ()
        }
      }
      formula = substitution.apply(
        self.context,
        formula,
        Some(source_span(condition.span)),
      )
      formula
    }
  ]
}

///|
fn ProgramTyping::post_result_pattern(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  pattern : @parser.Pattern,
  result : @mlw.Ity,
) -> (@parser.Ident?, @parser.Span) raise {
  match pattern.desc {
    Pvar(ident) => (Some(ident), pattern.span)
    Pwild => (None, pattern.span)
    Pparen(inner) | Pscope(_, inner) =>
      self.post_result_pattern(pure_space, program_space, inner, result)
    Pcast(inner, annotation) => {
      let annotated = self.program_ity(
        pure_space,
        program_space,
        annotation,
        Some(source_span(pattern.span)),
      )
      if annotated != result {
        @logic.fail_type(
          TypeMismatch,
          Some(source_span(pattern.span)),
          "postcondition result pattern has the wrong type",
        )
      }
      self.post_result_pattern(pure_space, program_space, inner, result)
    }
    Ptuple([]) => {
      let unit = self.unit_ity(
        pure_space,
        program_space,
        Some(source_span(pattern.span)),
      )
      if result != unit {
        @logic.fail_type(
          TypeMismatch,
          Some(source_span(pattern.span)),
          "unit postcondition pattern has the wrong result type",
        )
      }
      (None, pattern.span)
    }
    Pghost(_) =>
      fail_invalid_input(
        InvalidPattern,
        ProgramTyping,
        Some(source_span(pattern.span)),
        "ghost result patterns are outside the MVP",
      )
    _ =>
      fail_invalid_input(
        InvalidPattern,
        ProgramTyping,
        Some(source_span(pattern.span)),
        "destructuring result patterns are outside the MVP",
      )
  }
}

///|
fn simple_post_result_pattern(pattern : @parser.Pattern) -> Bool {
  match pattern.desc {
    Pvar(_) | Pwild | Ptuple([]) => true
    Pparen(inner) | Pscope(_, inner) | Pcast(inner, _) =>
      simple_post_result_pattern(inner)
    Pghost(_) | Papp(_, _) | Ptuple(_) | Prec(_) | Pas(_, _, _) | Por(_, _) =>
      false
  }
}

///|
fn ProgramTyping::type_case_postcondition(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  pending : PendingSpec,
  branches : ArrayView[(@parser.Pattern, @parser.Term)],
  result_ity : @mlw.Ity,
  result_mask : @mlw.ProgramMask,
  clause_span : @parser.Span,
) -> @mlw.Postcondition raise {
  let span = Some(source_span(clause_span))
  let result_ty = result_ity.to_ty(span)
  let result_symbol = @logic.VSymbol::new(
    self.context,
    b"result",
    @identity.Origin::user(b"result", span, []),
    result_ty,
    span,
  )
  let (parameter_locals, parameter_values) = program_spec_logic_scope(pending)
  let semantic_branches : Array[(@logic.Pattern, @logic.Term)] = []
  for branch in branches {
    let pattern = @mlw.ProgramPattern::new(
      self.context,
      self.program_prepattern(pure_space, program_space, branch.0),
      result_ity,
      result_mask,
      Some(source_span(branch.0.span)),
    )
    let locals = parameter_locals.copy()
    let values = parameter_values.copy()
    for variable in pattern.view().variables {
      let name = variable.view().name.view()
      let ident = @parser.Ident::{
        name: name.name,
        attributes: [
          for attribute in name.attributes => Text(attribute)
        ],
        span: branch.0.span,
      }
      let delayed = self.pure.make_local(
        Some(ident),
        branch.0.span,
        self.pure.delayed.known(variable.view().ity.to_ty(span), span),
      )
      locals.push((name.name, delayed))
      values.push((delayed.id, variable.view().pure_symbol))
    }
    semantic_branches.push(
      (
        pattern.view().pattern,
        self.pure.formula(
          pure_space,
          locals,
          values,
          branch.1,
          at_values=pending.at_values,
          at_labels=pending.at_labels,
          at_resolver=entry => self.materialize_at_value(entry),
        ),
      ),
    )
  }
  @mlw.Postcondition::trusted_new(
    result_symbol,
    @logic.Term::case(
      @logic.Term::variable(result_symbol).source_decorate(span, []),
      semantic_branches,
      span,
    ).source_decorate(span, []),
    span,
  )
}

///|
fn ProgramTyping::type_postcondition_branches(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  pending : PendingSpec,
  branches : ArrayView[(@parser.Pattern, @parser.Term)],
  result_ity : @mlw.Ity,
  result_mask : @mlw.ProgramMask,
  clause_span : @parser.Span,
) -> Array[@mlw.Postcondition] raise {
  if branches.length() != 1 || !simple_post_result_pattern(branches[0].0) {
    return [
      self.type_case_postcondition(
        pure_space, program_space, pending, branches, result_ity, result_mask, clause_span,
      ),
    ]
  }
  let (parameter_locals, parameter_values) = program_spec_logic_scope(pending)
  let result_ty = result_ity.to_ty(None)
  let result : Array[@mlw.Postcondition] = []
  for branch in branches {
    let (ident, fallback_span) = self.post_result_pattern(
      pure_space,
      program_space,
      branch.0,
      result_ity,
    )
    let delayed = self.pure.make_local(
      ident,
      fallback_span,
      self.pure.delayed.known(result_ty, Some(source_span(fallback_span))),
    )
    let result_symbol = @logic.VSymbol::new(
      self.context,
      delayed.name,
      delayed.origin,
      result_ty,
      Some(source_span(fallback_span)),
    )
    let locals = parameter_locals.copy()
    let values = parameter_values.copy()
    locals.push((delayed.name, delayed))
    values.push((delayed.id, result_symbol))
    let formula = self.pure.formula(
      pure_space,
      locals,
      values,
      branch.1,
      at_values=pending.at_values,
      at_labels=pending.at_labels,
      at_resolver=entry => self.materialize_at_value(entry),
    )
    result.push(
      @mlw.Postcondition::trusted_new(
        result_symbol,
        formula,
        Some(source_span(clause_span)),
      ),
    )
  }
  result
}

///|
fn ProgramTyping::type_postconditions(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  pending : PendingSpec,
  result_ity : @mlw.Ity,
  result_mask : @mlw.ProgramMask,
) -> Array[@mlw.Postcondition] raise {
  let result : Array[@mlw.Postcondition] = []
  for postcondition in pending.source.postconditions {
    for
      typed in self.type_postcondition_branches(
        pure_space,
        program_space,
        pending,
        postcondition.branches,
        result_ity,
        result_mask,
        postcondition.span,
      ) {
      result.push(typed)
    }
  }
  result
}

///|
fn ProgramTyping::type_exceptional_postconditions(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  pending : PendingSpec,
) -> Array[@mlw.ExceptionalPostconditions] raise {
  let grouped : Array[
    (@mlw.XSymbol, Array[(@parser.Pattern, @parser.Term)], @parser.Span),
  ] = []
  for clause in pending.source.exceptional_postconditions {
    for branch in clause.branches {
      let exception = program_space.find_exception(
        qualid_segments(branch.0),
        Some(qualid_span(branch.0)),
      )
      let mut found = -1
      for index, entry in grouped {
        if entry.0 == exception {
          found = index
          break
        }
      }
      if found < 0 {
        grouped.push((exception, [], clause.span))
        found = grouped.length() - 1
      }
      if branch.1 is Some(postcondition) {
        grouped[found].1.push(postcondition)
      }
    }
  }
  let result : Array[@mlw.ExceptionalPostconditions] = []
  for entry in grouped {
    let postconditions = if entry.1.is_empty() {
      []
    } else {
      self.type_postcondition_branches(
        pure_space,
        program_space,
        pending,
        entry.1,
        entry.0.view().ity,
        entry.0.view().mask,
        entry.2,
      )
    }
    result.push(
      @mlw.ExceptionalPostconditions::new(
        entry.0,
        postconditions,
        Some(source_span(entry.2)),
      ),
    )
  }
  result
}

///|
fn program_effect_local(
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  path : @parser.QualId,
) -> @mlw.PVariable raise {
  let segments = qualid_segments(path)
  if segments.length() == 1 {
    match find_program_local(locals, segments[0]) {
      Some(binding) => return binding.variable
      None => ()
    }
  }
  match program_space.find_variable_option(segments) {
    Some(variable) => return variable
    None => ()
  }
  @logic.fail_type(
    UnboundVariable,
    Some(qualid_span(path)),
    "effect clause expects a program variable",
  )
}

///|
fn ProgramTyping::apply_program_effect_projection(
  self : ProgramTyping,
  program_space : @mlw.ProgramNamespace,
  target : (@mlw.PVariable, @mlw.Ity, @mlw.RoutineSymbol?),
  path : @parser.QualId,
) -> (@mlw.PVariable, @mlw.Ity, @mlw.RoutineSymbol?) raise {
  let span = Some(qualid_span(path))
  let routine = program_space.find_routine(qualid_segments(path), span)
  let result = self.routine_result_for_argument_types(
    routine,
    [target.1],
    None,
    span,
  )
  if target.1.view() is ItyReg(region) &&
    routine.view().field is Some(field) &&
    region.view().symbol.view().mutable_fields.any(candidate => {
      candidate == field
    }) {
    (target.0, target.1, Some(routine))
  } else {
    (target.0, result, None)
  }
}

///|
fn ProgramTyping::program_effect_target(
  self : ProgramTyping,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  term : @parser.Term,
) -> (@mlw.PVariable, @mlw.Ity, @mlw.RoutineSymbol?) raise {
  match term.desc {
    Tident(path) => {
      let variable = program_effect_local(program_space, locals, path)
      (variable, variable.view().ity, None)
    }
    Tidapp(path, [argument]) => {
      let receiver = self.program_alias_target(program_space, locals, argument)
      self.apply_program_effect_projection(
        program_space,
        (receiver.0, receiver.1, None),
        path,
      )
    }
    Tapply({ desc: Tident(path), .. }, argument) => {
      let receiver = self.program_alias_target(program_space, locals, argument)
      self.apply_program_effect_projection(
        program_space,
        (receiver.0, receiver.1, None),
        path,
      )
    }
    Tscope(scope, nested) =>
      self.program_effect_target(
        program_space.open_scope(
          qualid_segments(scope),
          Some(qualid_span(scope)),
        ),
        locals,
        nested,
      )
    Tcast(nested, _) | Tattr(_, nested) =>
      self.program_effect_target(program_space, locals, nested)
    _ =>
      @logic.fail_type(
        TypeMismatch,
        Some(source_span(term.span)),
        "unsupported mutable expression in writes clause",
      )
  }
}

///|
fn program_alias_local(
  locals : ArrayView[(Bytes, ProgramLocal)],
  path : @parser.QualId,
) -> @mlw.PVariable raise {
  let segments = qualid_segments(path)
  if segments.length() == 1 {
    match find_program_local(locals, segments[0]) {
      Some(binding) => return binding.variable
      None => ()
    }
  }
  @logic.fail_type(
    UnboundVariable,
    Some(qualid_span(path)),
    "alias clause expects a program variable",
  )
}

///|
fn ProgramTyping::apply_program_alias_projection(
  self : ProgramTyping,
  program_space : @mlw.ProgramNamespace,
  target : (@mlw.PVariable, @mlw.Ity),
  path : @parser.QualId,
) -> (@mlw.PVariable, @mlw.Ity) raise {
  let span = Some(qualid_span(path))
  let routine = program_space.find_routine(qualid_segments(path), span)
  if routine.view().field is None {
    @logic.fail_type(
      TypeMismatch,
      span,
      "alias clause expects a record field projection",
    )
  }
  let result = self.routine_result_for_argument_types(
    routine,
    [target.1],
    None,
    span,
  )
  (target.0, result)
}

///|
fn ProgramTyping::program_alias_target(
  self : ProgramTyping,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  term : @parser.Term,
) -> (@mlw.PVariable, @mlw.Ity) raise {
  match term.desc {
    Tident(path) => {
      let variable = program_alias_local(locals, path)
      (variable, variable.view().ity)
    }
    Tidapp(path, [argument]) =>
      self.apply_program_alias_projection(
        program_space,
        self.program_alias_target(program_space, locals, argument),
        path,
      )
    Tapply({ desc: Tident(path), .. }, argument) =>
      self.apply_program_alias_projection(
        program_space,
        self.program_alias_target(program_space, locals, argument),
        path,
      )
    Tscope(scope, nested) =>
      self.program_alias_target(
        program_space.open_scope(
          qualid_segments(scope),
          Some(qualid_span(scope)),
        ),
        locals,
        nested,
      )
    Tcast(nested, _) | Tattr(_, nested) =>
      self.program_alias_target(program_space, locals, nested)
    _ =>
      @logic.fail_type(
        TypeMismatch,
        Some(source_span(term.span)),
        "alias clause expects a program variable or field projection",
      )
  }
}

///|
fn program_alias_root_is_local(
  root : @mlw.PVariable,
  arguments : ArrayView[@mlw.PVariable],
  results : ArrayView[@mlw.PVariable],
) -> Bool {
  arguments.any(argument => argument == root) ||
  results.any(result => result == root)
}

///|
fn ProgramTyping::apply_program_aliases(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  pending : PendingSpec,
  result : @mlw.Ity?,
  result_pattern : @parser.Pattern,
  result_mask : @mlw.ProgramMask,
) -> (PendingSpec, @mlw.Ity?) raise {
  if pending.source.aliases.is_empty() {
    return (pending, result)
  }
  let semantic_span = Some(source_span(result_pattern.span))
  let result_variable = match result {
    Some(result) =>
      Some(
        @mlw.PVariable::trusted_new(
          self.context,
          @theory.SemanticName::new(b"result", [], semantic_span),
          result,
          false,
          semantic_span,
        ),
      )
    None => None
  }
  let alias_scope = pending.parameter_scope.copy()
  let result_variables : Array[@mlw.PVariable] = []
  if result_variable is Some(variable) {
    result_variables.push(variable)
    let result_binding = self.program_local_from_variable(
      variable,
      result_pattern.span,
    )
    let pattern = @mlw.ProgramPattern::new(
      self.context,
      self.program_prepattern(pure_space, program_space, result_pattern),
      variable.view().ity,
      result_mask,
      semantic_span,
    )
    for component in pattern.view().variables {
      let name = component.view().name.view().name
      alias_scope.push(
        (name, self.program_local_from_variable(component, result_pattern.span)),
      )
      result_variables.push(component)
    }
    alias_scope.push((b"result", result_binding))
  }
  let mut substitution = @mlw.ItySubstitution::empty()
  for alias_entry in pending.source.aliases {
    let left = self.program_alias_target(
      program_space,
      alias_scope,
      alias_entry.0,
    )
    let right = self.program_alias_target(
      program_space,
      alias_scope,
      alias_entry.1,
    )
    let normalized = substitution.instantiate_partial(
      [left.1, right.1],
      Some(source_span(alias_entry.0.span)),
    )
    if normalized[0] == normalized[1] {
      continue
    }
    let left_local = program_alias_root_is_local(
      left.0,
      pending.arguments,
      result_variables,
    )
    let right_local = program_alias_root_is_local(
      right.0,
      pending.arguments,
      result_variables,
    )
    if !left_local && !right_local {
      @logic.fail_type(
        TypeMismatch,
        Some(source_span(alias_entry.0.span)),
        "alias clause cannot identify two distinct external regions",
      )
    }
    substitution = if left_local {
      substitution.match_ity(
        normalized[0],
        normalized[1],
        Some(source_span(alias_entry.0.span)),
      )
    } else {
      substitution.match_ity(
        normalized[1],
        normalized[0],
        Some(source_span(alias_entry.1.span)),
      )
    }
  }

  let signature = pending.arguments.map(argument => argument.view().ity)
  if result is Some(result) {
    signature.push(result)
  }
  let mut rewritten = signature
  // Alias clauses intentionally identify ordinary semantic regions. Their
  // substitutions can form an acyclic chain across several clauses, so apply
  // the accumulated map to a fixed point rather than using the one-layer
  // inference substitution rule.
  for iteration = 0
      iteration <= pending.source.aliases.length()
      iteration = iteration + 1 {
    let next = substitution.instantiate_partial(rewritten, semantic_span)
    if next == rewritten {
      break
    }
    rewritten = next
  }
  let arguments : Array[@mlw.PVariable] = []
  let replacements : Array[(@mlw.PVariable, @mlw.PVariable)] = []
  for index, argument in pending.arguments {
    let view = argument.view()
    let replacement = if view.ity == rewritten[index] {
      argument
    } else {
      @mlw.PVariable::trusted_new(
        self.context,
        view.name,
        rewritten[index],
        view.ghost,
        view.name.view().source_span,
      )
    }
    arguments.push(replacement)
    replacements.push((argument, replacement))
  }
  let parameter_scope : Array[(Bytes, ProgramLocal)] = []
  for entry in pending.parameter_scope {
    let mut replacement : @mlw.PVariable? = None
    for pair in replacements {
      if pair.0 == entry.1.variable {
        replacement = Some(pair.1)
        break
      }
    }
    match replacement {
      None => parameter_scope.push(entry)
      Some(variable) => {
        let span = variable.view().name.view().source_span
        parameter_scope.push(
          (
            entry.0,
            {
              ..entry.1,
              variable,
              delayed: {
                ..entry.1.delayed,
                ty: self.pure.delayed.known(
                  variable.view().ity.to_ty(span),
                  span,
                ),
              },
            },
          ),
        )
      }
    }
  }
  let oldies : Array[@mlw.OldSnapshot] = []
  let at_values : Array[DAtValue] = []
  for entry in parameter_scope {
    let original = entry.1.variable
    if !original.view().ity.is_pure() {
      let snapshot = @mlw.PVariable::trusted_new(
        self.context,
        original.view().name,
        original.view().ity.purify(),
        true,
        original.view().name.view().source_span,
      )
      self.register_snapshot_placeholder(snapshot, original)
      oldies.push(@mlw.OldSnapshot::new(snapshot, original, None))
      at_values.push({
        local_id: entry.1.delayed.id,
        label: b"'Old",
        value: snapshot.view().pure_symbol,
      })
    }
  }
  let rewritten_result = match result {
    Some(_) => Some(rewritten[rewritten.length() - 1])
    None => None
  }
  (
    { ..pending, arguments, parameter_scope, oldies, at_values },
    rewritten_result,
  )
}

///|
fn append_effect_read(
  reads : Array[@mlw.PVariable],
  variable : @mlw.PVariable,
) -> Unit {
  if !reads.any(existing => existing == variable) {
    reads.push(variable)
  }
}

///|
fn ProgramTyping::specified_effect(
  self : ProgramTyping,
  program_space : @mlw.ProgramNamespace,
  pending : PendingSpec,
  exceptional : ArrayView[@mlw.ExceptionalPostconditions],
  ghost : Bool,
  span : @identity.SourceSpan?,
) -> @mlw.Effect raise {
  let reads : Array[@mlw.PVariable] = []
  for path in pending.source.reads {
    append_effect_read(
      reads,
      program_effect_local(program_space, pending.parameter_scope, path),
    )
  }
  let writes : Array[@mlw.EffectWrite] = []
  for source in pending.source.writes {
    let (root, ity, projection) = self.program_effect_target(
      program_space,
      pending.parameter_scope,
      source,
    )
    append_effect_read(reads, root)
    guard ity.view() is ItyReg(region) else {
      @logic.fail_type(
        TypeMismatch,
        Some(source_span(source.span)),
        "writes clause expects a mutable region",
      )
    }
    let fields = match projection {
      Some(routine) =>
        match routine.view().field {
          Some(field) => [field]
          None => []
        }
      None => region.view().symbol.view().mutable_fields.to_owned()
    }
    writes.push(
      @mlw.EffectWrite::new(region, fields, Some(source_span(source.span))),
    )
  }
  let mut effect = @mlw.Effect::write(reads, writes, span)
  for entry in exceptional {
    effect = effect.raise_exception(entry.view().exception)
  }
  if pending.source.partial {
    effect = effect.partial(span)
  }
  if pending.source.diverges {
    effect = effect.diverge(span)
  }
  effect.ghostify(ghost, span)
}

///|
fn ProgramTyping::boolean_ity(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  span : @identity.SourceSpan?,
) -> @mlw.Ity raise {
  ignore(self)
  let symbol = pure_space.find_type([b"bool"], span)
  @mlw.Ity::from_ty(program_space, @logic.Ty::app(symbol, [], span), span)
}

///|
fn ProgramTyping::unit_ity(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  span : @identity.SourceSpan?,
) -> @mlw.Ity raise {
  ignore(self)
  let symbol = pure_space.find_type([b"unit"], span)
  @mlw.Ity::from_ty(program_space, @logic.Ty::app(symbol, [], span), span)
}

///|
fn ProgramTyping::constant_expression(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  constant : @parser.Constant,
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  ignore(self)
  let type_name = match constant {
    ConstInt(_) => b"int"
    ConstReal(_) => b"real"
    ConstStr(_) => b"string"
  }
  let ity = match expected {
    Some(expected) =>
      match (constant, expected.view()) {
        (ConstInt(_), ItyApp(symbol, _, _)) if symbol.view().logic_type.view().definition
          is Range(_, _) => expected
        (ConstReal(_), ItyApp(symbol, _, _)) if symbol.view().logic_type.view().definition
          is Float(_, _) => expected
        _ => {
          let symbol = pure_space.find_type(
            [type_name],
            Some(decoration.location),
          )
          @mlw.Ity::from_ty(
            program_space,
            @logic.Ty::app(symbol, [], Some(decoration.location)),
            Some(decoration.location),
          )
        }
      }
    None => {
      let symbol = pure_space.find_type([type_name], Some(decoration.location))
      @mlw.Ity::from_ty(
        program_space,
        @logic.Ty::app(symbol, [], Some(decoration.location)),
        Some(decoration.location),
      )
    }
  }
  @mlw.Expr::constant(
    constant,
    ity,
    program_origin(decoration),
    decoration.attributes,
  )
}

///|
fn ProgramTyping::zero_argument_pure_expression(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  name : BytesView,
  result : @mlw.Ity,
  decoration : ProgramDecoration,
  synthesized? : Bool = false,
) -> @mlw.Expr raise {
  let origin = if synthesized {
    @identity.Origin::user(b"", None, [])
  } else {
    program_origin(decoration)
  }
  let attributes : ArrayView[Bytes] = if synthesized {
    []
  } else {
    decoration.attributes
  }
  let expression_span = if synthesized {
    None
  } else {
    Some(decoration.location)
  }
  match program_space.find_routine_option([name.to_owned()]) {
    Some(routine) =>
      return @mlw.Expr::routine_call(
        routine,
        [],
        result,
        origin,
        attributes,
        expression_span,
      )
    None => ()
  }
  let symbol = pure_space.find_logic(
    [name.to_owned()],
    Some(decoration.location),
  )
  let view = symbol.view()
  if !view.argument_types.is_empty() || view.result_type is None {
    @logic.fail_type(
      TypeMismatch,
      Some(decoration.location),
      "expected a zero-argument pure program value",
    )
  }
  @mlw.Expr::pure_application(
    self.context,
    symbol,
    [],
    result,
    pure_space.find_logic([b"infix ="], expression_span),
    pure_space.find_logic([b"True"], expression_span),
    origin,
    attributes,
    expression_span,
  )
}

///|
fn collect_program_application(
  expression : @parser.Expr,
  reversed : Array[@parser.Expr],
) -> @parser.Expr {
  match expression.desc {
    Eapply(function_, argument) => {
      reversed.push(argument)
      collect_program_application(function_, reversed)
    }
    _ => expression
  }
}

///|
fn program_function_parts(
  ity : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> (@mlw.Ity, @mlw.Ity) raise @logic.TypeError {
  match ity.view() {
    ItyApp(symbol, arguments, regions) if symbol.view().logic_type.name() ==
      b"infix ->" &&
      arguments.length() == 2 &&
      regions.is_empty() => (arguments[0], arguments[1])
    _ =>
      @logic.fail_type(
        FunctionExpected,
        span,
        "program expression cannot be applied as a function",
      )
  }
}

///|
fn program_function_ity(
  function_type : @mlw.ProgramTypeSymbol,
  parameter : @mlw.Ity,
  result : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> @mlw.Ity raise {
  if function_type.view().logic_type.name() != b"infix ->" {
    @logic.fail_type(
      TypeMismatch,
      span,
      "expected the builtin program function type",
    )
  }
  @mlw.Ity::app(function_type, [parameter, result], span)
}

///|
fn ProgramTyping::higher_order_program_application(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  head : @parser.Expr,
  arguments : ArrayView[@parser.Expr],
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let result = self.type_program_expression(
    pure_space, program_space, locals, head,
  )
  self.continue_higher_order_program_application(
    pure_space,
    program_space,
    locals,
    result,
    arguments,
    source_span(head.span),
    decoration,
    expected,
  )
}

///|
fn ProgramTyping::continue_higher_order_program_application(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  initial : @mlw.Expr,
  arguments : ArrayView[@parser.Expr],
  function_span : @identity.SourceSpan,
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  let application = program_space.find_routine([b"infix @"], span)
  let mut result = initial
  for index, argument in arguments {
    let (parameter, _) = program_function_parts(result.ity(), span)
    let typed_argument = self.type_program_expression_expected(
      pure_space,
      program_space,
      locals,
      argument,
      Some(parameter),
    )
    result = self.typed_routine_application(
      application,
      [result, typed_argument],
      [function_span, source_span(argument.span)],
      decoration,
      if index + 1 == arguments.length() {
        expected
      } else {
        None
      },
    )
  }
  result
}

///|
fn ProgramTyping::proxy_argument(
  self : ProgramTyping,
  expression : @mlw.Expr,
  span : @identity.SourceSpan,
  ghost? : Bool = false,
  inherit_ghost_context? : Bool = true,
) -> (@mlw.PVariable, @mlw.Expr?) raise {
  match expression.view() {
    Evar(variable) => (variable, None)
    _ => {
      let proxy_ghost = (inherit_ghost_context && self.ghost_context) ||
        ghost ||
        expression.mask().is_ghost()
      let proxy = @mlw.PVariable::trusted_new(
        self.context,
        @theory.SemanticName::new(b"o", [b"mlw:proxy_symbol"], Some(span)),
        expression.ity(),
        proxy_ghost,
        Some(span),
      )
      (proxy, Some(expression))
    }
  }
}

///|
fn ProgramTyping::routine_application_proxy_ghosts(
  self : ProgramTyping,
  routine : @mlw.RoutineSymbol,
  arguments : ArrayView[@mlw.Expr],
  fully_applied : Bool,
) -> Array[Bool] {
  let view = routine.view()
  let formals = view.cty.view().arguments
  let tuple_application = fully_applied &&
    view.origin
    .attributes()
    .any(attribute => attribute == b"why3:builtin:tuple-constructor")
  let mut application_ghost = self.ghost_context || routine.is_ghost()
  if !tuple_application && !application_ghost {
    for index, argument in arguments {
      if !formals[index].view().ghost && argument.mask().is_ghost() {
        application_ghost = true
        break
      }
    }
  }
  [
    for index, _ in arguments => {
      application_ghost || formals[index].view().ghost
    }
  ]
}

///|
fn ProgramTyping::wrap_argument_proxies(
  self : ProgramTyping,
  proxies : ArrayView[(@mlw.PVariable, @mlw.Expr?)],
  body : @mlw.Expr,
  decoration : ProgramDecoration,
) -> @mlw.Expr raise {
  ignore(self)
  let mut result = body
  for index = 0; index < proxies.length(); index = index + 1 {
    let (binder, value) = proxies[index]
    if value is Some(value) {
      result = @mlw.Expr::let_in(
        binder,
        value,
        result,
        program_origin(decoration),
        decoration.attributes,
        Some(decoration.location),
      )
    }
  }
  result
}

///|
fn try_instantiate_program_type(
  substitution : @mlw.ItySubstitution,
  ity : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> @mlw.Ity? raise @mlw.MlwError {
  Some(substitution.instantiate(ity, span)) catch {
    @mlw.MlwError(diagnostic) =>
      match diagnostic.kind {
        UnboundProgramTypeVariable | UnboundRegion => None
        _ => raise @mlw.MlwError(diagnostic)
      }
  }
}

///|
fn instantiate_program_expected(
  context : @identity.CompilationContext,
  substitution : @mlw.ItySubstitution,
  ity : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> (@mlw.ItySubstitution, @mlw.Ity) raise @mlw.MlwError {
  match try_instantiate_program_type(substitution, ity, span) {
    Some(instantiated) => (substitution, instantiated)
    None => substitution.instantiate_inference_expected(context, ity, span)
  }
}

///|
fn freshen_program_expected_regions(
  context : @identity.CompilationContext,
  ity : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> @mlw.Ity raise {
  let mut substitution = @mlw.ItySubstitution::empty()
  for variable in ity.free_type_variables() {
    substitution = substitution.freeze(@mlw.Ity::variable(variable), span)
  }
  substitution.instantiate_inference_expected(context, ity, span).1
}

///|
fn match_routine_application_type(
  substitution : @mlw.ItySubstitution,
  routine : @mlw.RoutineSymbol,
  formal : @mlw.Ity,
  actual : @mlw.Ity,
  role : String,
  span : @identity.SourceSpan?,
) -> @mlw.ItySubstitution raise @mlw.MlwError {
  substitution.match_ity(formal, actual, span) catch {
    @mlw.MlwError(diagnostic) =>
      if diagnostic.kind == ProgramTypeMismatch {
        raise @mlw.MlwError({
          ..diagnostic,
          message: "routine \{routine.view().name} \{role}: \{diagnostic.message}",
        })
      } else {
        raise @mlw.MlwError(diagnostic)
      }
  }
}

///|
fn instantiate_program_result(
  context : @identity.CompilationContext,
  substitution : @mlw.ItySubstitution,
  result : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> @mlw.Ity raise {
  let instantiated = substitution.instantiate_generalized_call_result(
    context, result, span,
  ) catch {
    @mlw.MlwError(diagnostic) =>
      match diagnostic.kind {
        UnboundProgramTypeVariable =>
          @logic.fail_type(
            PolymorphicProgramRoutine,
            span,
            "program call leaves a residual program type variable",
          )
        _ => raise @mlw.MlwError(diagnostic)
      }
  }
  instantiated
}

///|
fn ProgramTyping::typed_routine_application(
  self : ProgramTyping,
  routine : @mlw.RoutineSymbol,
  arguments : ArrayView[@mlw.Expr],
  argument_spans : ArrayView[@identity.SourceSpan],
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  let cty = routine.view().cty.view()
  if arguments.length() != cty.arguments.length() {
    @logic.fail_type(
      ArityMismatch,
      span,
      "routine expected \{cty.arguments.length()} arguments but received \{arguments.length()}",
    )
  }
  let mut substitution = cty.freeze
  if expected is Some(expected) {
    substitution = match_routine_application_type(
      substitution,
      routine,
      cty.result,
      expected,
      "result",
      span,
    )
  }
  for index, argument in arguments {
    substitution = match_routine_application_type(
      substitution,
      routine,
      cty.arguments[index].view().ity,
      argument.ity(),
      "argument \{index}",
      span,
    )
  }
  let result_ity = instantiate_program_result(
    self.context,
    substitution,
    cty.result,
    span,
  )
  let proxy_ghosts = self.routine_application_proxy_ghosts(
    routine, arguments, true,
  )
  let pending_proxies : Array[(@mlw.PVariable, @mlw.Expr?)?] = [
    for _ in arguments => None
  ]
  for index = arguments.length() - 1; index >= 0; index = index - 1 {
    let argument = arguments[index]
    let argument_span = if index < argument_spans.length() {
      argument_spans[index]
    } else {
      decoration.location
    }
    let proxy = self.proxy_argument(
      argument,
      argument_span,
      ghost=proxy_ghosts[index],
    )
    pending_proxies[index] = Some(proxy)
  }
  let proxies = pending_proxies.map(proxy => {
    match proxy {
      Some(proxy) => proxy
      None => abort("routine proxy construction left an argument unbound")
    }
  })
  let variables = proxies.map(proxy => proxy.0)
  let call = @mlw.Expr::routine_call(
    routine,
    variables,
    result_ity,
    program_origin(decoration),
    decoration.attributes,
    span,
  )
  self.wrap_argument_proxies(proxies, call, decoration)
}

///|
fn program_expression_needs_expected_type(
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  expression : @parser.Expr,
) -> Bool {
  match expression.desc {
    Eident(Qident(ident)) =>
      if find_program_local(locals, ident.name) is Some(binding) {
        binding.reference
      } else {
        match program_space.find_routine_option([ident.name]) {
          Some(routine) => !routine.view().cty.view().result.is_closed()
          // A name absent from the program namespace can still be a
          // polymorphic pure-logic constant. Keep it delayed until an
          // expected type is available.
          None => true
        }
      }
    Eident(qualid) =>
      match program_space.find_routine_option(qualid_segments(qualid)) {
        Some(routine) => !routine.view().cty.view().result.is_closed()
        None => true
      }
    Eidapp(_, _) | Eapply(_, _) => true
    Efun(binders, _, _, _, _, _) =>
      binders.any(binder => binder.binder_type is None)
    Eany(_, _, return_type, _, _, _) => return_type is None
    Eghost(inner) | Eattr(_, inner) =>
      program_expression_needs_expected_type(program_space, locals, inner)
    Ecast(_, _) => false
    _ => false
  }
}

///|
fn program_expression_is_anonymous_routine(expression : @parser.Expr) -> Bool {
  match expression.desc {
    Efun(_, _, _, _, _, _) | Eany(_, _, _, _, _, _) => true
    Escope(_, inner) | Elabel(_, inner) | Eghost(inner) | Eattr(_, inner) =>
      program_expression_is_anonymous_routine(inner)
    _ => false
  }
}

///|
fn routine_is_nonfree_record_constructor(
  routine : @mlw.RoutineSymbol,
  result_symbol : @mlw.ProgramTypeSymbol,
) -> Bool {
  let routine_view = routine.view()
  guard routine_view.logic is RLnone else { return false }
  let cty = routine_view.cty.view()
  guard program_ity_head_symbol(cty.result) is Some(actual_symbol) &&
    actual_symbol == result_symbol else {
    return false
  }
  let symbol_view = result_symbol.view()
  let fields = symbol_view.mutable_fields.to_owned() +
    symbol_view.immutable_fields.to_owned()
  cty.arguments.length() == fields.length() &&
  cty.arguments.all(argument => fields.any(field => field == argument))
}

///|
fn routine_is_logical_constructor(routine : @mlw.RoutineSymbol) -> Bool {
  match routine.view().logic {
    RLls(symbol) => symbol.view().role is Constructor(1)
    RLnone | RLpv(_) | RLlemma => false
  }
}

///|
fn ProgramTyping::resolved_routine_application(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  routine : @mlw.RoutineSymbol,
  arguments : ArrayView[@parser.Expr],
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  let cty = routine.view().cty.view()
  if arguments.length() < cty.arguments.length() {
    return self.partial_routine_application(
      pure_space, program_space, locals, routine, arguments, decoration, expected,
    )
  }
  if arguments.length() > cty.arguments.length() {
    let direct = self.resolved_routine_application(
      pure_space,
      program_space,
      locals,
      routine,
      arguments[0:cty.arguments.length()],
      decoration,
      None,
    )
    return self.continue_higher_order_program_application(
      pure_space,
      program_space,
      locals,
      direct,
      arguments[cty.arguments.length():],
      decoration.location,
      decoration,
      expected,
    )
  }
  let application_expected = match expected {
    Some(expected) =>
      match program_ity_head_symbol(expected) {
        Some(result_symbol) if (
            routine_is_logical_constructor(routine) ||
            routine_is_nonfree_record_constructor(routine, result_symbol)
          ) &&
          result_symbol.view().mutable_fields.is_empty() &&
          !expected.reachable_regions().is_empty() =>
          Some(freshen_program_expected_regions(self.context, expected, span))
        _ => Some(expected)
      }
    None => None
  }
  let mut substitution = cty.freeze
  if application_expected is Some(expected) {
    substitution = match_routine_application_type(
      substitution,
      routine,
      cty.result,
      expected,
      "result constraint",
      span,
    )
  }
  // An argument that syntactically needs an expected type can still expose a
  // unique, concrete result through its own application. Use those results to
  // constrain the shared routine instantiation before introducing temporary
  // inference variables for earlier arguments.
  for index, argument in arguments {
    if !program_expression_needs_expected_type(program_space, locals, argument) {
      continue
    }
    let inferred = self.partially_inferred_program_expression_type(
      pure_space, program_space, locals, argument,
    ) catch {
      _ => None
    }
    if inferred is Some(inferred) &&
      !program_ity_has_inference_variables(inferred) {
      let constrained = Some(
        substitution.match_ity(cty.arguments[index].view().ity, inferred, span),
      ) catch {
        _ => None
      }
      if constrained is Some(constrained) {
        substitution = constrained
      }
    }
  }
  let pending : Array[@mlw.Expr?] = [ for _ in arguments => None ]
  let mut remaining = arguments.length()
  while remaining > 0 {
    let mut progress = false
    for index, argument in arguments {
      if pending[index] is Some(_) {
        continue
      }
      let argument_expected = try_instantiate_program_type(
        substitution,
        cty.arguments[index].view().ity,
        span,
      )
      if argument_expected is None {
        continue
      }
      let actual = self.type_program_expression_expected(
        pure_space, program_space, locals, argument, argument_expected,
      )
      pending[index] = Some(actual)
      substitution = match_routine_application_type(
        substitution,
        routine,
        cty.arguments[index].view().ity,
        actual.ity(),
        "inferred argument \{index}",
        span,
      )
      remaining = remaining - 1
      progress = true
    }
    if progress {
      continue
    }
    let mut fallback = -1
    for index, argument in arguments {
      if pending[index] is None &&
        !program_expression_needs_expected_type(program_space, locals, argument) {
        fallback = index
        break
      }
    }
    if fallback < 0 {
      for index, argument in arguments {
        if pending[index] is None &&
          !program_expression_is_anonymous_routine(argument) {
          fallback = index
          break
        }
      }
      if fallback < 0 {
        fallback = 0
        while pending[fallback] is Some(_) {
          fallback = fallback + 1
        }
      }
      let (next, argument_expected) = instantiate_program_expected(
        self.context,
        substitution,
        cty.arguments[fallback].view().ity,
        span,
      )
      substitution = next
      let actual = self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        arguments[fallback],
        Some(argument_expected),
      )
      pending[fallback] = Some(actual)
      substitution = match_routine_application_type(
        substitution,
        routine,
        cty.arguments[fallback].view().ity,
        actual.ity(),
        "contextual argument \{fallback}",
        span,
      )
      remaining = remaining - 1
      continue
    }
    let actual = self.type_program_expression_expected(
      pure_space,
      program_space,
      locals,
      arguments[fallback],
      None,
    )
    pending[fallback] = Some(actual)
    substitution = match_routine_application_type(
      substitution,
      routine,
      cty.arguments[fallback].view().ity,
      actual.ity(),
      "fallback argument \{fallback}",
      span,
    )
    remaining = remaining - 1
  }
  let typed = pending.map(expression => {
    match expression {
      Some(expression) => expression
      None => abort("routine argument inference left an untyped argument")
    }
  })
  self.typed_routine_application(
    routine,
    typed,
    arguments.map(argument => source_span(argument.span)),
    decoration,
    application_expected,
  )
}

///|
fn ProgramTyping::partial_routine_application(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  routine : @mlw.RoutineSymbol,
  arguments : ArrayView[@parser.Expr],
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  let cty = routine.view().cty.view()
  if arguments.length() >= cty.arguments.length() {
    @logic.fail_type(
      ArityMismatch,
      span,
      "partial routine application must leave at least one parameter",
    )
  }
  let function_type = program_space.find_type([b"infix ->"], span) catch {
    @mlw.MlwError(diagnostic) =>
      if diagnostic.kind == @mlw.UnboundProgramName {
        @logic.fail_type(
          TypeMismatch,
          span,
          "partial routine application has the wrong result type",
        )
      } else {
        raise @mlw.MlwError(diagnostic)
      }
  }
  let mut formal_value = cty.result
  for index = cty.arguments.length() - 1
      index >= arguments.length()
      index = index - 1 {
    formal_value = program_function_ity(
      function_type,
      cty.arguments[index].view().ity,
      formal_value,
      span,
    )
  }
  let mut substitution = cty.freeze
  if expected is Some(expected) {
    substitution = substitution.match_ity(formal_value, expected, span) catch {
      @mlw.MlwError(diagnostic) =>
        if diagnostic.kind == @mlw.ProgramTypeMismatch {
          @logic.fail_type(
            TypeMismatch,
            span,
            "partial routine application has the wrong function type",
          )
        } else {
          raise @mlw.MlwError(diagnostic)
        }
    }
  }
  let typed : Array[@mlw.Expr] = []
  for index, argument in arguments {
    let formal = cty.arguments[index].view().ity
    let (next, argument_expected) = instantiate_program_expected(
      self.context,
      substitution,
      formal,
      span,
    )
    substitution = next
    let actual = self.type_program_expression_expected(
      pure_space,
      program_space,
      locals,
      argument,
      Some(argument_expected),
    )
    typed.push(actual)
    substitution = substitution.match_ity(formal, actual.ity(), span)
  }
  let remaining_types : Array[@mlw.Ity] = []
  for index = arguments.length()
      index < cty.arguments.length()
      index = index + 1 {
    remaining_types.push(
      instantiate_program_result(
        self.context,
        substitution,
        cty.arguments[index].view().ity,
        span,
      ),
    )
  }
  let result = instantiate_program_result(
    self.context,
    substitution,
    cty.result,
    span,
  )
  let proxies : Array[(@mlw.PVariable, @mlw.Expr?)] = []
  let variables : Array[@mlw.PVariable] = []
  let proxy_ghosts = self.routine_application_proxy_ghosts(
    routine, typed, false,
  )
  for index, argument in typed {
    let proxy = self.proxy_argument(
      argument,
      source_span(arguments[index].span),
      ghost=proxy_ghosts[index],
    )
    proxies.push(proxy)
    variables.push(proxy.0)
  }
  let computation = @mlw.Cexp::call(
    routine, variables, remaining_types, result, span,
  )
  let value = @mlw.Expr::execute_function_value(
    computation,
    self.context,
    function_type,
    pure_space.find_logic([b"infix @"], span),
    program_origin(decoration),
    decoration.attributes,
    span,
  )
  self.wrap_argument_proxies(proxies, value, decoration)
}

///|
fn overloaded_routine_matches_known_arguments(
  routine : @mlw.RoutineSymbol,
  known : ArrayView[(Int, @mlw.Ity)],
  expected : @mlw.Ity?,
  span : @identity.SourceSpan?,
) -> Bool raise @mlw.MlwError {
  let cty = routine.view().cty.view()
  let mut substitution = cty.freeze
  if expected is Some(expected) {
    substitution = substitution.match_ity(cty.result, expected, span) catch {
      @mlw.MlwError(diagnostic) =>
        if diagnostic.kind == @mlw.ProgramTypeMismatch {
          return false
        } else {
          raise @mlw.MlwError(diagnostic)
        }
    }
  }
  for entry in known {
    substitution = substitution.match_ity(
      cty.arguments[entry.0].view().ity,
      entry.1,
      span,
    ) catch {
      @mlw.MlwError(diagnostic) =>
        if diagnostic.kind == @mlw.ProgramTypeMismatch {
          return false
        } else {
          raise @mlw.MlwError(diagnostic)
        }
    }
  }
  true
}

///|
fn ProgramTyping::overloaded_routine_application(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  routines : ArrayView[@mlw.RoutineSymbol],
  arguments : ArrayView[@parser.Expr],
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  if routines.is_empty() {
    abort("overloaded routine application has no candidates")
  }
  let representative = routines[0].view().cty.view()
  if arguments.length() != representative.arguments.length() {
    @logic.fail_type(
      ArityMismatch,
      span,
      "overloaded routine notation has the wrong number of arguments",
    )
  }
  if arguments.is_empty() {
    @logic.fail_type(
      TypeMismatch,
      span,
      "zero-argument routine notation cannot be overloaded",
    )
  }
  // Machine integer literals acquire their range type from context. Resolve
  // overloaded notation from independently typed non-literal operands before
  // falling back to the default `int`/`real` literal types.
  let known : Array[(Int, @mlw.Ity)] = []
  for index, argument in arguments {
    if !program_expression_is_untyped_constant(argument) {
      let inferred = try {
        if program_expression_needs_expected_type(
            program_space, locals, argument,
          ) {
          self.partially_inferred_program_expression_type(
            pure_space, program_space, locals, argument,
          )
        } else {
          Some(
            self
            .type_program_expression(
              pure_space, program_space, locals, argument,
            )
            .ity(),
          )
        }
      } catch {
        _ => None
      }
      if inferred is Some(inferred) &&
        !program_ity_has_inference_variables(inferred) {
        known.push((index, inferred))
      }
    }
  }
  if !known.is_empty() || expected is Some(_) {
    let compatible : Array[@mlw.RoutineSymbol] = []
    for routine in routines {
      if overloaded_routine_matches_known_arguments(
          routine, known, expected, span,
        ) {
        compatible.push(routine)
      }
    }
    if compatible is [routine] {
      return self.resolved_routine_application(
        pure_space, program_space, locals, routine, arguments, decoration, expected,
      )
    }
  }
  let first_formal = representative.arguments[0].view().ity
  let first_expected = if representative.result == first_formal {
    expected
  } else {
    None
  }
  let typed : Array[@mlw.Expr] = [
    self.type_program_expression_expected(
      pure_space,
      program_space,
      locals,
      arguments[0],
      first_expected,
    ),
  ]
  for index = 1; index < arguments.length(); index = index + 1 {
    typed.push(
      self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        arguments[index],
        Some(typed[0].ity()),
      ),
    )
  }
  let argument_spans = arguments.map(argument => source_span(argument.span))
  let matches : Array[@mlw.Expr] = []
  for routine in routines {
    matches.push(
      self.typed_routine_application(
        routine, typed, argument_spans, decoration, expected,
      ),
    ) catch {
      @mlw.MlwError(diagnostic) =>
        if diagnostic.kind != @mlw.ProgramTypeMismatch {
          raise @mlw.MlwError(diagnostic)
        }
      error => raise error
    }
  }
  match matches {
    [result] => result
    [] =>
      @logic.fail_type(
        TypeMismatch,
        span,
        "no suitable program routine matches the overloaded notation",
      )
    _ =>
      @logic.fail_type(
        TypeMismatch,
        span,
        "program routine notation is ambiguous",
      )
  }
}

///|
fn ProgramTyping::routine_result_for_argument_types(
  self : ProgramTyping,
  routine : @mlw.RoutineSymbol,
  arguments : ArrayView[@mlw.Ity],
  expected : @mlw.Ity?,
  span : @identity.SourceSpan?,
) -> @mlw.Ity raise {
  let cty = routine.view().cty.view()
  if arguments.length() != cty.arguments.length() {
    @logic.fail_type(
      ArityMismatch,
      span,
      "routine expected \{cty.arguments.length()} arguments but received \{arguments.length()}",
    )
  }
  let mut substitution = cty.freeze
  if expected is Some(expected) {
    substitution = substitution.match_ity(cty.result, expected, span)
  }
  for index, argument in arguments {
    substitution = substitution.match_ity(
      cty.arguments[index].view().ity,
      argument,
      span,
    )
  }
  instantiate_program_result(self.context, substitution, cty.result, span)
}

///|
fn ProgramTyping::pure_application(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  path : ArrayView[Bytes],
  arguments : ArrayView[@parser.Expr],
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  let symbol = pure_space.find_logic(path, span)
  let symbol_view = symbol.view()
  if arguments.length() > symbol_view.argument_types.length() {
    let direct = self.pure_application(
      pure_space,
      program_space,
      locals,
      path,
      arguments[0:symbol_view.argument_types.length()],
      decoration,
      None,
    )
    return self.continue_higher_order_program_application(
      pure_space,
      program_space,
      locals,
      direct,
      arguments[symbol_view.argument_types.length():],
      decoration.location,
      decoration,
      expected,
    )
  }
  if arguments.length() < symbol_view.argument_types.length() {
    return self.partial_pure_application(
      pure_space, program_space, locals, symbol, arguments, decoration, expected,
    )
  }
  let formal_result = match symbol_view.result_type {
    Some(result) => @mlw.Ity::from_ty(program_space, result, span)
    None => self.boolean_ity(pure_space, program_space, span)
  }
  let mut substitution = @mlw.ItySubstitution::empty()
  if expected is Some(expected) {
    substitution = substitution.match_ity(formal_result, expected, span)
  }
  let formal_arguments = symbol_view.argument_types.map(argument => {
    @mlw.Ity::from_ty(program_space, argument, span)
  })
  let pending : Array[@mlw.Expr?] = [ for _ in arguments => None ]
  let mut remaining = arguments.length()
  while remaining > 0 {
    let mut progress = false
    for index, argument in arguments {
      if pending[index] is Some(_) {
        continue
      }
      let argument_expected = try_instantiate_program_type(
        substitution,
        formal_arguments[index],
        span,
      )
      if argument_expected is None {
        continue
      }
      let actual = self.type_program_expression_expected(
        pure_space, program_space, locals, argument, argument_expected,
      )
      pending[index] = Some(actual)
      substitution = substitution.match_ity(
        formal_arguments[index],
        actual.ity(),
        span,
      )
      remaining = remaining - 1
      progress = true
    }
    if progress {
      continue
    }
    let mut fallback = -1
    for index, argument in arguments {
      if pending[index] is None &&
        !program_expression_is_anonymous_routine(argument) {
        fallback = index
        break
      }
    }
    if fallback < 0 {
      fallback = 0
      while pending[fallback] is Some(_) {
        fallback = fallback + 1
      }
    }
    let (next, argument_expected) = instantiate_program_expected(
      self.context,
      substitution,
      formal_arguments[fallback],
      span,
    )
    substitution = next
    let actual = self.type_program_expression_expected(
      pure_space,
      program_space,
      locals,
      arguments[fallback],
      Some(argument_expected),
    )
    pending[fallback] = Some(actual)
    substitution = substitution.match_ity(
      formal_arguments[fallback],
      actual.ity(),
      span,
    )
    remaining = remaining - 1
  }
  let typed = pending.map(expression => {
    match expression {
      Some(expression) => expression
      None => abort("pure application inference left an untyped argument")
    }
  })
  let result_ity = instantiate_program_result(
    self.context,
    substitution,
    formal_result,
    span,
  )
  let proxies : Array[(@mlw.PVariable, @mlw.Expr?)] = []
  let variables : Array[@mlw.PVariable] = []
  for index = typed.length() - 1; index >= 0; index = index - 1 {
    let argument = typed[index]
    let proxy = self.proxy_argument(
      argument,
      source_span(arguments[index].span),
    )
    proxies.push(proxy)
    variables.push(proxy.0)
  }
  proxies.rev_in_place()
  variables.rev_in_place()
  let application = @mlw.Expr::pure_application(
    self.context,
    symbol,
    variables,
    result_ity,
    pure_space.find_logic([b"infix ="], span),
    pure_space.find_logic([b"True"], span),
    program_origin(decoration),
    decoration.attributes,
    span,
  )
  self.wrap_argument_proxies(proxies, application, decoration)
}

///|
fn ProgramTyping::partial_pure_application(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  symbol : @logic.LSymbol,
  arguments : ArrayView[@parser.Expr],
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  let symbol_view = symbol.view()
  if arguments.length() >= symbol_view.argument_types.length() {
    @logic.fail_type(
      ArityMismatch,
      span,
      "partial pure application must leave at least one parameter",
    )
  }
  let function_type = program_space.find_type([b"infix ->"], span) catch {
    @mlw.MlwError(diagnostic) =>
      if diagnostic.kind == @mlw.UnboundProgramName {
        @logic.fail_type(
          TypeMismatch,
          span,
          "partial pure application has the wrong function type",
        )
      } else {
        raise @mlw.MlwError(diagnostic)
      }
  }
  let formal_arguments = symbol_view.argument_types.map(argument => {
    @mlw.Ity::from_ty(program_space, argument, span)
  })
  let formal_result = match symbol_view.result_type {
    Some(result) => @mlw.Ity::from_ty(program_space, result, span)
    None => self.boolean_ity(pure_space, program_space, span)
  }
  let mut formal_value = formal_result
  for index = formal_arguments.length() - 1
      index >= arguments.length()
      index = index - 1 {
    formal_value = program_function_ity(
      function_type,
      formal_arguments[index],
      formal_value,
      span,
    )
  }
  let mut substitution = @mlw.ItySubstitution::empty()
  if expected is Some(expected) {
    substitution = substitution.match_ity(formal_value, expected, span) catch {
      @mlw.MlwError(diagnostic) =>
        if diagnostic.kind == @mlw.ProgramTypeMismatch {
          @logic.fail_type(
            TypeMismatch,
            span,
            "partial pure application has the wrong function type",
          )
        } else {
          raise @mlw.MlwError(diagnostic)
        }
    }
  }
  let typed : Array[@mlw.Expr] = []
  for index, argument in arguments {
    let formal = formal_arguments[index]
    let (next, argument_expected) = instantiate_program_expected(
      self.context,
      substitution,
      formal,
      span,
    )
    substitution = next
    let actual = self.type_program_expression_expected(
      pure_space,
      program_space,
      locals,
      argument,
      Some(argument_expected),
    )
    typed.push(actual)
    substitution = substitution.match_ity(formal, actual.ity(), span)
  }
  let remaining_types : Array[@mlw.Ity] = []
  for index = arguments.length()
      index < formal_arguments.length()
      index = index + 1 {
    remaining_types.push(
      instantiate_program_result(
        self.context,
        substitution,
        formal_arguments[index],
        span,
      ),
    )
  }
  let result = instantiate_program_result(
    self.context,
    substitution,
    formal_result,
    span,
  )
  let proxies : Array[(@mlw.PVariable, @mlw.Expr?)] = []
  let supplied : Array[@mlw.PVariable] = []
  for index, argument in typed {
    let proxy = self.proxy_argument(
      argument,
      source_span(arguments[index].span),
      ghost=true,
    )
    proxies.push(proxy)
    supplied.push(proxy.0)
  }
  let remaining : Array[@mlw.PVariable] = []
  for argument_type in remaining_types {
    remaining.push(
      @mlw.PVariable::trusted_new(
        self.context,
        @theory.SemanticName::new(b"u", [], span),
        argument_type,
        false,
        span,
      ),
    )
  }
  let application = @logic.Term::elaborated_apply(
    symbol,
    [
      for argument in supplied + remaining => {
        @logic.Term::variable(argument.view().pure_symbol)
      }
    ],
    symbol_view.result_type,
    span,
  )
  let result_symbol = @logic.VSymbol::new(
    self.context,
    b"result",
    @identity.Origin::user(b"result", span, [b"mlw:proxy_symbol"]),
    result.to_ty(span),
    span,
  )
  let equality = pure_space.find_logic([b"infix ="], span)
  let formula = match symbol_view.result_type {
    Some(_) =>
      @logic.Term::elaborated_apply(
        equality,
        [@logic.Term::variable(result_symbol), application],
        None,
        span,
      )
    None => {
      let result_is_true = @logic.Term::elaborated_apply(
        equality,
        [
          @logic.Term::variable(result_symbol),
          program_boolean_term(pure_space, true, span),
        ],
        None,
        span,
      )
      @logic.Term::binary(Iff, result_is_true, application, span)
    }
  }
  let postcondition = @mlw.Postcondition::trusted_new(
    result_symbol, formula, span,
  )
  let cty = @mlw.Cty::new_with_variables(
    supplied + remaining,
    remaining,
    [],
    [postcondition],
    [],
    [],
    @mlw.Effect::pure(true).spoil(result),
    result,
    span,
  )
  let computation = @mlw.Cexp::trusted_new(Cpur(symbol, supplied), cty, span)
  let value = @mlw.Expr::execute_function_value(
    computation,
    self.context,
    function_type,
    pure_space.find_logic([b"infix @"], span),
    program_origin(decoration),
    decoration.attributes,
    span,
  )
  self.wrap_argument_proxies(proxies, value, decoration)
}

///|
fn ProgramTyping::resolved_application(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  path : ArrayView[Bytes],
  arguments : ArrayView[@parser.Expr],
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let routines = program_space.find_routine_candidates(path)
  let pure_function = try {
    let symbol = pure_space.find_logic(path, Some(decoration.location))
    if symbol.view().role is Projection {
      None
    } else {
      Some(symbol)
    }
  } catch {
    _ => None
  }
  let generated_projections_only = !routines.is_empty() &&
    routines.all(routine => {
      routine.view().logic is RLls(symbol) && symbol.view().role is Projection
    })
  if pure_function is Some(_) &&
    (routines.is_empty() || generated_projections_only) {
    return self.pure_application(
      pure_space, program_space, locals, path, arguments, decoration, expected,
    )
  }
  if path.length() == 1 &&
    !arguments.is_empty() &&
    !program_expression_needs_expected_type(program_space, locals, arguments[0]) {
    let receiver_type = Some(
      self
      .type_program_expression(pure_space, program_space, locals, arguments[0])
      .ity(),
    ) catch {
      _ => None
    }
    if receiver_type is Some(receiver_type) &&
      program_ity_head_symbol(receiver_type) is Some(symbol) {
      let fields = symbol.view().mutable_fields.to_owned() +
        symbol.view().immutable_fields.to_owned()
      for field in fields {
        if field.view().name.view().name == path[0] {
          let projection = Some(
            program_space.find_projection_by_field(
              field,
              Some(decoration.location),
            ),
          ) catch {
            @mlw.MlwError(_) => None
          }
          if projection is Some(projection) {
            return self.resolved_routine_application(
              pure_space, program_space, locals, projection, arguments, decoration,
              expected,
            )
          }
        }
      }
    }
  }
  match routines {
    [] =>
      self.pure_application(
        pure_space, program_space, locals, path, arguments, decoration, expected,
      )
    [routine] =>
      self.resolved_routine_application(
        pure_space, program_space, locals, routine, arguments, decoration, expected,
      )
    routines =>
      self.overloaded_routine_application(
        pure_space, program_space, locals, routines, arguments, decoration, expected,
      )
  }
}

///|
fn ProgramTyping::negate_boolean_expression(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  condition : @mlw.Expr,
  decoration : ProgramDecoration,
) -> @mlw.Expr raise {
  let boolean = self.boolean_ity(
    pure_space,
    program_space,
    Some(decoration.location),
  )
  let false_value = self.zero_argument_pure_expression(
    pure_space,
    program_space,
    b"False",
    boolean,
    decoration,
    synthesized=true,
  )
  let true_value = self.zero_argument_pure_expression(
    pure_space,
    program_space,
    b"True",
    boolean,
    decoration,
    synthesized=true,
  )
  @mlw.Expr::if_then_else(
    condition,
    false_value,
    true_value,
    boolean,
    program_origin(decoration),
    decoration.attributes,
    Some(decoration.location),
  )
}

///|
fn ProgramTyping::resolved_relation_application(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  left : @parser.Expr,
  operator : @parser.Ident,
  right : @parser.Expr,
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let resolved_name = if operator.name == b"infix <>" {
    b"infix ="
  } else {
    operator.name
  }
  let comparison = self.resolved_application(
    pure_space,
    program_space,
    locals,
    [resolved_name],
    [left, right],
    decoration,
    expected,
  )
  if operator.name == b"infix <>" {
    self.negate_boolean_expression(
      pure_space, program_space, comparison, decoration,
    )
  } else {
    comparison
  }
}

///|
fn ProgramTyping::program_relation_chain(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  left : @parser.Expr,
  operator : @parser.Ident,
  tail : @parser.Expr,
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let boolean = self.boolean_ity(
    pure_space,
    program_space,
    Some(decoration.location),
  )
  guard tail.desc is Einfix(middle, next_operator, rest) else {
    return self.resolved_relation_application(
      pure_space, program_space, locals, left, operator, tail, decoration, expected,
    )
  }
  let usable_preliminary = fn(
    source : @parser.Expr,
    typed : @mlw.Expr?,
  ) -> @mlw.Expr? {
    match typed {
      Some(typed) if !program_expression_is_untyped_constant(source) &&
        !program_ity_has_inference_variables(typed.ity()) => Some(typed)
      _ => None
    }
  }
  let preliminary_left = usable_preliminary(
    left,
    Some(self.type_program_expression(pure_space, program_space, locals, left)) catch {
      _ => None
    },
  )
  let preliminary_middle = usable_preliminary(
    middle,
    Some(
      self.type_program_expression(pure_space, program_space, locals, middle),
    ) catch {
      _ => None
    },
  )
  let (typed_left, typed_middle) = match
    (preliminary_left, preliminary_middle) {
    (Some(typed_left), Some(typed_middle)) => (typed_left, typed_middle)
    (Some(typed_left), None) =>
      (
        typed_left,
        self.type_program_expression_expected(
          pure_space,
          program_space,
          locals,
          middle,
          Some(typed_left.ity()),
        ),
      )
    (None, Some(typed_middle)) =>
      (
        self.type_program_expression_expected(
          pure_space,
          program_space,
          locals,
          left,
          Some(typed_middle.ity()),
        ),
        typed_middle,
      )
    (None, None) => {
      let typed_left = self.type_program_expression(
        pure_space, program_space, locals, left,
      )
      (
        typed_left,
        self.type_program_expression_expected(
          pure_space,
          program_space,
          locals,
          middle,
          Some(typed_left.ity()),
        ),
      )
    }
  }
  let left_proxy = self.proxy_argument(typed_left, source_span(left.span))
  let middle_proxy = self.proxy_argument(typed_middle, source_span(middle.span))
  let left_name = b"\x00relation_left"
  let middle_name = b"\x00relation_middle"
  let nested = locals.to_owned()
  nested.push(
    (left_name, self.program_local_from_variable(left_proxy.0, left.span)),
  )
  nested.push(
    (middle_name, self.program_local_from_variable(middle_proxy.0, middle.span)),
  )
  let left_ident = @parser.Ident::{
    name: left_name,
    attributes: [],
    span: left.span,
  }
  let middle_ident = @parser.Ident::{
    name: middle_name,
    attributes: [],
    span: middle.span,
  }
  let left_source = @parser.Expr::{
    desc: Eident(Qident(left_ident)),
    span: left.span,
  }
  let middle_source = @parser.Expr::{
    desc: Eident(Qident(middle_ident)),
    span: middle.span,
  }
  let first = self.resolved_relation_application(
    pure_space,
    program_space,
    nested,
    left_source,
    operator,
    middle_source,
    decoration,
    Some(boolean),
  )
  let remaining = self.program_relation_chain(
    pure_space,
    program_space,
    nested,
    middle_source,
    next_operator,
    rest,
    { ..decoration, location: source_span(tail.span) },
    Some(boolean),
  )
  let false_value = self.zero_argument_pure_expression(
    pure_space,
    program_space,
    b"False",
    boolean,
    decoration,
    synthesized=true,
  )
  let conjunction = @mlw.Expr::if_then_else(
    first,
    remaining,
    false_value,
    boolean,
    program_origin(decoration),
    decoration.attributes,
    Some(decoration.location),
  )
  self.wrap_argument_proxies(
    [left_proxy, middle_proxy],
    conjunction,
    decoration,
  )
}

///|
fn program_expression_needs_expected(expression : @parser.Expr) -> Bool {
  match expression.desc {
    Eraise(_, _) | Eabsurd => true
    Esequence(_, body) | Elet(_, _, _, _, body) | Erec(_, body) =>
      program_expression_needs_expected(body)
    Eif(_, consequent, alternative) =>
      program_expression_needs_expected(consequent) &&
      program_expression_needs_expected(alternative)
    Escope(_, inner)
    | Elabel(_, inner)
    | Eghost(inner)
    | Eattr(_, inner)
    | Eexn(_, _, _, inner)
    | Eoptexn(_, _, inner) => program_expression_needs_expected(inner)
    _ => false
  }
}

///|
fn program_expression_provides_named_unit_result(
  expression : @parser.Expr,
  unit_routines : ArrayView[Bytes],
) -> Bool {
  let recurse = fn(nested) {
    program_expression_provides_named_unit_result(nested, unit_routines)
  }
  match expression.desc {
    Etuple([])
    | Ewhile(_, _, _, _)
    | Efor(_, _, _, _, _, _)
    | Eassign(_)
    | Eassert(_, _) => true
    Esequence(_, body)
    | Elet(_, _, _, _, body)
    | Erec(_, body)
    | Escope(_, body)
    | Elabel(_, body)
    | Eghost(body)
    | Eattr(_, body)
    | Ecast(body, _)
    | Eexn(_, _, _, body)
    | Eoptexn(_, _, body) => recurse(body)
    Eif(_, consequent, alternative) =>
      recurse(consequent) || recurse(alternative)
    Ematch(scrutinee, regular, exceptional) =>
      recurse(scrutinee) ||
      regular.any(branch => recurse(branch.body)) ||
      exceptional.any(branch => recurse(branch.body))
    Eident(path) => unit_routines.any(name => name == qualid_last(path).name)
    Eidapp(path, _) => unit_routines.any(name => name == qualid_last(path).name)
    Eapply(_, _) => {
      let arguments : Array[@parser.Expr] = []
      let head = collect_program_application(expression, arguments)
      match head.desc {
        Eident(path) | Eidapp(path, _) =>
          unit_routines.any(name => name == qualid_last(path).name)
        _ => false
      }
    }
    _ => false
  }
}

///|
fn program_expression_provides_unit_result(expression : @parser.Expr) -> Bool {
  program_expression_provides_named_unit_result(expression, [])
}

///|
fn direct_unqualified_program_call_name(expression : @parser.Expr) -> Bytes? {
  match expression.desc {
    Eident(Qident(ident)) | Eidapp(Qident(ident), _) => Some(ident.name)
    Eapply(_, _) => {
      let arguments : Array[@parser.Expr] = []
      let head = collect_program_application(expression, arguments)
      match head.desc {
        Eident(Qident(ident)) | Eidapp(Qident(ident), _) => Some(ident.name)
        _ => None
      }
    }
    _ => None
  }
}

///|
fn collect_recursive_result_calls(
  expression : @parser.Expr,
  group_names : ArrayView[Bytes],
  calls : Array[Bytes],
) -> Unit {
  match direct_unqualified_program_call_name(expression) {
    Some(name) if group_names.any(candidate => candidate == name) => {
      if !calls.any(existing => existing == name) {
        calls.push(name)
      }
      return
    }
    Some(_) | None => ()
  }
  let recurse = fn(nested) {
    collect_recursive_result_calls(nested, group_names, calls)
  }
  match expression.desc {
    Eif(_, consequent, alternative) => {
      recurse(consequent)
      recurse(alternative)
    }
    Ematch(_, regular, exceptional) => {
      for branch in regular {
        recurse(branch.body)
      }
      for branch in exceptional {
        recurse(branch.body)
      }
    }
    Esequence(_, body)
    | Elet(_, _, _, _, body)
    | Erec(_, body)
    | Escope(_, body)
    | Elabel(_, body)
    | Eghost(body)
    | Eattr(_, body)
    | Ecast(body, _)
    | Eexn(_, _, _, body)
    | Eoptexn(_, _, body) => recurse(body)
    Eraise(path, Some(payload)) if qualid_last(path).name == b"'Return" =>
      recurse(payload)
    Eref
    | Etrue
    | Efalse
    | Econst(_)
    | Eident(_)
    | Easref(_)
    | Epure(_)
    | Eidpur(_)
    | Eidapp(_, _)
    | Eapply(_, _)
    | Einfix(_, _, _)
    | Einnfix(_, _, _)
    | Efun(_, _, _, _, _, _)
    | Eany(_, _, _, _, _, _)
    | Etuple(_)
    | Erecord(_)
    | Eupdate(_, _)
    | Eassign(_)
    | Ewhile(_, _, _, _)
    | Efor(_, _, _, _, _, _)
    | Eraise(_, _)
    | Eand(_, _)
    | Eor(_, _)
    | Enot(_)
    | Eabsurd
    | Eassert(_, _) => ()
  }
}

///|
fn program_result_needs_group_constraint(ity : @mlw.Ity) -> Bool {
  match ity.view() {
    ItyVar(variable) => variable.name() == b"xi"
    ItyApp(_, _, _) | ItyReg(_) => false
  }
}

///|
fn program_loop_bound_needs_expected(expression : @parser.Expr) -> Bool {
  match expression.desc {
    Econst(_) | Eraise(_, _) | Eabsurd => true
    Escope(_, inner)
    | Elabel(_, inner)
    | Eghost(inner)
    | Eattr(_, inner)
    | Eexn(_, _, _, inner)
    | Eoptexn(_, _, inner) => program_loop_bound_needs_expected(inner)
    Ecast(_, _) => false
    _ => false
  }
}

///|
fn program_expression_returns_name(
  expression : @parser.Expr,
  name : BytesView,
) -> Bool {
  match expression.desc {
    Eident(Qident(ident)) | Easref(Qident(ident)) => ident.name[:] == name
    Esequence(_, body)
    | Elabel(_, body)
    | Escope(_, body)
    | Ecast(body, _)
    | Eattr(_, body)
    | Eghost(body)
    | Eexn(_, _, _, body)
    | Eoptexn(_, _, body) => program_expression_returns_name(body, name)
    Elet(ident, _, _, _, body) =>
      ident.name[:] != name && program_expression_returns_name(body, name)
    Eif(_, consequent, alternative) =>
      program_expression_returns_name(consequent, name) &&
      program_expression_returns_name(alternative, name)
    Ematch(_, regular, exceptional) =>
      !regular.is_empty() &&
      regular.all(branch => program_expression_returns_name(branch.body, name)) &&
      exceptional.all(branch => {
        program_expression_returns_name(branch.body, name)
      })
    _ => false
  }
}

///|
fn program_expression_returns_implicit_read(
  expression : @parser.Expr,
  name : BytesView,
) -> Bool {
  match expression.desc {
    Eident(Qident(ident)) => ident.name[:] == name
    Eidapp(path, [argument]) =>
      qualid_last(path).name == b"prefix !" &&
      program_expression_returns_name(argument, name)
    Eapply({ desc: Eident(path), .. }, argument) =>
      qualid_last(path).name == b"prefix !" &&
      program_expression_returns_name(argument, name)
    Esequence(_, body)
    | Elabel(_, body)
    | Escope(_, body)
    | Ecast(body, _)
    | Eattr(_, body)
    | Eghost(body)
    | Eexn(_, _, _, body)
    | Eoptexn(_, _, body) =>
      program_expression_returns_implicit_read(body, name)
    Elet(ident, _, _, _, body) =>
      ident.name[:] != name &&
      program_expression_returns_implicit_read(body, name)
    Eif(_, consequent, alternative) =>
      program_expression_returns_implicit_read(consequent, name) &&
      program_expression_returns_implicit_read(alternative, name)
    Ematch(_, regular, exceptional) =>
      !regular.is_empty() &&
      regular.all(branch => {
        program_expression_returns_implicit_read(branch.body, name)
      }) &&
      exceptional.all(branch => {
        program_expression_returns_implicit_read(branch.body, name)
      })
    _ => false
  }
}

///|
fn program_reference_initializer(expression : @parser.Expr) -> @parser.Expr? {
  match expression.desc {
    Eapply({ desc: Eref, .. }, argument) => Some(argument)
    Eidapp(path, [argument]) if qualid_last(path).name == b"ref" =>
      Some(argument)
    Eapply({ desc: Eident(path), .. }, argument) if qualid_last(path).name ==
      b"ref" => Some(argument)
    Escope(_, inner) | Elabel(_, inner) | Eghost(inner) | Eattr(_, inner) =>
      program_reference_initializer(inner)
    _ => None
  }
}

///|
fn program_expression_is_untyped_constant(expression : @parser.Expr) -> Bool {
  match expression.desc {
    Econst(_) => true
    Escope(_, inner) | Elabel(_, inner) | Eghost(inner) | Eattr(_, inner) =>
      program_expression_is_untyped_constant(inner)
    _ => false
  }
}

///|
fn program_expression_is_untyped_numeric_constant(
  expression : @parser.Expr,
) -> Bool {
  match expression.desc {
    Econst(ConstInt(_) | ConstReal(_)) => true
    Escope(_, inner) | Elabel(_, inner) | Eghost(inner) | Eattr(_, inner) =>
      program_expression_is_untyped_numeric_constant(inner)
    _ => false
  }
}

///|
fn program_expression_is_reference_read(
  expression : @parser.Expr,
  name : BytesView,
) -> Bool {
  match expression.desc {
    Eident(Qident(ident)) => ident.name[:] == name
    Eidapp(path, [argument]) =>
      qualid_last(path).name == b"prefix !" &&
      program_expression_returns_name(argument, name)
    Eapply({ desc: Eident(path), .. }, argument) =>
      qualid_last(path).name == b"prefix !" &&
      program_expression_returns_name(argument, name)
    Escope(_, inner) | Elabel(_, inner) | Eghost(inner) | Eattr(_, inner) =>
      program_expression_is_reference_read(inner, name)
    _ => false
  }
}

///|
fn program_expression_contains_untyped_constant(
  expression : @parser.Expr,
) -> Bool {
  let contains = fn(nested) {
    program_expression_contains_untyped_constant(nested)
  }
  match expression.desc {
    Econst(_) => true
    Eapply(function_, argument)
    | Einfix(function_, _, argument)
    | Einnfix(function_, _, argument)
    | Eand(function_, argument)
    | Eor(function_, argument)
    | Esequence(function_, argument) =>
      contains(function_) || contains(argument)
    Eidapp(_, arguments) | Etuple(arguments) => arguments.any(contains)
    Eif(condition, consequent, alternative) =>
      contains(condition) || contains(consequent) || contains(alternative)
    Erecord(fields) => fields.any(field => contains(field.1))
    Eupdate(source, fields) =>
      contains(source) || fields.any(field => contains(field.1))
    Escope(_, inner)
    | Elabel(_, inner)
    | Eghost(inner)
    | Eattr(_, inner)
    | Ecast(inner, _)
    | Eexn(_, _, _, inner)
    | Eoptexn(_, _, inner) => contains(inner)
    _ => false
  }
}

///|
fn ProgramTyping::reference_read_routine_expected(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  routine : @mlw.RoutineSymbol,
  arguments : ArrayView[@parser.Expr],
  target_indices : ArrayView[Int],
  span : @identity.SourceSpan?,
) -> @mlw.Ity? raise {
  let cty = routine.view().cty.view()
  if arguments.length() != cty.arguments.length() {
    return None
  }
  let mut substitution = cty.freeze
  let literal_indices : Array[Int] = []
  let mut constrained = false
  for index, argument in arguments {
    if target_indices.any(target => target == index) {
      continue
    }
    if program_expression_is_untyped_constant(argument) {
      literal_indices.push(index)
      continue
    }
    let actual = self.partially_inferred_program_expression_type(
      pure_space, program_space, locals, argument,
    ) catch {
      _ => None
    }
    if actual is Some(actual) {
      let matched = Some(
        substitution.match_ity(cty.arguments[index].view().ity, actual, span),
      ) catch {
        @mlw.MlwError(_) => None
      }
      if matched is Some(matched) {
        substitution = matched
        constrained = true
      } else {
        return None
      }
    }
  }
  let target = cty.arguments[target_indices[0]].view().ity
  let declared_target = target.is_closed()
  if (constrained || declared_target) &&
    try_instantiate_program_type(substitution, target, span) is Some(inferred) {
    return Some(inferred)
  }
  if !constrained && !declared_target {
    return None
  }
  for index in literal_indices {
    let typed = try {
      let (next, argument_expected) = instantiate_program_expected(
        self.context,
        substitution,
        cty.arguments[index].view().ity,
        span,
      )
      let actual = self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        arguments[index],
        Some(argument_expected),
      )
      Some((next, actual.ity()))
    } catch {
      _ => None
    }
    if typed is Some((next, actual)) {
      let matched = Some(
        next.match_ity(cty.arguments[index].view().ity, actual, span),
      ) catch {
        @mlw.MlwError(_) => None
      }
      guard matched is Some(next) else { return None }
      substitution = next
    }
  }
  try_instantiate_program_type(substitution, target, span)
}

///|
fn ProgramTyping::reference_read_application_expected(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  name : BytesView,
  path : ArrayView[Bytes],
  arguments : ArrayView[@parser.Expr],
  span : @identity.SourceSpan?,
) -> @mlw.Ity? raise {
  // The formal argument of `prefix !` is the reference container itself,
  // whereas this scanner is inferring the type stored in that container.
  // Its surrounding application supplies the useful content constraint.
  if path is [operator] && operator == b"prefix !" {
    return None
  }
  let target_indices : Array[Int] = []
  for index, argument in arguments {
    if program_expression_is_reference_read(argument, name) {
      target_indices.push(index)
    }
  }
  if target_indices.is_empty() {
    return None
  }
  let assignment_target = path is [operator] &&
    operator == b"infix :=" &&
    target_indices.any(index => index == 0)
  if assignment_target &&
    arguments is [_, value] &&
    program_expression_is_untyped_constant(value) {
    return None
  }
  if assignment_target && arguments is [_, value] {
    let content = self.partially_inferred_program_expression_type(
      pure_space, program_space, locals, value,
    )
    if content is Some(content) && !program_ity_has_inference_variables(content) {
      return Some(content)
    }
  }
  let inferred : Array[@mlw.Ity] = []
  for routine in program_space.find_routine_candidates(path) {
    match
      self.reference_read_routine_expected(
        pure_space, program_space, locals, routine, arguments, target_indices, span,
      ) {
      Some(candidate) => {
        let candidate = if assignment_target {
          program_ity_reference_content(candidate)
        } else {
          Some(candidate)
        }
        if candidate is Some(candidate) &&
          !inferred.any(existing => existing == candidate) {
          inferred.push(candidate)
        }
      }
      None => ()
    }
  }
  match inferred {
    [candidate] => Some(candidate)
    _ => None
  }
}

///|
fn ProgramTyping::direct_local_routine_expected(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  name : BytesView,
  routine : @mlw.RoutineSymbol,
  arguments : ArrayView[@parser.Expr],
  span : @identity.SourceSpan?,
  result_expected? : @mlw.Ity? = None,
) -> @mlw.Ity? raise {
  let cty = routine.view().cty.view()
  if arguments.length() != cty.arguments.length() {
    return None
  }
  let target_indices : Array[Int] = []
  for index, argument in arguments {
    if program_expression_returns_name(argument, name) {
      target_indices.push(index)
    }
  }
  if target_indices.is_empty() {
    return None
  }
  let mut substitution = cty.freeze
  if result_expected is Some(result_expected) {
    substitution = substitution.match_ity(cty.result, result_expected, span) catch {
      @mlw.MlwError(_) => return None
    }
  }
  let literal_indices : Array[Int] = []
  for index, argument in arguments {
    if target_indices.any(target => target == index) {
      continue
    }
    if program_expression_is_untyped_constant(argument) {
      literal_indices.push(index)
      continue
    }
    let actual = Some(
      self
      .type_program_expression(pure_space, program_space, locals, argument)
      .ity(),
    ) catch {
      _ => None
    }
    if actual is Some(actual) {
      let matched = Some(
        substitution.match_ity(cty.arguments[index].view().ity, actual, span),
      ) catch {
        @mlw.MlwError(_) => None
      }
      if matched is Some(matched) {
        substitution = matched
      } else {
        return None
      }
    }
  }
  let target = cty.arguments[target_indices[0]].view().ity
  if try_instantiate_program_type(substitution, target, span) is Some(inferred) &&
    !program_ity_has_inference_variables(inferred) {
    return Some(inferred)
  }
  for index in literal_indices {
    let typed = try {
      let (next, argument_expected) = instantiate_program_expected(
        self.context,
        substitution,
        cty.arguments[index].view().ity,
        span,
      )
      let actual = self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        arguments[index],
        Some(argument_expected),
      )
      Some((next, actual.ity()))
    } catch {
      _ => None
    }
    if typed is Some((next, actual)) {
      let matched = Some(
        next.match_ity(cty.arguments[index].view().ity, actual, span),
      ) catch {
        @mlw.MlwError(_) => None
      }
      guard matched is Some(next) else { return None }
      substitution = next
    }
  }
  let inferred = match
    try_instantiate_program_type(substitution, target, span) {
    Some(inferred) => inferred
    None =>
      substitution.instantiate_inference_expected(self.context, target, span).1
  }
  if program_ity_has_inference_variables(inferred) {
    None
  } else {
    Some(inferred)
  }
}

///|
fn ProgramTyping::direct_local_application_expected(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  name : BytesView,
  path : ArrayView[Bytes],
  arguments : ArrayView[@parser.Expr],
  span : @identity.SourceSpan?,
  result_expected? : @mlw.Ity? = None,
) -> @mlw.Ity? raise {
  let inferred : Array[@mlw.Ity] = []
  for routine in program_space.find_routine_candidates(path) {
    match
      self.direct_local_routine_expected(
        pure_space,
        program_space,
        locals,
        name,
        routine,
        arguments,
        span,
        result_expected~,
      ) {
      Some(candidate) =>
        if !inferred.any(existing => existing == candidate) {
          inferred.push(candidate)
        }
      None => ()
    }
  }
  match inferred {
    [candidate] => Some(candidate)
    _ => None
  }
}

///|
fn ProgramTyping::nested_local_routine_expected(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  name : BytesView,
  routine : @mlw.RoutineSymbol,
  arguments : ArrayView[@parser.Expr],
  span : @identity.SourceSpan?,
  skeleton : @mlw.Ity?,
  result_expected : @mlw.Ity?,
) -> @mlw.Ity? raise {
  let cty = routine.view().cty.view()
  if arguments.length() != cty.arguments.length() {
    return None
  }
  let targets = arguments.map(argument => {
    program_expression_mentions_name(argument, name)
  })
  if !targets.any(target => target) {
    return None
  }
  let mut substitution = cty.freeze
  if result_expected is Some(result_expected) {
    substitution = substitution.match_ity(cty.result, result_expected, span) catch {
      @mlw.MlwError(_) => return None
    }
  }
  for index, argument in arguments {
    if targets[index] {
      continue
    }
    let typed = try {
      let (next, expected) = instantiate_program_expected(
        self.context,
        substitution,
        cty.arguments[index].view().ity,
        span,
      )
      let actual = self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        argument,
        Some(expected),
      )
      Some((next, actual.ity()))
    } catch {
      _ => None
    }
    guard typed is Some((next, actual)) else { return None }
    substitution = next.match_ity(cty.arguments[index].view().ity, actual, span) catch {
      @mlw.MlwError(_) => return None
    }
  }
  let inferred : Array[@mlw.Ity] = []
  for index, argument in arguments {
    if !targets[index] {
      continue
    }
    let expected = instantiate_program_expected(
        self.context,
        substitution,
        cty.arguments[index].view().ity,
        span,
      ).1 catch {
        _ => continue
      }
    match
      self.local_initializer_expected(
        pure_space,
        program_space,
        locals,
        name,
        argument,
        skeleton~,
        expression_expected=Some(expected),
      ) {
      Some(candidate) =>
        if !inferred.any(existing => existing == candidate) {
          inferred.push(candidate)
        }
      None => ()
    }
  }
  match inferred {
    [candidate] => Some(candidate)
    _ => None
  }
}

///|
fn ProgramTyping::nested_local_application_expected(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  name : BytesView,
  path : ArrayView[Bytes],
  arguments : ArrayView[@parser.Expr],
  span : @identity.SourceSpan?,
  skeleton : @mlw.Ity?,
  result_expected : @mlw.Ity?,
) -> @mlw.Ity? raise {
  guard result_expected is Some(result_expected) &&
    !result_expected.free_type_variables().is_empty() else {
    return None
  }
  let inferred : Array[@mlw.Ity] = []
  for routine in program_space.find_routine_candidates(path) {
    match
      self.nested_local_routine_expected(
        pure_space,
        program_space,
        locals,
        name,
        routine,
        arguments,
        span,
        skeleton,
        Some(result_expected),
      ) {
      Some(candidate) =>
        if !inferred.any(existing => existing == candidate) {
          inferred.push(candidate)
        }
      None => ()
    }
  }
  match inferred {
    [candidate] => Some(candidate)
    _ => None
  }
}

///|
fn ProgramTyping::partially_inferred_program_routine_result(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  routine : @mlw.RoutineSymbol,
  arguments : ArrayView[@parser.Expr],
  span : @identity.SourceSpan?,
) -> @mlw.Ity? raise {
  let cty = routine.view().cty.view()
  if arguments.length() != cty.arguments.length() {
    return None
  }
  let mut substitution = cty.freeze
  let result_initially_concrete = try_instantiate_program_type(
      substitution,
      cty.result,
      span,
    )
    is Some(_)
  let literal_indices : Array[Int] = []
  for index, argument in arguments {
    if program_expression_is_untyped_constant(argument) {
      literal_indices.push(index)
      continue
    }
    let actual = match
      try_instantiate_program_type(
        substitution,
        cty.arguments[index].view().ity,
        span,
      ) {
      Some(expected) =>
        Some(
          self
          .type_program_expression_expected(
            pure_space,
            program_space,
            locals,
            argument,
            Some(expected),
          )
          .ity(),
        ) catch {
          _ => if result_initially_concrete { return None } else { None }
        }
      None if program_expression_needs_expected_type(
          program_space, locals, argument,
        ) => None
      None =>
        Some(
          self
          .type_program_expression(pure_space, program_space, locals, argument)
          .ity(),
        ) catch {
          _ => if result_initially_concrete { return None } else { None }
        }
    }
    if actual is Some(actual) {
      let matched = Some(
        substitution.match_ity(cty.arguments[index].view().ity, actual, span),
      ) catch {
        @mlw.MlwError(_) => None
      }
      guard matched is Some(next) else { return None }
      substitution = next
    }
  }
  if try_instantiate_program_type(substitution, cty.result, span)
    is Some(inferred) {
    return Some(inferred)
  }
  for index in literal_indices {
    let actual = Some(
      self
      .type_program_expression(
        pure_space,
        program_space,
        locals,
        arguments[index],
      )
      .ity(),
    ) catch {
      _ => None
    }
    if actual is Some(actual) {
      let matched = Some(
        substitution.match_ity(cty.arguments[index].view().ity, actual, span),
      ) catch {
        @mlw.MlwError(_) => None
      }
      guard matched is Some(next) else { return None }
      substitution = next
    }
  }
  try_instantiate_program_type(substitution, cty.result, span)
}

///|
fn ProgramTyping::partially_inferred_program_expression_type(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  expression : @parser.Expr,
) -> @mlw.Ity? raise {
  let span = Some(source_span(expression.span))
  let (path, arguments) = match expression.desc {
    Eidapp(path, arguments) => (qualid_segments(path), arguments)
    Einfix(left, operator, right) | Einnfix(left, operator, right) =>
      ([operator.name], [left, right])
    Eapply(_, _) => {
      let reversed : Array[@parser.Expr] = []
      let head = collect_program_application(expression, reversed)
      let arguments = reversed.rev()
      match head.desc {
        Eident(path) => (qualid_segments(path), arguments)
        Eidapp(path, initial) => {
          let all = initial.copy()
          all.push_iter(arguments.iter())
          (qualid_segments(path), all)
        }
        Eref => ([b"ref"], arguments)
        _ => return None
      }
    }
    Escope(scope, body) => {
      let scope_span = Some(qualid_span(scope))
      return self.partially_inferred_program_expression_type(
        pure_space.open_scope(qualid_segments(scope), scope_span),
        program_space.open_scope(qualid_segments(scope), scope_span),
        locals,
        body,
      )
    }
    Elabel(_, body) | Eghost(body) | Eattr(_, body) =>
      return self.partially_inferred_program_expression_type(
        pure_space, program_space, locals, body,
      )
    _ =>
      return Some(
        self
        .type_program_expression(pure_space, program_space, locals, expression)
        .ity(),
      ) catch {
        _ => None
      }
  }
  let inferred : Array[@mlw.Ity] = []
  for routine in program_space.find_routine_candidates(path) {
    match
      self.partially_inferred_program_routine_result(
        pure_space, program_space, locals, routine, arguments, span,
      ) {
      Some(candidate) =>
        if !inferred.any(existing => existing == candidate) {
          inferred.push(candidate)
        }
      None => ()
    }
  }
  match inferred {
    [candidate] => Some(candidate)
    [] =>
      Some(
        self
        .type_program_expression(pure_space, program_space, locals, expression)
        .ity(),
      ) catch {
        _ => None
      }
    _ => None
  }
}

///|
fn program_ity_has_inference_variables(ity : @mlw.Ity) -> Bool {
  ity
  .free_type_variables()
  .any(variable => {
    variable
    .origin()
    .attributes()
    .any(attribute => attribute == b"mlw:inference_type_variable")
  })
}

///|
fn ProgramTyping::constrain_inferred_program_result(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  expression : @parser.Expr,
  delayed_result : Dty,
) -> Unit raise {
  let span = Some(source_span(expression.span))
  let candidate = self.partially_inferred_program_expression_type(
    pure_space, program_space, locals, expression,
  ) catch {
    _ => None
  }
  if candidate is Some(candidate) &&
    !program_ity_has_inference_variables(candidate) {
    self.pure.delayed.unify(
      delayed_result,
      self.pure.delayed.known(candidate.to_ty(span), span),
      span,
    )
    return
  }
  let recurse = fn(nested) raise {
    self.constrain_inferred_program_result(
      pure_space, program_space, locals, nested, delayed_result,
    )
  }
  match expression.desc {
    Eif(_, consequent, alternative) => {
      recurse(consequent)
      recurse(alternative)
    }
    Ematch(_, regular, exceptional) => {
      for branch in regular {
        recurse(branch.body)
      }
      for branch in exceptional {
        recurse(branch.body)
      }
    }
    Esequence(_, body)
    | Elet(_, _, _, _, body)
    | Erec(_, body)
    | Efun([], _, _, _, _, body)
    | Escope(_, body)
    | Elabel(_, body)
    | Eghost(body)
    | Eattr(_, body)
    | Ecast(body, _)
    | Eexn(_, _, _, body)
    | Eoptexn(_, _, body) => recurse(body)
    Eraise(path, payload) if qualid_last(path).name == b"'Return" =>
      match payload {
        Some(payload) => recurse(payload)
        None => {
          let unit = self.unit_ity(pure_space, program_space, span)
          self.pure.delayed.unify(
            delayed_result,
            self.pure.delayed.known(unit.to_ty(span), span),
            span,
          )
        }
      }
    Eraise(_, _)
    | Eabsurd
    | Eref
    | Etrue
    | Efalse
    | Econst(_)
    | Eident(_)
    | Easref(_)
    | Eidapp(_, _)
    | Eapply(_, _)
    | Einfix(_, _, _)
    | Einnfix(_, _, _)
    | Efun(_, _, _, _, _, _)
    | Eany(_, _, _, _, _, _)
    | Etuple(_)
    | Erecord(_)
    | Eupdate(_, _)
    | Eassign(_)
    | Ewhile(_, _, _, _)
    | Efor(_, _, _, _, _, _)
    | Eand(_, _)
    | Eor(_, _)
    | Enot(_)
    | Epure(_)
    | Eidpur(_)
    | Eassert(_, _) => ()
  }
}

///|
fn ProgramTyping::formula_local_expected(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  name : BytesView,
  formula : @parser.Term,
  skeleton? : @mlw.Ity? = None,
) -> @mlw.Ity? {
  try {
    let delayed = match skeleton {
      Some(skeleton) =>
        self.pure.delayed.specialize(
          skeleton.to_ty(Some(source_span(formula.span))),
          Map([]),
          Some(source_span(formula.span)),
        )
      None => self.pure.delayed.fresh()
    }
    let binding = self.pure.make_local(None, formula.span, delayed)
    let expanded = self.program_logic_mappings(program_space, formula.span)
    expanded.push_iter(locals.iter())
    let logical = program_logic_scope(expanded).0
    logical.push((name.to_owned(), binding))
    let typed = self.pure.type_term(pure_space, logical, formula)
    self.pure.expect_formula(pure_space, typed)
    let ty = self.pure.delayed.finalize_pure(
      delayed,
      Some(source_span(formula.span)),
    )
    Some(@mlw.Ity::from_ty(program_space, ty, Some(source_span(formula.span))))
  } catch {
    _ => None
  }
}

///|
fn ProgramTyping::formula_reference_content_expected(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  name : BytesView,
  formula : @parser.Term,
) -> @mlw.Ity? {
  for implicit_read in [false, true] {
    let inferred = try {
      let span = Some(source_span(formula.span))
      let content = self.pure.delayed.fresh()
      let reference = self.pure.delayed.app(
        pure_space.find_type([b"ref"], span),
        [content],
        span,
      )
      let ident = @parser.Ident::{
        name: name.to_owned(),
        attributes: if implicit_read {
          [@parser.Text(b"mlw:reference_var")]
        } else {
          []
        },
        span: formula.span,
      }
      let binding = self.pure.make_local(Some(ident), formula.span, reference)
      let expanded = self.program_logic_mappings(program_space, formula.span)
      expanded.push_iter(locals.iter())
      let logical = program_logic_scope(expanded).0
      logical.push((name.to_owned(), binding))
      let typed = self.pure.type_term(pure_space, logical, formula)
      self.pure.expect_formula(pure_space, typed)
      let ty = self.pure.delayed.finalize_pure(content, span)
      Some(@mlw.Ity::from_ty(program_space, ty, span))
    } catch {
      _ => None
    }
    if inferred is Some(inferred) {
      return Some(inferred)
    }
  }
  None
}

///|
fn ProgramTyping::initializer_scan_locals(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  ident : @parser.Ident,
  ghost : Bool,
  value : @parser.Expr,
) -> Array[(Bytes, ProgramLocal)] {
  let nested = locals.to_owned()
  if program_expression_is_untyped_numeric_constant(value) ||
    (
      program_reference_initializer(value) is Some(initializer) &&
      program_expression_is_untyped_constant(initializer)
    ) {
    return nested
  }
  let binding = try {
    let typed = self.type_program_expression(
      pure_space, program_space, locals, value,
    )
    if program_ity_has_inference_variables(typed.ity()) {
      None
    } else {
      Some(self.make_program_local(Some(ident), ident.span, typed.ity(), ghost))
    }
  } catch {
    _ => None
  }
  if binding is Some(binding) {
    nested.push((ident.name, binding))
  }
  nested
}

///|
fn ProgramTyping::initializer_scan_loop_locals(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  ident : @parser.Ident,
  first : @parser.Expr,
  last : @parser.Expr,
) -> Array[(Bytes, ProgramLocal)] {
  let index_source = if program_loop_bound_needs_expected(first) &&
    !program_loop_bound_needs_expected(last) {
    last
  } else {
    first
  }
  self.initializer_scan_locals(
    pure_space, program_space, locals, ident, false, index_source,
  )
}

///|
fn ProgramTyping::shadowed_local_return_expected(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  name : BytesView,
  expression : @parser.Expr,
  expected : @mlw.Ity,
) -> @mlw.Ity? raise {
  let recurse = fn(nested) raise {
    self.shadowed_local_return_expected(
      pure_space, program_space, locals, name, nested, expected,
    )
  }
  match expression.desc {
    Eident(Qident(ident)) if ident.name[:] == name => Some(expected)
    Esequence(_, body) => recurse(body)
    Elet(ident, ghost, _, value, body) =>
      if ident.name[:] == name {
        guard recurse(body) is Some(inner_expected) else { return None }
        let hypothetical = self.make_program_local(
          None,
          value.span,
          inner_expected,
          self.ghost_context || ghost,
        )
        let nested = locals.to_owned()
        nested.push((ident.name, hypothetical))
        let compatible = try {
          ignore(
            self.type_program_expression_expected(
              pure_space,
              program_space,
              nested,
              value,
              Some(inner_expected),
            ),
          )
          true
        } catch {
          _ => false
        }
        if compatible {
          Some(inner_expected)
        } else {
          None
        }
      } else {
        self.shadowed_local_return_expected(
          pure_space,
          program_space,
          self.initializer_scan_locals(
            pure_space, program_space, locals, ident, ghost, value,
          ),
          name,
          body,
          expected,
        )
      }
    Eif(_, consequent, alternative) =>
      match (recurse(consequent), recurse(alternative)) {
        (Some(left), Some(right)) if left == right => Some(left)
        _ => None
      }
    Escope(scope, body) => {
      let scope_span = Some(qualid_span(scope))
      self.shadowed_local_return_expected(
        pure_space.open_scope(qualid_segments(scope), scope_span),
        program_space.open_scope(qualid_segments(scope), scope_span),
        locals,
        name,
        body,
        expected,
      )
    }
    Efun([], _, _, _, _, body)
    | Elabel(_, body)
    | Eghost(body)
    | Eattr(_, body)
    | Ecast(body, _)
    | Eexn(_, _, _, body)
    | Eoptexn(_, _, body) => recurse(body)
    _ => None
  }
}

///|
fn ProgramTyping::assignment_local_value_expected(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  name : BytesView,
  assignment : @parser.Assignment,
) -> @mlw.Ity? {
  if !program_expression_returns_name(assignment.value, name) {
    return None
  }
  try {
    let (field, field_span) = match assignment.field {
      Some(field_path) =>
        (
          program_space.find_routine(
            qualid_segments(field_path),
            Some(qualid_span(field_path)),
          ),
          Some(qualid_span(field_path)),
        )
      None =>
        (
          program_space.find_routine(
            [b"contents"],
            Some(source_span(assignment.target.span)),
          ),
          Some(source_span(assignment.target.span)),
        )
    }
    guard field.view().logic is RLls(logic_symbol) &&
      logic_symbol.view().role is Projection else {
      return None
    }
    let target = self.type_program_expression(
      pure_space,
      program_space,
      locals,
      assignment.target,
    )
    let expected = self.routine_result_for_argument_types(
      field,
      [target.ity()],
      None,
      field_span,
    )
    if program_ity_has_inference_variables(expected) {
      None
    } else if expected.reachable_regions().is_empty() {
      Some(expected)
    } else {
      Some(freshen_program_expected_regions(self.context, expected, field_span))
    }
  } catch {
    _ => None
  }
}

///|
fn ProgramTyping::local_initializer_expected(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  name : BytesView,
  expression : @parser.Expr,
  skeleton? : @mlw.Ity? = None,
  expression_expected? : @mlw.Ity? = None,
) -> @mlw.Ity? raise {
  let scan = fn(nested) raise {
    self.local_initializer_expected(
      pure_space,
      program_space,
      locals,
      name,
      nested,
      skeleton~,
    )
  }
  let scan_expected = fn(nested, nested_expected) raise {
    self.local_initializer_expected(
      pure_space,
      program_space,
      locals,
      name,
      nested,
      skeleton~,
      expression_expected=nested_expected,
    )
  }
  match expression.desc {
    Eident(Qident(ident)) if ident.name[:] == name => expression_expected
    Easref(Qident(ident)) if ident.name[:] == name => expression_expected
    Esequence(first, second) =>
      match scan_expected(second, expression_expected) {
        Some(inferred) => return Some(inferred)
        None => scan(first)
      }
    Eand(first, second) | Eor(first, second) =>
      match scan(first) {
        Some(inferred) => return Some(inferred)
        None => scan(second)
      }
    Einfix(first, operator, second) | Einnfix(first, operator, second) => {
      match
        self.direct_local_application_expected(
          pure_space,
          program_space,
          locals,
          name,
          [operator.name],
          [first, second],
          Some(source_span(expression.span)),
          result_expected=expression_expected,
        ) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      match
        self.nested_local_application_expected(
          pure_space,
          program_space,
          locals,
          name,
          [operator.name],
          [first, second],
          Some(source_span(expression.span)),
          skeleton,
          expression_expected,
        ) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      match scan(first) {
        Some(inferred) => return Some(inferred)
        None => scan(second)
      }
    }
    Eif(condition, consequent, alternative) => {
      match scan(condition) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      for nested in [consequent, alternative] {
        match scan_expected(nested, expression_expected) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      None
    }
    Ewhile(condition, invariant, _, body) => {
      match scan(body) {
        Some(inferred) if !program_ity_has_inference_variables(inferred) =>
          return Some(inferred)
        Some(_) | None => ()
      }
      match scan(condition) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      for formula in invariant.terms {
        match
          self.formula_local_expected(
            pure_space,
            program_space,
            locals,
            name,
            formula,
            skeleton~,
          ) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      None
    }
    Efor(ident, first, _, last, invariant, body) => {
      for nested in [first, last] {
        match scan(nested) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      let nested = if ident.name[:] == name {
        locals.to_owned()
      } else {
        self.initializer_scan_loop_locals(
          pure_space, program_space, locals, ident, first, last,
        )
      }
      if ident.name[:] != name {
        match
          self.local_initializer_expected(
            pure_space,
            program_space,
            nested,
            name,
            body,
            skeleton~,
          ) {
          Some(inferred) if !program_ity_has_inference_variables(inferred) =>
            return Some(inferred)
          Some(_) | None => ()
        }
      }
      for formula in invariant.terms {
        match
          self.formula_local_expected(
            pure_space,
            program_space,
            nested,
            name,
            formula,
            skeleton~,
          ) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      None
    }
    Elet(ident, ghost, _, value, body) => {
      let value_expected = if ident.name[:] == name {
        None
      } else if expression_expected is Some(expected) &&
        !expected.free_type_variables().is_empty() {
        self.local_initializer_expected(
          pure_space,
          program_space,
          locals,
          ident.name,
          body,
          expression_expected~,
        )
      } else {
        None
      }
      match scan_expected(value, value_expected) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      if ident.name[:] == name {
        let downstream = self.local_initializer_expected(
          pure_space,
          program_space,
          locals,
          name,
          body,
          skeleton~,
          expression_expected~,
        )
        match downstream {
          Some(expected) if !program_ity_has_inference_variables(expected) => {
            let hypothetical = self.make_program_local(
              None,
              value.span,
              expected,
              self.ghost_context || ghost,
            )
            let nested = locals.to_owned()
            nested.push((ident.name, hypothetical))
            let compatible = try {
              ignore(
                self.type_program_expression_expected(
                  pure_space,
                  program_space,
                  nested,
                  value,
                  Some(expected),
                ),
              )
              true
            } catch {
              _ => false
            }
            if compatible {
              Some(expected)
            } else {
              None
            }
          }
          Some(_) | None => None
        }
      } else {
        self.local_initializer_expected(
          pure_space,
          program_space,
          self.initializer_scan_locals(
            pure_space, program_space, locals, ident, ghost, value,
          ),
          name,
          body,
          skeleton~,
          expression_expected~,
        )
      }
    }
    Erec(_, body) => scan_expected(body, expression_expected)
    Eidapp(path, arguments) => {
      match
        self.direct_local_application_expected(
          pure_space,
          program_space,
          locals,
          name,
          qualid_segments(path),
          arguments,
          Some(source_span(expression.span)),
          result_expected=expression_expected,
        ) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      match
        self.nested_local_application_expected(
          pure_space,
          program_space,
          locals,
          name,
          qualid_segments(path),
          arguments,
          Some(source_span(expression.span)),
          skeleton,
          expression_expected,
        ) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      for argument in arguments {
        match scan(argument) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      None
    }
    Eapply(_, _) => {
      let reversed : Array[@parser.Expr] = []
      let head = collect_program_application(expression, reversed)
      let mut arguments = reversed.rev()
      let path = match head.desc {
        Eident(path) => Some(qualid_segments(path))
        Eidapp(path, initial) => {
          let all = initial.copy()
          all.push_iter(arguments.iter())
          arguments = all
          Some(qualid_segments(path))
        }
        Eref => Some([b"ref"])
        _ => None
      }
      if path is Some(path) {
        match
          self.direct_local_application_expected(
            pure_space,
            program_space,
            locals,
            name,
            path,
            arguments,
            Some(source_span(expression.span)),
            result_expected=expression_expected,
          ) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
        match
          self.nested_local_application_expected(
            pure_space,
            program_space,
            locals,
            name,
            path,
            arguments,
            Some(source_span(expression.span)),
            skeleton,
            expression_expected,
          ) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      for argument in arguments {
        match scan(argument) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      None
    }
    Ematch(scrutinee, regular, exceptional) => {
      match scan(scrutinee) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      for branch in regular {
        let bound : Array[Bytes] = []
        program_pattern_bound_names(branch.pattern, bound)
        if !bound.any(bound_name => bound_name[:] == name) {
          match scan_expected(branch.body, expression_expected) {
            Some(inferred) => return Some(inferred)
            None => ()
          }
        }
      }
      for branch in exceptional {
        let bound : Array[Bytes] = []
        if branch.pattern is Some(pattern) {
          program_pattern_bound_names(pattern, bound)
        }
        if !bound.any(bound_name => bound_name[:] == name) {
          match scan_expected(branch.body, expression_expected) {
            Some(inferred) => return Some(inferred)
            None => ()
          }
        }
      }
      None
    }
    Eassign(assignments) => {
      for assignment in assignments {
        match
          self.assignment_local_value_expected(
            pure_space, program_space, locals, name, assignment,
          ) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
        for nested in [assignment.target, assignment.value] {
          match scan(nested) {
            Some(inferred) => return Some(inferred)
            None => ()
          }
        }
      }
      None
    }
    Etuple(items) => {
      for item in items {
        match scan(item) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      None
    }
    Erecord(fields) => {
      let inferred = try {
        let (constructor_routine, projections, values) = self.program_record_layout(
          program_space,
          fields,
          Some(source_span(expression.span)),
        )
        let cty = constructor_routine.view().cty.view()
        let mut result : @mlw.Ity? = None
        for index, projection in projections {
          if projection.view().field is Some(field) &&
            values.get(field) is Some(value) &&
            program_expression_returns_name(value, name) {
            let candidate = match
              try_instantiate_program_type(
                cty.freeze,
                cty.arguments[index].view().ity,
                Some(source_span(value.span)),
              ) {
              Some(candidate) => candidate
              None =>
                cty.freeze.instantiate_inference_expected(
                  self.context,
                  cty.arguments[index].view().ity,
                  Some(source_span(value.span)),
                ).1
            }
            if !program_ity_has_inference_variables(candidate) {
              result = Some(candidate)
              break
            }
          }
        }
        result
      } catch {
        _ => None
      }
      if inferred is Some(inferred) {
        return Some(inferred)
      }
      for field in fields {
        match scan(field.1) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      None
    }
    Eupdate(source, fields) => {
      match scan(source) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      for field in fields {
        match scan(field.1) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      None
    }
    Escope(scope, body) => {
      let scope_span = Some(qualid_span(scope))
      self.local_initializer_expected(
        pure_space.open_scope(qualid_segments(scope), scope_span),
        program_space.open_scope(qualid_segments(scope), scope_span),
        locals,
        name,
        body,
        skeleton~,
        expression_expected~,
      )
    }
    Efun([], _, _, _, _, body) => scan_expected(body, expression_expected)
    Eraise(path, Some(payload)) if qualid_last(path).name == b"'Return" => {
      let payload_expected = Some(
        program_space
        .find_exception(qualid_segments(path), Some(qualid_span(path)))
        .view().ity,
      ) catch {
        _ => expression_expected
      }
      scan_expected(payload, payload_expected)
    }
    Eraise(_, Some(payload)) => scan(payload)
    Elabel(_, body)
    | Eexn(_, _, _, body)
    | Eoptexn(_, _, body)
    | Eghost(body)
    | Eattr(_, body)
    | Ecast(body, _) => scan_expected(body, expression_expected)
    _ => None
  }
}

///|
fn ProgramTyping::reference_initializer_content_expected(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  name : BytesView,
  expression : @parser.Expr,
) -> @mlw.Ity? raise {
  match expression.desc {
    Einfix(left, operator, right) | Einnfix(left, operator, right) => {
      match
        self.reference_read_application_expected(
          pure_space,
          program_space,
          locals,
          name,
          [operator.name],
          [left, right],
          Some(source_span(expression.span)),
        ) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      let reference_assignment = operator.name == b"infix :="
      if !reference_assignment &&
        program_expression_is_reference_read(left, name) &&
        !program_expression_is_untyped_constant(right) {
        let inferred = Some(
          self
          .type_program_expression(pure_space, program_space, locals, right)
          .ity(),
        ) catch {
          _ => None
        }
        if inferred is Some(inferred) {
          return Some(inferred)
        }
      }
      if !reference_assignment &&
        program_expression_is_reference_read(right, name) &&
        !program_expression_is_untyped_constant(left) {
        let inferred = Some(
          self
          .type_program_expression(pure_space, program_space, locals, left)
          .ity(),
        ) catch {
          _ => None
        }
        if inferred is Some(inferred) {
          return Some(inferred)
        }
      }
      match
        self.reference_initializer_content_expected(
          pure_space, program_space, locals, name, left,
        ) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      self.reference_initializer_content_expected(
        pure_space, program_space, locals, name, right,
      )
    }
    Esequence(first, second) => {
      let later = self.reference_initializer_content_expected(
        pure_space, program_space, locals, name, second,
      )
      if later is Some(inferred) && !program_ity_is_default_numeric(inferred) {
        return later
      }
      let earlier = self.reference_initializer_content_expected(
        pure_space, program_space, locals, name, first,
      )
      match earlier {
        Some(inferred) if !program_ity_is_default_numeric(inferred) =>
          Some(inferred)
        Some(inferred) =>
          match later {
            Some(later) => Some(later)
            None => Some(inferred)
          }
        None => later
      }
    }
    Eand(first, second) | Eor(first, second) => {
      match
        self.reference_initializer_content_expected(
          pure_space, program_space, locals, name, first,
        ) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      self.reference_initializer_content_expected(
        pure_space, program_space, locals, name, second,
      )
    }
    Ewhile(condition, invariant, _, body) => {
      match
        self.reference_initializer_content_expected(
          pure_space, program_space, locals, name, body,
        ) {
        Some(inferred) if !program_ity_has_inference_variables(inferred) =>
          return Some(inferred)
        Some(_) | None => ()
      }
      match
        self.reference_initializer_content_expected(
          pure_space, program_space, locals, name, condition,
        ) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      for formula in invariant.terms {
        match
          self.formula_reference_content_expected(
            pure_space, program_space, locals, name, formula,
          ) {
          Some(inferred) if !program_ity_is_default_numeric(inferred) =>
            return Some(inferred)
          Some(_) => ()
          None => ()
        }
      }
      None
    }
    Efor(ident, first, _, last, invariant, body) => {
      for nested in [first, last] {
        match
          self.reference_initializer_content_expected(
            pure_space, program_space, locals, name, nested,
          ) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      let nested = if ident.name[:] == name {
        locals.to_owned()
      } else {
        self.initializer_scan_loop_locals(
          pure_space, program_space, locals, ident, first, last,
        )
      }
      if ident.name[:] != name {
        match
          self.reference_initializer_content_expected(
            pure_space, program_space, nested, name, body,
          ) {
          Some(inferred) if !program_ity_has_inference_variables(inferred) =>
            return Some(inferred)
          Some(_) | None => ()
        }
      }
      for formula in invariant.terms {
        match
          self.formula_reference_content_expected(
            pure_space, program_space, nested, name, formula,
          ) {
          Some(inferred) if !program_ity_is_default_numeric(inferred) =>
            return Some(inferred)
          Some(_) => ()
          None => ()
        }
      }
      None
    }
    Eif(condition, consequent, alternative) => {
      let mut fallback : @mlw.Ity? = None
      for nested in [consequent, alternative, condition] {
        match
          self.reference_initializer_content_expected(
            pure_space, program_space, locals, name, nested,
          ) {
          Some(inferred) if !program_ity_is_default_numeric(inferred) =>
            return Some(inferred)
          Some(inferred) => if fallback is None { fallback = Some(inferred) }
          None => ()
        }
      }
      fallback
    }
    Elet(ident, ghost, _, value, body) => {
      match
        self.reference_initializer_content_expected(
          pure_space, program_space, locals, name, value,
        ) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      if ident.name[:] == name {
        None
      } else {
        self.reference_initializer_content_expected(
          pure_space,
          program_space,
          self.initializer_scan_locals(
            pure_space, program_space, locals, ident, ghost, value,
          ),
          name,
          body,
        )
      }
    }
    Eidapp(path, arguments) => {
      match
        self.reference_read_application_expected(
          pure_space,
          program_space,
          locals,
          name,
          qualid_segments(path),
          arguments,
          Some(source_span(expression.span)),
        ) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      for argument in arguments {
        match
          self.reference_initializer_content_expected(
            pure_space, program_space, locals, name, argument,
          ) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      None
    }
    Eapply(_, _) => {
      let reversed : Array[@parser.Expr] = []
      let head = collect_program_application(expression, reversed)
      let mut arguments = reversed.rev()
      let path = match head.desc {
        Eident(path) => Some(qualid_segments(path))
        Eidapp(path, initial) => {
          let all = initial.copy()
          all.push_iter(arguments.iter())
          arguments = all
          Some(qualid_segments(path))
        }
        Eref => Some([b"ref"])
        _ => None
      }
      if path is Some(path) {
        match
          self.reference_read_application_expected(
            pure_space,
            program_space,
            locals,
            name,
            path,
            arguments,
            Some(source_span(expression.span)),
          ) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      for argument in arguments {
        match
          self.reference_initializer_content_expected(
            pure_space, program_space, locals, name, argument,
          ) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      None
    }
    Eassign(assignments) => {
      for assignment in assignments {
        if assignment.field is None &&
          program_expression_returns_name(assignment.target, name) {
          match
            self.partially_inferred_program_expression_type(
              pure_space,
              program_space,
              locals,
              assignment.value,
            ) {
            Some(inferred) => return Some(inferred)
            None => ()
          }
          match
            self.reference_initializer_content_expected(
              pure_space,
              program_space,
              locals,
              name,
              assignment.value,
            ) {
            Some(inferred) => return Some(inferred)
            None => ()
          }
        }
        for nested in [assignment.target, assignment.value] {
          match
            self.reference_initializer_content_expected(
              pure_space, program_space, locals, name, nested,
            ) {
            Some(inferred) => return Some(inferred)
            None => ()
          }
        }
      }
      None
    }
    Erecord(_) | Eupdate(_, _) =>
      self.local_initializer_expected(
        pure_space, program_space, locals, name, expression,
      )
    Ematch(scrutinee, regular, exceptional) => {
      match
        self.reference_initializer_content_expected(
          pure_space, program_space, locals, name, scrutinee,
        ) {
        Some(inferred) => return Some(inferred)
        None => ()
      }
      let scrutinee_ity = Some(
        self
        .type_program_expression(pure_space, program_space, locals, scrutinee)
        .ity(),
      ) catch {
        _ => None
      }
      for branch in regular {
        let nested = match scrutinee_ity {
          Some(ity) =>
            try {
              let pattern = @mlw.ProgramPattern::new(
                self.context,
                self.program_prepattern(
                  pure_space,
                  program_space,
                  branch.pattern,
                ),
                ity,
                @mlw.Visible,
                Some(source_span(branch.pattern.span)),
              )
              self.extend_pattern_locals(locals, pattern, branch.pattern.span)
            } catch {
              _ => locals.to_owned()
            }
          None => {
            let mut nested = locals.to_owned()
            match (scrutinee.desc, branch.pattern.desc) {
              (Etuple(items), Ptuple(patterns)) if items.length() ==
                patterns.length() =>
                for index, item in items {
                  let component_ity = Some(
                    self
                    .type_program_expression(
                      pure_space, program_space, nested, item,
                    )
                    .ity(),
                  ) catch {
                    _ => None
                  }
                  if component_ity is Some(ity) {
                    let extended = try {
                      let pattern = @mlw.ProgramPattern::new(
                        self.context,
                        self.program_prepattern(
                          pure_space,
                          program_space,
                          patterns[index],
                        ),
                        ity,
                        @mlw.Visible,
                        Some(source_span(patterns[index].span)),
                      )
                      Some(
                        self.extend_pattern_locals(
                          nested,
                          pattern,
                          patterns[index].span,
                        ),
                      )
                    } catch {
                      _ => None
                    }
                    if extended is Some(extended) {
                      nested = extended
                    }
                  }
                }
              _ => ()
            }
            nested
          }
        }
        match
          self.reference_initializer_content_expected(
            pure_space,
            program_space,
            nested,
            name,
            branch.body,
          ) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      for branch in exceptional {
        match
          self.reference_initializer_content_expected(
            pure_space,
            program_space,
            locals,
            name,
            branch.body,
          ) {
          Some(inferred) => return Some(inferred)
          None => ()
        }
      }
      None
    }
    Escope(scope, body) => {
      let scope_span = Some(qualid_span(scope))
      self.reference_initializer_content_expected(
        pure_space.open_scope(qualid_segments(scope), scope_span),
        program_space.open_scope(qualid_segments(scope), scope_span),
        locals,
        name,
        body,
      )
    }
    Efun([], _, _, _, _, body) =>
      self.reference_initializer_content_expected(
        pure_space, program_space, locals, name, body,
      )
    Eraise(_, Some(payload)) =>
      self.reference_initializer_content_expected(
        pure_space, program_space, locals, name, payload,
      )
    Elabel(_, body)
    | Eexn(_, _, _, body)
    | Eoptexn(_, _, body)
    | Eghost(body)
    | Eattr(_, body)
    | Ecast(body, _) =>
      self.reference_initializer_content_expected(
        pure_space, program_space, locals, name, body,
      )
    _ => None
  }
}

///|
fn program_expression_raises_name(
  expression : @parser.Expr,
  name : BytesView,
) -> Bool {
  let recurse = fn(child) { program_expression_raises_name(child, name) }
  match expression.desc {
    Eraise(path, payload) =>
      qualid_last(path).name[:] == name ||
      (payload is Some(payload) && recurse(payload))
    Elet(_, _, _, value, body) => recurse(value) || recurse(body)
    Erec(definitions, body) =>
      definitions.any(definition => recurse(definition.body)) || recurse(body)
    Efun(_, _, _, _, _, body) => recurse(body)
    Eany(_, _, _, _, _, _) => false
    Eapply(function_, argument)
    | Einfix(function_, _, argument)
    | Einnfix(function_, _, argument)
    | Esequence(function_, argument)
    | Eand(function_, argument)
    | Eor(function_, argument) => recurse(function_) || recurse(argument)
    Eidapp(_, arguments) | Etuple(arguments) => arguments.any(recurse)
    Erecord(fields) => fields.any(field => recurse(field.1))
    Eupdate(source, fields) =>
      recurse(source) || fields.any(field => recurse(field.1))
    Eassign(assignments) =>
      assignments.any(assignment => {
        recurse(assignment.target) || recurse(assignment.value)
      })
    Eif(condition, consequent, alternative) =>
      recurse(condition) || recurse(consequent) || recurse(alternative)
    Ewhile(condition, _, _, body) => recurse(condition) || recurse(body)
    Efor(_, first, _, last, _, body) =>
      recurse(first) || recurse(last) || recurse(body)
    Ematch(scrutinee, regular, exceptional) =>
      recurse(scrutinee) ||
      regular.any(branch => recurse(branch.body)) ||
      exceptional.any(branch => recurse(branch.body))
    Eexn(ident, _, _, _) if ident.name[:] == name => false
    Eexn(_, _, _, body) => recurse(body)
    Eoptexn(ident, _, _) if ident.name[:] == name => false
    Eoptexn(_, _, body) => recurse(body)
    Eghost(body)
    | Elabel(_, body)
    | Ecast(body, _)
    | Escope(_, body)
    | Eattr(_, body) => recurse(body)
    Enot(body) => recurse(body)
    Eref
    | Etrue
    | Efalse
    | Econst(_)
    | Eident(_)
    | Easref(_)
    | Epure(_)
    | Eidpur(_)
    | Eabsurd
    | Eassert(_, _) => false
  }
}

///|
fn ProgramTyping::inferred_optional_exception_payload(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  expression : @parser.Expr,
  name : BytesView,
) -> @mlw.Ity? raise {
  let recurse = fn(child) raise {
    self.inferred_optional_exception_payload(
      pure_space, program_space, locals, child, name,
    )
  }
  match expression.desc {
    Eraise(path, payload) if qualid_last(path).name[:] == name =>
      match payload {
        None =>
          Some(
            self.unit_ity(
              pure_space,
              program_space,
              Some(source_span(expression.span)),
            ),
          )
        Some(payload) =>
          match
            self.partially_inferred_program_expression_type(
              pure_space, program_space, locals, payload,
            ) {
            Some(candidate) if !program_ity_has_inference_variables(candidate) =>
              Some(candidate)
            Some(_) | None => None
          }
      }
    Eraise(_, Some(payload)) => recurse(payload)
    Elet(_, _, _, value, body) =>
      match recurse(value) {
        Some(candidate) => Some(candidate)
        None => recurse(body)
      }
    Erec(definitions, body) => {
      for definition in definitions {
        match recurse(definition.body) {
          Some(candidate) => return Some(candidate)
          None => ()
        }
      }
      recurse(body)
    }
    Efun(_, _, _, _, _, body) => recurse(body)
    Eapply(function_, argument)
    | Einfix(function_, _, argument)
    | Einnfix(function_, _, argument)
    | Esequence(function_, argument)
    | Eand(function_, argument)
    | Eor(function_, argument) =>
      match recurse(function_) {
        Some(candidate) => Some(candidate)
        None => recurse(argument)
      }
    Eidapp(_, arguments) | Etuple(arguments) => {
      for argument in arguments {
        match recurse(argument) {
          Some(candidate) => return Some(candidate)
          None => ()
        }
      }
      None
    }
    Erecord(fields) => {
      for field in fields {
        match recurse(field.1) {
          Some(candidate) => return Some(candidate)
          None => ()
        }
      }
      None
    }
    Eupdate(source, fields) =>
      match recurse(source) {
        Some(candidate) => Some(candidate)
        None => {
          for field in fields {
            match recurse(field.1) {
              Some(candidate) => return Some(candidate)
              None => ()
            }
          }
          None
        }
      }
    Eassign(assignments) => {
      for assignment in assignments {
        match recurse(assignment.target) {
          Some(candidate) => return Some(candidate)
          None => ()
        }
        match recurse(assignment.value) {
          Some(candidate) => return Some(candidate)
          None => ()
        }
      }
      None
    }
    Eif(condition, consequent, alternative) =>
      match recurse(condition) {
        Some(candidate) => Some(candidate)
        None =>
          match recurse(consequent) {
            Some(candidate) => Some(candidate)
            None => recurse(alternative)
          }
      }
    Ewhile(condition, _, _, body) =>
      match recurse(condition) {
        Some(candidate) => Some(candidate)
        None => recurse(body)
      }
    Efor(_, first, _, last, _, body) =>
      match recurse(first) {
        Some(candidate) => Some(candidate)
        None =>
          match recurse(last) {
            Some(candidate) => Some(candidate)
            None => recurse(body)
          }
      }
    Ematch(scrutinee, regular, exceptional) =>
      match recurse(scrutinee) {
        Some(candidate) => Some(candidate)
        None => {
          for branch in regular {
            match recurse(branch.body) {
              Some(candidate) => return Some(candidate)
              None => ()
            }
          }
          for branch in exceptional {
            match recurse(branch.body) {
              Some(candidate) => return Some(candidate)
              None => ()
            }
          }
          None
        }
      }
    Eexn(ident, _, _, _) | Eoptexn(ident, _, _) if ident.name[:] == name => None
    Eexn(_, _, _, body)
    | Eoptexn(_, _, body)
    | Eghost(body)
    | Elabel(_, body)
    | Ecast(body, _)
    | Escope(_, body)
    | Eattr(_, body)
    | Enot(body) => recurse(body)
    Eref
    | Etrue
    | Efalse
    | Econst(_)
    | Eident(_)
    | Easref(_)
    | Eany(_, _, _, _, _, _)
    | Eabsurd
    | Epure(_)
    | Eidpur(_)
    | Eraise(_, None)
    | Eassert(_, _) => None
  }
}

///|
fn program_ity_head_symbol(ity : @mlw.Ity) -> @mlw.ProgramTypeSymbol? {
  match ity.view() {
    ItyVar(_) => None
    ItyApp(symbol, _, _) => Some(symbol)
    ItyReg(region) => Some(region.view().symbol)
  }
}

///|
fn program_ity_skeleton_compatible(
  expected : @mlw.Ity,
  actual : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> Bool raise {
  if expected == actual {
    return true
  }
  try {
    ignore(@mlw.ItySubstitution::empty().match_ity(expected, actual, span))
    true
  } catch {
    @mlw.MlwError(diagnostic) =>
      if diagnostic.kind == @mlw.ProgramTypeMismatch {
        false
      } else {
        raise @mlw.MlwError(diagnostic)
      }
  }
}

///|
fn validate_program_ity_skeleton(
  expected : @mlw.Ity,
  actual : @mlw.Ity,
  span : @identity.SourceSpan?,
  message : String,
) -> Unit raise {
  if !program_ity_skeleton_compatible(expected, actual, span) {
    let expected_shape = semantic_ty_diagnostic_bytes(expected.to_ty(span)).to_string()
    let actual_shape = semantic_ty_diagnostic_bytes(actual.to_ty(span)).to_string()
    @logic.fail_type(
      TypeMismatch,
      span,
      "\{message}: \{expected_shape} vs \{actual_shape}",
    )
  }
}

///|
fn ProgramTyping::program_record_expression(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  fields : ArrayView[(@parser.QualId, @parser.Expr)],
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  let (constructor_routine, projections, values) = self.program_record_layout(
    program_space, fields, span,
  )
  let arguments : Array[@parser.Expr] = []
  for projection in projections {
    guard projection.view().field is Some(field) else {
      @logic.fail_type(
        BadRecordField,
        span,
        "program record projection has no field",
      )
    }
    match values.get(field) {
      Some(value) => arguments.push(value)
      None =>
        @logic.fail_type(
          RecordFieldMissing,
          span,
          "record construction omits a field",
        )
    }
  }
  self.resolved_routine_application(
    pure_space, program_space, locals, constructor_routine, arguments, decoration,
    expected,
  )
}

///|
fn ProgramTyping::program_record_update(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  source : @parser.Expr,
  fields : ArrayView[(@parser.QualId, @parser.Expr)],
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  let construction_expected = expected
  let (constructor_routine, projections, values) = self.program_record_layout(
    program_space, fields, span,
  )
  let source_expression = self.type_program_expression(
    pure_space, program_space, locals, source,
  )
  let constructor_head = program_ity_head_symbol(
    constructor_routine.view().cty.view().result,
  )
  if program_ity_head_symbol(source_expression.ity()) != constructor_head {
    @logic.fail_type(
      BadRecordType,
      Some(source_span(source.span)),
      "record update source has a different record type",
    )
  }
  let source_proxy = self.proxy_argument(
    source_expression,
    source_span(source.span),
  )
  let source_reference = @mlw.Expr::variable(
    source_proxy.0,
    program_origin(decoration),
    decoration.attributes,
  )
  let constructor_cty = constructor_routine.view().cty.view()
  let mut substitution = constructor_cty.freeze
  if construction_expected is Some(expected) {
    substitution = substitution.match_ity(
      constructor_cty.result,
      expected,
      span,
    )
  }
  let arguments : Array[@mlw.Expr] = []
  let argument_spans : Array[@identity.SourceSpan] = []
  for index, projection in projections {
    guard projection.view().field is Some(field) else {
      @logic.fail_type(
        BadRecordField,
        span,
        "program record projection has no field",
      )
    }
    let argument_expected = try_instantiate_program_type(
      substitution,
      constructor_cty.arguments[index].view().ity,
      span,
    )
    let (argument, argument_span) = match values.get(field) {
      Some(value) =>
        (
          self.type_program_expression_expected(
            pure_space, program_space, locals, value, argument_expected,
          ),
          source_span(value.span),
        )
      None =>
        (
          self.typed_routine_application(
            projection,
            [source_reference],
            [source_span(source.span)],
            decoration,
            argument_expected,
          ),
          source_span(source.span),
        )
    }
    substitution = substitution.match_ity(
      constructor_cty.arguments[index].view().ity,
      argument.ity(),
      span,
    )
    arguments.push(argument)
    argument_spans.push(argument_span)
  }
  let rebuilt = self.typed_routine_application(
    constructor_routine, arguments, argument_spans, decoration, construction_expected,
  )
  match source_proxy.1 {
    Some(value) =>
      @mlw.Expr::let_in(
        source_proxy.0,
        value,
        rebuilt,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    None => rebuilt
  }
}

///|
fn ProgramTyping::program_assignment(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  sources : ArrayView[@parser.Assignment],
  decoration : ProgramDecoration,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  let assignments : Array[@mlw.Assignment] = []
  let proxies : Array[(@mlw.PVariable, @mlw.Expr?)] = []
  for source in sources {
    let (field, field_span) = match source.field {
      Some(field_path) =>
        (
          program_space.find_routine(
            qualid_segments(field_path),
            Some(qualid_span(field_path)),
          ),
          Some(qualid_span(field_path)),
        )
      None =>
        (
          program_space.find_routine(
            [b"contents"],
            Some(source_span(source.target.span)),
          ),
          Some(source_span(source.target.span)),
        )
    }
    guard field.view().field is Some(field_variable) &&
      field.view().logic is RLls(_) else {
      @logic.fail_type(
        BadRecordField,
        field_span,
        "assignment field is not a mutable record projection",
      )
    }
    let target = self.type_program_expression(
      pure_space,
      program_space,
      locals,
      source.target,
    )
    let value_type = self.routine_result_for_argument_types(
      field,
      [target.ity()],
      None,
      field_span,
    )
    let value = self.type_program_expression_expected(
      pure_space,
      program_space,
      locals,
      source.value,
      if !value_type.is_pure() &&
        !program_expression_needs_expected(source.value) {
        None
      } else {
        Some(value_type)
      },
    )
    // Why3 proxies both sides of an assignment as ghost whenever the target,
    // value, or mutable model field is ghost. This is essential for concrete
    // containers such as `ArrayInt63`, whose runtime update is represented by
    // a mutable ghost `elts` field: the ghost proxy isolates that model write
    // from the non-ghost record through which the container was reached.
    let proxy_ghost = target.effect().view().ghost ||
      field_variable.view().ghost ||
      value.effect().view().ghost
    let target_proxy = self.proxy_argument(
      target,
      source_span(source.target.span),
      ghost=proxy_ghost,
    )
    let value_proxy = self.proxy_argument(
      value,
      source_span(source.value.span),
      ghost=proxy_ghost,
    )
    proxies.push(target_proxy)
    proxies.push(value_proxy)
    assignments.push(
      @mlw.Assignment::new(target_proxy.0, field, value_proxy.0, field_span),
    )
  }
  let assignment = @mlw.Expr::assignment(
    assignments,
    self.unit_ity(pure_space, program_space, span),
    program_origin(decoration),
    decoration.attributes,
    span,
  )
  self.wrap_argument_proxies(proxies, assignment, decoration)
}

///|
fn ProgramTyping::program_labeled_expression(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  label : @parser.Ident,
  body : @parser.Expr,
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let saved_values = self.at_values
  let saved_labels = self.at_labels
  let saved_program_variables = self.at_program_variables
  self.at_values = saved_values.copy()
  self.at_labels = saved_labels.copy()
  self.at_program_variables = saved_program_variables.copy()
  self.at_labels.push(label.name)
  let snapshots : Array[(@mlw.PVariable, @mlw.PVariable)] = []
  for entry in locals {
    let original = entry.1.variable
    if !original.view().ity.is_pure() {
      let snapshot = @mlw.PVariable::trusted_new(
        self.context,
        @theory.SemanticName::new(
          original.view().name.view().name,
          [b"mlw:label_snapshot"],
          Some(source_span(label.span)),
        ),
        original.view().ity.purify(),
        true,
        Some(source_span(label.span)),
      )
      self.register_snapshot_placeholder(snapshot, original)
      self.at_values.push({
        local_id: entry.1.delayed.id,
        label: label.name,
        value: snapshot.view().pure_symbol,
      })
      self.at_program_variables.push(snapshot)
      snapshots.push((snapshot, original))
    }
  }
  let typed = self.type_program_expression_expected(
    pure_space, program_space, locals, body, expected,
  ) catch {
    error => {
      self.at_values = saved_values
      self.at_labels = saved_labels
      self.at_program_variables = saved_program_variables
      raise error
    }
  }
  self.at_values = saved_values
  self.at_labels = saved_labels
  self.at_program_variables = saved_program_variables
  let mut result = typed
  for index = snapshots.length() - 1; index >= 0; index = index - 1 {
    let (placeholder, original) = snapshots[index]
    let snapshot = self.materialized_snapshot(placeholder)
    if result.effect().view().reads.any(read => read == snapshot) {
      let snapshot_value = @mlw.Expr::pure_term(
        @logic.Term::variable(original.view().pure_symbol),
        snapshot.view().ity,
        [original],
        @identity.Origin::user(b"", None, []),
        [],
        None,
      )
      result = @mlw.Expr::let_in(
        snapshot,
        snapshot_value,
        result,
        program_origin(decoration),
        decoration.attributes,
        Some(decoration.location),
      )
    }
  }
  result
}

///|
fn ProgramTyping::type_program_expression(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  expression : @parser.Expr,
) -> @mlw.Expr raise {
  self.type_program_expression_expected(
    pure_space,
    program_space,
    locals,
    expression,
    None,
  )
}

///|
fn ProgramTyping::type_program_expression_expected(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  expression : @parser.Expr,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  self.type_decorated_program_expression(
    pure_space,
    program_space,
    locals,
    expression,
    default_program_decoration(expression),
    expected,
  )
}

///|
fn ProgramTyping::type_decorated_program_expression(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, ProgramLocal)],
  expression : @parser.Expr,
  decoration : ProgramDecoration,
  expected : @mlw.Ity?,
) -> @mlw.Expr raise {
  let span = Some(decoration.location)
  let typed = match expression.desc {
    Etrue => {
      let boolean = self.boolean_ity(pure_space, program_space, span)
      self.zero_argument_pure_expression(
        pure_space, program_space, b"True", boolean, decoration,
      )
    }
    Efalse => {
      let boolean = self.boolean_ity(pure_space, program_space, span)
      self.zero_argument_pure_expression(
        pure_space, program_space, b"False", boolean, decoration,
      )
    }
    Econst(constant) =>
      self.constant_expression(
        pure_space, program_space, constant, decoration, expected,
      )
    Eident(Qident(ident)) =>
      match find_program_local(locals, ident.name) {
        Some(binding) => {
          let variable = @mlw.Expr::variable(
            binding.variable,
            program_origin(decoration),
            decoration.attributes,
          )
          if binding.reference &&
            !(expected is Some(expected) && program_ity_is_reference(expected)) {
            self.typed_routine_application(
              program_space.find_routine([b"contents"], span),
              [variable],
              [decoration.location],
              decoration,
              expected,
            )
          } else {
            variable
          }
        }
        None =>
          self.resolved_application(
            pure_space,
            program_space,
            locals,
            [ident.name],
            [],
            decoration,
            expected,
          )
      }
    Eident(qualid) =>
      self.resolved_application(
        pure_space,
        program_space,
        locals,
        qualid_segments(qualid),
        [],
        decoration,
        expected,
      )
    Eidapp(Qident(ident), arguments) if find_program_local(locals, ident.name)
      is Some(_) =>
      self.higher_order_program_application(
        pure_space,
        program_space,
        locals,
        @parser.Expr::{ desc: Eident(Qident(ident)), span: ident.span },
        arguments,
        decoration,
        expected,
      )
    Eidapp(qualid, arguments) =>
      self.resolved_application(
        pure_space,
        program_space,
        locals,
        qualid_segments(qualid),
        arguments,
        decoration,
        expected,
      )
    Eapply(_, _) => {
      let reversed : Array[@parser.Expr] = []
      let head = collect_program_application(expression, reversed)
      let arguments = reversed.rev()
      match head.desc {
        Eident(Qident(ident)) if find_program_local(locals, ident.name)
          is Some(_) =>
          self.higher_order_program_application(
            pure_space, program_space, locals, head, arguments, decoration, expected,
          )
        Eident(qualid) =>
          self.resolved_application(
            pure_space,
            program_space,
            locals,
            qualid_segments(qualid),
            arguments,
            decoration,
            expected,
          )
        Eidapp(qualid, initial) => {
          let all = initial.copy()
          for argument in arguments {
            all.push(argument)
          }
          self.resolved_application(
            pure_space,
            program_space,
            locals,
            qualid_segments(qualid),
            all,
            decoration,
            expected,
          )
        }
        Eref =>
          self.resolved_application(
            pure_space,
            program_space,
            locals,
            [b"ref"],
            arguments,
            decoration,
            expected,
          )
        _ =>
          self.higher_order_program_application(
            pure_space, program_space, locals, head, arguments, decoration, expected,
          )
      }
    }
    Einfix(left, operator, right) =>
      self.program_relation_chain(
        pure_space, program_space, locals, left, operator, right, decoration, expected,
      )
    Einnfix(left, operator, right) =>
      self.resolved_relation_application(
        pure_space, program_space, locals, left, operator, right, decoration, expected,
      )
    Elet(ident, ghost, kind, value, body) => {
      let direct_alias = if kind == RKnone {
        direct_program_routine_alias(program_space, value)
      } else {
        None
      }
      let is_routine = match value.desc {
        Efun(binders, _, _, _, _, _) => !binders.is_empty() || kind != RKnone
        Eany(parameters, _, _, _, _, _) =>
          !parameters.is_empty() || kind != RKnone
        _ => false
      }
      if direct_alias is Some(source) {
        let (symbol, computation) = self.make_program_routine_alias(
          ident, source, ghost,
        )
        let nested_space = program_space.overlay(
          @mlw.ProgramNamespace::empty().add_routine(
            ident.name,
            symbol,
            Some(source_span(ident.span)),
          ),
        )
        let body = self.type_program_expression_expected(
          pure_space, nested_space, locals, body, expected,
        )
        @mlw.Expr::let_definition(
          @mlw.LetDefinition::symbol(
            symbol,
            computation,
            Some(source_span(ident.span)),
          ),
          body,
          program_origin(decoration),
          decoration.attributes,
          span,
        )
      } else if is_routine {
        let local_kind = match kind {
          RKfunc | RKpred => @parser.RKlocal
          _ => kind
        }
        let routine = self.type_routine_expression(
          pure_space,
          program_space,
          locals,
          ident,
          ghost,
          local_kind,
          value,
          None,
        )
        let nested_space = program_space.overlay(
          @mlw.ProgramNamespace::empty().add_routine(
            ident.name,
            routine.symbol,
            Some(source_span(ident.span)),
          ),
        )
        let body = self.type_program_expression_expected(
          pure_space, nested_space, locals, body, expected,
        )
        @mlw.Expr::let_definition(
          @mlw.LetDefinition::symbol(
            routine.symbol,
            routine.cexp,
            Some(source_span(ident.span)),
          ),
          body,
          program_origin(decoration),
          decoration.attributes,
          span,
        )
      } else {
        if kind != RKnone {
          fail_invalid_input(
            InvalidDeclaration,
            ProgramTyping,
            Some(source_span(ident.span)),
            "a routine kind qualifier requires a routine binding",
          )
        }
        let reference_initializer = program_reference_initializer(value)
        let reference_allocation = reference_initializer is Some(_)
        let reference_preliminary_content : @mlw.Ity? = match
          reference_initializer {
          Some(initializer) if program_expression_is_untyped_constant(
              initializer,
            ) => None
          Some(initializer) if program_expression_contains_untyped_constant(
              initializer,
            ) =>
            self.partially_inferred_program_expression_type(
              pure_space, program_space, locals, initializer,
            ) catch {
              _ => None
            }
          Some(initializer) =>
            Some(
              self
              .type_program_expression(
                pure_space, program_space, locals, initializer,
              )
              .ity(),
            ) catch {
              _ => None
            }
          None => None
        }
        let reference_preliminary_concrete = reference_preliminary_content
          is Some(content) &&
          content.is_closed() &&
          !program_ity_has_inference_variables(content)
        let reference_preliminary_expected : @mlw.Ity? = match
          reference_preliminary_content {
          Some(content) if content.is_pure() &&
            content.is_closed() &&
            !program_ity_has_inference_variables(content) =>
            Some(
              @mlw.Ity::instantiate(
                program_space.find_type([b"ref"], span),
                [content],
                [],
                span,
              ),
            )
          _ => None
        }
        let preliminary : @mlw.Expr? = if reference_allocation {
          None
        } else {
          Some(
            self.type_program_expression(
              pure_space, program_space, locals, value,
            ),
          ) catch {
            _ => None
          }
        }
        let returned_expected = if reference_allocation {
          None
        } else if program_expression_returns_name(body, ident.name) {
          expected
        } else {
          match expected {
            Some(expected) =>
              self.shadowed_local_return_expected(
                pure_space,
                program_space,
                locals,
                ident.name,
                body,
                expected,
              )
            None => None
          }
        }
        let returned_reference_content_expected = if reference_allocation &&
          program_expression_returns_implicit_read(body, ident.name) {
          expected
        } else {
          None
        }
        let initializer_needs_context = returned_expected is Some(_) ||
          program_expression_contains_untyped_constant(value) ||
          (match preliminary {
            Some(preliminary) =>
              program_ity_has_inference_variables(preliminary.ity())
            None => true
          })
        let contextual_expected = if reference_allocation {
          match reference_preliminary_expected {
            Some(expected) => Some(expected)
            None =>
              if reference_preliminary_concrete {
                None
              } else {
                let content = match returned_reference_content_expected {
                  Some(content) => Some(content)
                  None =>
                    self.reference_initializer_content_expected(
                      pure_space,
                      program_space,
                      locals,
                      ident.name,
                      body,
                    )
                }
                match content {
                  Some(content) =>
                    Some(
                      @mlw.Ity::instantiate(
                        program_space.find_type([b"ref"], span),
                        [content],
                        [],
                        span,
                      ),
                    )
                  None => None
                }
              }
          }
        } else if returned_expected is Some(_) {
          None
        } else if initializer_needs_context {
          self.local_initializer_expected(
            pure_space,
            program_space,
            locals,
            ident.name,
            body,
            skeleton=preliminary.map(value => value.ity()),
            expression_expected=expected,
          )
        } else {
          None
        }
        let value = match preliminary {
          Some(preliminary) if !initializer_needs_context => preliminary
          _ =>
            self.type_program_expression_expected(
              pure_space,
              program_space,
              locals,
              value,
              if reference_allocation {
                contextual_expected
              } else if returned_expected is Some(returned_expected) {
                Some(returned_expected)
              } else {
                contextual_expected
              },
            )
        }
        let binding_ghost = self.ghost_context ||
          ghost ||
          value.mask().is_ghost()
        let binding = self.make_program_local(
          Some(ident),
          ident.span,
          value.ity(),
          binding_ghost,
        )
        let nested = locals.to_owned()
        nested.push((ident.name, binding))
        let body = self.type_program_expression_expected(
          pure_space, program_space, nested, body, expected,
        )
        @mlw.Expr::let_in(
          binding.variable,
          value,
          body,
          program_origin(decoration),
          decoration.attributes,
          span,
        )
      }
    }
    Esequence(first, second) => {
      let unit = self.unit_ity(pure_space, program_space, span)
      let first = self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        first,
        Some(unit),
      )
      let binder = self.make_program_local(
        None,
        expression.span,
        first.ity(),
        self.ghost_context || first.mask().is_ghost(),
      )
      let second = self.type_program_expression_expected(
        pure_space, program_space, locals, second, expected,
      )
      @mlw.Expr::let_in(
        binder.variable,
        first,
        second,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Eif(condition, consequent, alternative) => {
      let boolean = self.boolean_ity(pure_space, program_space, span)
      let condition = self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        condition,
        Some(boolean),
      )
      let (consequent, alternative) = match expected {
        Some(expected) => {
          let consequent_needs_expected = program_expression_needs_expected(
            consequent,
          )
          let alternative_needs_expected = program_expression_needs_expected(
            alternative,
          )
          if consequent_needs_expected && !alternative_needs_expected {
            let inferred = self.type_program_expression(
              pure_space, program_space, locals, alternative,
            )
            if !program_ity_has_inference_variables(inferred.ity()) &&
              program_ity_skeleton_compatible(
                expected,
                inferred.ity(),
                Some(source_span(alternative.span)),
              ) {
              (
                self.type_program_expression_expected(
                  pure_space,
                  program_space,
                  locals,
                  consequent,
                  Some(inferred.ity()),
                ),
                inferred,
              )
            } else {
              (
                self.type_program_expression_expected(
                  pure_space,
                  program_space,
                  locals,
                  consequent,
                  Some(expected),
                ),
                self.type_program_expression_expected(
                  pure_space,
                  program_space,
                  locals,
                  alternative,
                  Some(expected),
                ),
              )
            }
          } else if alternative_needs_expected && !consequent_needs_expected {
            let inferred = self.type_program_expression(
              pure_space, program_space, locals, consequent,
            )
            if !program_ity_has_inference_variables(inferred.ity()) &&
              program_ity_skeleton_compatible(
                expected,
                inferred.ity(),
                Some(source_span(consequent.span)),
              ) {
              (
                inferred,
                self.type_program_expression_expected(
                  pure_space,
                  program_space,
                  locals,
                  alternative,
                  Some(inferred.ity()),
                ),
              )
            } else {
              (
                self.type_program_expression_expected(
                  pure_space,
                  program_space,
                  locals,
                  consequent,
                  Some(expected),
                ),
                self.type_program_expression_expected(
                  pure_space,
                  program_space,
                  locals,
                  alternative,
                  Some(expected),
                ),
              )
            }
          } else {
            (
              self.type_program_expression_expected(
                pure_space,
                program_space,
                locals,
                consequent,
                Some(expected),
              ),
              self.type_program_expression_expected(
                pure_space,
                program_space,
                locals,
                alternative,
                Some(expected),
              ),
            )
          }
        }
        None =>
          if program_expression_needs_expected(consequent) &&
            !program_expression_needs_expected(alternative) {
            let alternative = self.type_program_expression(
              pure_space, program_space, locals, alternative,
            )
            (
              self.type_program_expression_expected(
                pure_space,
                program_space,
                locals,
                consequent,
                Some(alternative.ity()),
              ),
              alternative,
            )
          } else {
            let consequent = self.type_program_expression(
              pure_space, program_space, locals, consequent,
            )
            (
              consequent,
              self.type_program_expression_expected(
                pure_space,
                program_space,
                locals,
                alternative,
                Some(consequent.ity()),
              ),
            )
          }
      }
      if condition.ity() != boolean {
        @logic.fail_type(
          TypeMismatch,
          span,
          "program conditional condition is not boolean",
        )
      }
      if consequent.ity() != alternative.ity() {
        let consequent_shape = semantic_ty_diagnostic_bytes(
          consequent.ity().to_ty(span),
        ).to_string()
        let alternative_shape = semantic_ty_diagnostic_bytes(
          alternative.ity().to_ty(span),
        ).to_string()
        @logic.fail_type(
          TypeMismatch,
          span,
          "program conditional branches have incompatible types: \{consequent_shape} vs \{alternative_shape}",
        )
      }
      @mlw.Expr::if_then_else(
        condition,
        consequent,
        alternative,
        boolean,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Eand(left, right) => {
      let boolean = self.boolean_ity(pure_space, program_space, span)
      let condition = self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        left,
        Some(boolean),
      )
      let consequent = self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        right,
        Some(boolean),
      )
      let alternative = self.zero_argument_pure_expression(
        pure_space,
        program_space,
        b"False",
        boolean,
        decoration,
        synthesized=true,
      )
      if condition.ity() != boolean || consequent.ity() != boolean {
        @logic.fail_type(TypeMismatch, span, "boolean conjunction expected")
      }
      @mlw.Expr::if_then_else(
        condition,
        consequent,
        alternative,
        boolean,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Eor(left, right) => {
      let boolean = self.boolean_ity(pure_space, program_space, span)
      let condition = self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        left,
        Some(boolean),
      )
      let alternative = self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        right,
        Some(boolean),
      )
      let consequent = self.zero_argument_pure_expression(
        pure_space,
        program_space,
        b"True",
        boolean,
        decoration,
        synthesized=true,
      )
      if condition.ity() != boolean || alternative.ity() != boolean {
        @logic.fail_type(TypeMismatch, span, "boolean disjunction expected")
      }
      @mlw.Expr::if_then_else(
        condition,
        consequent,
        alternative,
        boolean,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Enot(inner) => {
      let boolean = self.boolean_ity(pure_space, program_space, span)
      let condition = self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        inner,
        Some(boolean),
      )
      self.negate_boolean_expression(
        pure_space, program_space, condition, decoration,
      )
    }
    Eassert(kind, formula) => {
      let expanded = self.program_logic_mappings(program_space, expression.span)
      expanded.push_iter(locals.iter())
      let (logic_locals, logic_values) = program_logic_scope(expanded)
      let formula = self.pure.formula(
        pure_space,
        logic_locals,
        logic_values,
        formula,
        at_values=self.at_values,
        at_labels=self.at_labels,
        at_resolver=entry => self.materialize_at_value(entry),
      )
      let reads = program_formula_reads(
        expanded,
        formula,
        snapshots=self.materialized_snapshots(self.at_program_variables),
      )
      let unit = self.unit_ity(pure_space, program_space, span)
      match kind {
        Assert =>
          @mlw.Expr::assert_formula(
            formula,
            reads,
            unit,
            program_origin(decoration),
            decoration.attributes,
            span,
          )
        Assume =>
          @mlw.Expr::assume_formula(
            formula,
            reads,
            unit,
            program_origin(decoration),
            decoration.attributes,
            span,
          )
        Check =>
          @mlw.Expr::assertion(
            @mlw.Check,
            formula,
            reads,
            unit,
            program_origin(decoration),
            decoration.attributes,
            span,
          )
      }
    }
    Escope(qualid, inner) => {
      let scope_span = Some(qualid_span(qualid))
      self.type_decorated_program_expression(
        pure_space.open_scope(qualid_segments(qualid), scope_span),
        program_space.open_scope(qualid_segments(qualid), scope_span),
        locals,
        inner,
        decoration,
        expected,
      )
    }
    Ecast(inner, annotation) => {
      let annotated = self.program_ity(
        pure_space, program_space, annotation, span,
      )
      let inner = self.type_decorated_program_expression(
        pure_space,
        program_space,
        locals,
        inner,
        decoration,
        Some(annotated),
      )
      if inner.ity() != annotated {
        @logic.fail_type(TypeMismatch, span, "program cast has the wrong type")
      }
      inner
    }
    Eattr(attribute, inner) => {
      let nested = match attribute {
        Text(text) => {
          let attributes = decoration.attributes.copy()
          let checked = if text == b"vc:white_box" &&
            inner.desc is Efun([], _, _, _, _, _) {
            // The parser synthesizes this wrapper for an expression-local
            // contract. User-authored VC controls remain rejected.
            text
          } else {
            checked_text_attribute(text, span)
          }
          attributes.push(checked)
          { ..decoration, attributes, }
        }
        Position(position) => { ..decoration, location: source_span(position) }
      }
      self.type_decorated_program_expression(
        pure_space, program_space, locals, inner, nested, expected,
      )
    }
    Etuple(arguments) =>
      self.resolved_application(
        pure_space,
        program_space,
        locals,
        [tuple_constructor_name(arguments.length())],
        arguments,
        decoration,
        expected,
      )
    Ewhile(condition, invariant, variants, body) => {
      let boolean = self.boolean_ity(pure_space, program_space, span)
      let unit = self.unit_ity(pure_space, program_space, span)
      let condition = self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        condition,
        Some(boolean),
      )
      let body = self.type_program_expression_expected(
        pure_space,
        program_space,
        locals,
        body,
        Some(unit),
      )
      @mlw.Expr::while_loop(
        condition,
        self.type_program_invariant(
          pure_space,
          program_space,
          locals,
          invariant,
          expression.span,
        ),
        self.type_program_variants(
          pure_space,
          program_space,
          locals,
          variants,
          expression.span,
        ),
        body,
        boolean,
        unit,
        program_variables(
          locals,
          snapshots=self.materialized_snapshots(self.at_program_variables),
        ),
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Efor(ident, first, direction, last, invariant, body) => {
      let (first_expression, last_expression) = if program_loop_bound_needs_expected(
          first,
        ) &&
        !program_loop_bound_needs_expected(last) {
        let last_expression = self.type_program_expression(
          pure_space, program_space, locals, last,
        )
        (
          self.type_program_expression_expected(
            pure_space,
            program_space,
            locals,
            first,
            Some(last_expression.ity()),
          ),
          last_expression,
        )
      } else {
        let first_expression = self.type_program_expression(
          pure_space, program_space, locals, first,
        )
        (
          first_expression,
          self.type_program_expression_expected(
            pure_space,
            program_space,
            locals,
            last,
            Some(first_expression.ity()),
          ),
        )
      }
      let first_proxy = self.proxy_argument(
        first_expression,
        source_span(first.span),
        inherit_ghost_context=false,
      )
      let last_proxy = self.proxy_argument(
        last_expression,
        source_span(last.span),
        inherit_ghost_context=false,
      )
      let index = self.make_program_local(
        Some(ident),
        ident.span,
        first_proxy.0.view().ity,
        false,
      )
      let integer_symbol = pure_space.find_type([b"int"], span)
      let integer = @mlw.Ity::from_ty(
        program_space,
        @logic.Ty::app(integer_symbol, [], span),
        span,
      )
      let internal_index = if index.variable.view().ity == integer {
        index.variable
      } else {
        @mlw.PVariable::trusted_new(
          self.context,
          semantic_name(ident),
          integer,
          true,
          span,
        )
      }
      let nested = locals.to_owned()
      nested.push((ident.name, index))
      let unit = self.unit_ity(pure_space, program_space, span)
      let body = self.type_program_expression_expected(
        pure_space,
        program_space,
        nested,
        body,
        Some(unit),
      )
      let invariants = self.type_program_invariant(
        pure_space,
        program_space,
        nested,
        invariant,
        expression.span,
        logical_override=Some((index.variable, internal_index)),
      )
      let direction = match direction {
        To => @mlw.To
        DownTo => @mlw.DownTo
      }
      let bounds = @mlw.ForBounds::new(
        first_proxy.0,
        direction,
        last_proxy.0,
        span,
      )
      let variables = program_variables(
        nested,
        snapshots=self.materialized_snapshots(self.at_program_variables),
      )
      if internal_index != index.variable {
        variables.push(internal_index)
      }
      let loop_ = @mlw.Expr::for_loop(
        index.variable,
        bounds,
        internal_index,
        invariants,
        body,
        integer,
        unit,
        variables,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
      self.wrap_argument_proxies([first_proxy, last_proxy], loop_, decoration)
    }
    Erec(sources, body) => {
      let (definitions, nested_space, _) = self.type_recursive_routines(
        pure_space, program_space, locals, sources,
      )
      let definition = @mlw.LetDefinition::recursive(definitions, span)
      let body = self.type_program_expression_expected(
        pure_space, nested_space, locals, body, expected,
      )
      @mlw.Expr::let_definition(
        definition,
        body,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Eraise(exception, payload) => {
      let exception = program_space.find_exception(
        qualid_segments(exception),
        Some(qualid_span(exception)),
      )
      let exception_type = exception.view().ity
      let payload = match payload {
        Some(payload) =>
          self.type_program_expression_expected(
            pure_space,
            program_space,
            locals,
            payload,
            Some(exception_type),
          )
        None => {
          let unit = self.unit_ity(pure_space, program_space, span)
          if exception_type != unit {
            @logic.fail_type(
              TypeMismatch,
              span,
              "exception payload is required",
            )
          }
          self.zero_argument_pure_expression(
            pure_space, program_space, b"Tuple0", unit, decoration,
          )
        }
      }
      guard expected is Some(result) else {
        @logic.fail_type(
          UnresolvedTypeVariable,
          span,
          "cannot infer the result type of raise",
        )
      }
      @mlw.Expr::raise_exception(
        exception,
        payload,
        result,
        self.unit_ity(pure_space, program_space, span),
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Eexn(ident, payload_type, mask, body) => {
      let payload_type = self.program_ity(
        pure_space, program_space, payload_type, span,
      )
      let exception = @mlw.XSymbol::new(
        self.context,
        semantic_name(ident),
        payload_type,
        Some(source_span(ident.span)),
        mask=semantic_program_mask(mask),
      )
      let nested = program_space.overlay(
        @mlw.ProgramNamespace::empty().add_exception(
          ident.name,
          exception,
          Some(source_span(ident.span)),
        ),
      )
      let body = self.type_program_expression_expected(
        pure_space, nested, locals, body, expected,
      )
      @mlw.Expr::exception_scope(
        exception,
        body,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Eoptexn(ident, mask, body) => {
      if !program_expression_raises_name(body, ident.name) {
        return self.type_decorated_program_expression(
          pure_space, program_space, locals, body, decoration, expected,
        )
      }
      let payload_type = match expected {
        Some(expected) => expected
        None if ident.name == b"'Break" || ident.name == b"'Continue" =>
          self.unit_ity(pure_space, program_space, span)
        None =>
          match
            self.inferred_optional_exception_payload(
              pure_space,
              program_space,
              locals,
              body,
              ident.name,
            ) {
            Some(inferred) => inferred
            None =>
              @logic.fail_type(
                UnresolvedTypeVariable,
                span,
                "cannot infer the optional exception payload type",
              )
          }
      }
      let semantic_mask = semantic_program_mask(mask)
      let exception = @mlw.XSymbol::new(
        self.context,
        semantic_name(ident),
        payload_type,
        Some(source_span(ident.span)),
        mask=semantic_mask,
      )
      let nested = program_space.overlay(
        @mlw.ProgramNamespace::empty().add_exception(
          ident.name,
          exception,
          Some(source_span(ident.span)),
        ),
      )
      let body = self.type_program_expression_expected(
        pure_space,
        nested,
        locals,
        body,
        Some(payload_type),
      )
      if !body.effect().view().raises.any(raised => raised == exception) {
        body
      } else {
        let unit = self.unit_ity(pure_space, program_space, span)
        let variables : Array[@mlw.PVariable] = if payload_type == unit {
          []
        } else {
          match (semantic_mask, payload_type.view()) {
            (@mlw.Tuple(masks), ItyApp(_, items, _)) if masks.length() ==
              items.length() =>
              [
                for index, item in items => {
                  @mlw.PVariable::trusted_new(
                    self.context,
                    @theory.SemanticName::new(b"r", [b"mlw:proxy_symbol"], None),
                    item,
                    masks[index].is_ghost(),
                    None,
                  )
                }
              ]
            _ =>
              [
                @mlw.PVariable::trusted_new(
                  self.context,
                  @theory.SemanticName::new(b"r", [b"mlw:proxy_symbol"], None),
                  payload_type,
                  semantic_mask.is_ghost(),
                  None,
                ),
              ]
          }
        }
        let synthesized_origin = @identity.Origin::user(b"", None, [])
        let recovered = match variables {
          [variable] => @mlw.Expr::variable(variable, synthesized_origin, [])
          _ => {
            let tuple = program_space.find_routine(
              [tuple_constructor_name(variables.length())],
              None,
            )
            @mlw.Expr::routine_call(
              tuple,
              variables,
              payload_type,
              synthesized_origin,
              [],
              None,
            )
          }
        }
        let branch = @mlw.ExceptionalBranch::new(
          exception,
          variables,
          recovered,
          None,
        )
        let caught = @mlw.Expr::match_with(
          body,
          [],
          [branch],
          unit,
          synthesized_origin,
          [],
          None,
        )
        @mlw.Expr::exception_scope(
          exception,
          caught,
          program_origin(decoration),
          decoration.attributes,
          span,
        )
      }
    }
    Eghost(inner) => {
      let saved_ghost_context = self.ghost_context
      self.ghost_context = true
      let inner = self.type_program_expression_expected(
        pure_space, program_space, locals, inner, expected,
      ) catch {
        error => {
          self.ghost_context = saved_ghost_context
          raise error
        }
      }
      self.ghost_context = saved_ghost_context
      inner.ghostify(
        true,
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Eref =>
      fail_invalid_input(
        InvalidDeclaration,
        ProgramTyping,
        span,
        "the reference constructor requires an argument",
      )
    Easref(Qident(ident)) =>
      match find_program_local(locals, ident.name) {
        Some(binding) if binding.reference =>
          @mlw.Expr::variable(
            binding.variable,
            program_origin(decoration),
            decoration.attributes,
          )
        _ =>
          @logic.fail_type(
            TypeMismatch,
            span,
            "reference escape expects a reference-marked local variable",
          )
      }
    Easref(_) =>
      @logic.fail_type(
        TypeMismatch,
        span,
        "reference escape expects an unqualified local variable",
      )
    Eassign(assignments) =>
      self.program_assignment(
        pure_space, program_space, locals, assignments, decoration,
      )
    Efun(_, _, _, _, _, _) | Eany(_, _, _, _, _, _) => {
      let identifier = @parser.Ident::{
        name: b"anonymous",
        attributes: [],
        span: expression.span,
      }
      let routine = self.type_routine_expression(
        pure_space,
        program_space,
        locals,
        identifier,
        false,
        RKnone,
        expression,
        expected,
      )
      let execution_cty = self.computation_type_for_execution(
        pure_space,
        program_space,
        routine.cexp,
        span,
      )
      let executable = if execution_cty.view().arguments.is_empty() {
        execution_cty
      } else {
        execution_cty.execute_as_function(
          self.context,
          program_space.find_type([b"infix ->"], span),
          pure_space.find_logic([b"infix @"], span),
          span,
        )
      }
      @mlw.Expr::trusted_new(
        Eexec(routine.cexp, executable),
        executable.view().result,
        program_origin(decoration),
        decoration.attributes,
        executable.view().effect,
        executable.view().mask,
        span,
      )
    }
    Eidpur(qualid) =>
      match qualid {
        Qident(ident) if find_program_local(locals, ident.name) is Some(binding) =>
          @mlw.Expr::pure_term(
            @logic.Term::variable(binding.variable.view().pure_symbol),
            binding.variable.view().ity.purify(),
            [binding.variable],
            program_origin(decoration),
            decoration.attributes,
            span,
          )
        _ =>
          match program_space.find_variable_option(qualid_segments(qualid)) {
            Some(variable) =>
              @mlw.Expr::pure_term(
                @logic.Term::variable(variable.view().pure_symbol),
                variable.view().ity.purify(),
                [variable],
                program_origin(decoration),
                decoration.attributes,
                span,
              )
            None =>
              self.pure_application(
                pure_space,
                program_space,
                locals,
                qualid_segments(qualid),
                [],
                decoration,
                expected,
              )
          }
      }
    Epure(term) => {
      let expanded = self.program_logic_mappings(program_space, expression.span)
      expanded.push_iter(locals.iter())
      let (logic_locals, logic_values) = program_logic_scope(expanded)
      let (term, result_ty) = self.pure.program_term(
        pure_space,
        logic_locals,
        logic_values,
        term,
        at_values=self.at_values,
        at_labels=self.at_labels,
        at_resolver=entry => self.materialize_at_value(entry),
      )
      let term = match term.ty() {
        Some(_) => term
        None =>
          @logic.Term::if_then_else(
            term,
            program_boolean_term(pure_space, true, None),
            program_boolean_term(pure_space, false, None),
            term.source_span(),
          ).source_decorate(term.source_span(), term.attributes())
      }
      let result = @mlw.Ity::from_ty(program_space, result_ty, span)
      @mlw.Expr::pure_term(
        term,
        result,
        program_variables(
          expanded,
          snapshots=self.materialized_snapshots(self.at_program_variables),
        ),
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Elabel(label, body) =>
      self.program_labeled_expression(
        pure_space, program_space, locals, label, body, decoration, expected,
      )
    Eabsurd =>
      match expected {
        Some(result) =>
          @mlw.Expr::absurd(
            result,
            program_origin(decoration),
            decoration.attributes,
          )
        None =>
          @logic.fail_type(
            UnresolvedTypeVariable,
            span,
            "cannot infer the result type of absurd",
          )
      }
    Ematch(scrutinee, regular_sources, exceptional_sources) => {
      let mut branch_result = expected
      let exceptional_bodies : Array[@mlw.Expr?] = [
        for _ in exceptional_sources => None
      ]
      if regular_sources.is_empty() {
        for index, branch in exceptional_sources {
          if branch.pattern is None &&
            !program_expression_needs_expected(branch.body) {
            let body = self.type_program_expression(
              pure_space,
              program_space,
              locals,
              branch.body,
            )
            let compatible = expected is None ||
              program_ity_skeleton_compatible(
                expected.unwrap(),
                body.ity(),
                Some(source_span(branch.body.span)),
              )
            if compatible && !program_ity_has_inference_variables(body.ity()) {
              branch_result = Some(body.ity())
              exceptional_bodies[index] = Some(body)
              break
            }
          }
        }
      }
      let scrutinee_expected = if regular_sources.is_empty() {
        branch_result
      } else {
        None
      }
      let scrutinee = self.type_program_expression_expected(
        pure_space, program_space, locals, scrutinee, scrutinee_expected,
      )
      if regular_sources.is_empty() && branch_result is None {
        branch_result = Some(scrutinee.ity())
      }
      let regular_patterns : Array[@mlw.ProgramPattern] = []
      let regular_locals : Array[Array[(Bytes, ProgramLocal)]] = []
      for branch in regular_sources {
        let pattern = @mlw.ProgramPattern::new(
          self.context,
          self.program_prepattern(pure_space, program_space, branch.pattern),
          scrutinee.ity(),
          scrutinee.mask(),
          Some(source_span(branch.pattern.span)),
        )
        let nested = self.extend_pattern_locals(
          locals,
          pattern,
          branch.pattern.span,
        )
        regular_patterns.push(pattern)
        regular_locals.push(nested)
      }
      let regular_bodies : Array[@mlw.Expr?] = [
        for _ in regular_sources => None
      ]
      if branch_result is None {
        let mut seed = -1
        let mut fallback_seed = -1
        let mut fallback_body : @mlw.Expr? = None
        for index, branch in regular_sources {
          if !program_expression_needs_expected(branch.body) {
            let body = self.type_program_expression(
              pure_space,
              program_space,
              regular_locals[index],
              branch.body,
            )
            if !program_ity_has_inference_variables(body.ity()) {
              seed = index
              branch_result = Some(body.ity())
              regular_bodies[index] = Some(body)
              break
            }
            if fallback_seed < 0 {
              fallback_seed = index
              fallback_body = Some(body)
            }
          }
        }
        if seed < 0 && fallback_seed >= 0 {
          seed = fallback_seed
          guard fallback_body is Some(body) else {
            abort("match result inference lost its fallback branch")
          }
          branch_result = Some(body.ity())
          regular_bodies[seed] = Some(body)
        }
        if seed < 0 {
          @logic.fail_type(
            UnresolvedTypeVariable,
            Some(source_span(regular_sources[0].body.span)),
            "cannot infer the result type of a bottom match branch",
          )
        }
      }
      let typed_regular_bodies : Array[@mlw.Expr] = []
      for index, branch in regular_sources {
        let body = match regular_bodies[index] {
          Some(body) => body
          None =>
            self.type_program_expression_expected(
              pure_space,
              program_space,
              regular_locals[index],
              branch.body,
              branch_result,
            )
        }
        typed_regular_bodies.push(body)
      }
      if branch_result is Some(result) &&
        program_ity_has_inference_variables(result) {
        let mut refined : @mlw.Ity? = None
        for body in typed_regular_bodies {
          if !program_ity_has_inference_variables(body.ity()) &&
            program_ity_skeleton_compatible(
              result,
              body.ity(),
              Some(source_span(expression.span)),
            ) {
            refined = Some(body.ity())
            break
          }
        }
        if refined is Some(refined_result) {
          branch_result = Some(refined_result)
          for index, branch in regular_sources {
            if typed_regular_bodies[index].ity() != refined_result {
              typed_regular_bodies[index] = self.type_program_expression_expected(
                pure_space,
                program_space,
                regular_locals[index],
                branch.body,
                Some(refined_result),
              )
            }
          }
        }
      }
      let regular : Array[@mlw.RegularBranch] = []
      for index, branch in regular_sources {
        regular.push(
          @mlw.RegularBranch::new(
            regular_patterns[index],
            typed_regular_bodies[index],
            Some(source_span(branch.pattern.span)),
          ),
        )
      }
      if !regular.is_empty() {
        let rows = [
          for pattern in regular_patterns => [pattern.view().pattern]
        ]
        if !self.pure.known.patterns_are_exhaustive(
            [scrutinee.ity().to_ty(span)],
            rows,
            span,
          ) {
          guard branch_result is Some(result) else {
            abort("typed match branches lost their result type")
          }
          let wildcard = @mlw.ProgramPattern::new(
            self.context,
            @mlw.PPwild,
            scrutinee.ity(),
            scrutinee.mask(),
            span,
          )
          regular.push(
            @mlw.RegularBranch::new(
              wildcard,
              @mlw.Expr::absurd(
                result,
                program_origin(decoration),
                decoration.attributes,
              ),
              span,
            ),
          )
        }
      }
      let exceptional : Array[@mlw.ExceptionalBranch] = []
      for index, branch in exceptional_sources {
        let exception = program_space.find_exception(
          qualid_segments(branch.exception),
          Some(qualid_span(branch.exception)),
        )
        let exception_view = exception.view()
        let (variables, body) = match branch.pattern {
          None => {
            let unit = self.unit_ity(pure_space, program_space, span)
            if exception_view.ity != unit {
              @logic.fail_type(
                TypeMismatch,
                Some(source_span(branch.body.span)),
                "exception argument expected",
              )
            }
            (
              [],
              match exceptional_bodies[index] {
                Some(body) => body
                None =>
                  self.type_program_expression_expected(
                    pure_space,
                    program_space,
                    locals,
                    branch.body,
                    branch_result,
                  )
              },
            )
          }
          Some(source_pattern) => {
            let pattern = @mlw.ProgramPattern::new(
              self.context,
              self.program_prepattern(pure_space, program_space, source_pattern),
              exception_view.ity,
              exception_view.mask,
              Some(source_span(source_pattern.span)),
            )
            let nested = self.extend_pattern_locals(
              locals,
              pattern,
              source_pattern.span,
            )
            let branch_body = self.type_program_expression_expected(
              pure_space,
              program_space,
              nested,
              branch.body,
              branch_result,
            )
            match pattern.view().pattern.view() {
              @logic.Pvar(_) =>
                (pattern.view().variables.to_owned(), branch_body)
              @logic.Pwild(_) => {
                let unit = self.unit_ity(pure_space, program_space, span)
                if exception_view.ity == unit {
                  ([], branch_body)
                } else {
                  let payload = @mlw.PVariable::trusted_new(
                    self.context,
                    @theory.SemanticName::new(b"_", [], span),
                    exception_view.ity,
                    exception_view.mask.is_ghost(),
                    span,
                  )
                  ([payload], branch_body)
                }
              }
              @logic.Papp(_, arguments, _) if arguments.is_empty() &&
                exception_view.ity ==
                self.unit_ity(pure_space, program_space, span) =>
                ([], branch_body)
              _ => {
                let payload = @mlw.PVariable::trusted_new(
                  self.context,
                  @theory.SemanticName::new(b"q", [b"mlw:proxy_symbol"], span),
                  exception_view.ity,
                  exception_view.mask.is_ghost(),
                  span,
                )
                let nested_match = @mlw.Expr::match_with(
                  @mlw.Expr::variable(
                    payload,
                    program_origin(decoration),
                    decoration.attributes,
                  ),
                  [
                    @mlw.RegularBranch::new(
                      pattern,
                      branch_body,
                      Some(source_span(source_pattern.span)),
                    ),
                  ],
                  [],
                  self.unit_ity(pure_space, program_space, span),
                  program_origin(decoration),
                  decoration.attributes,
                  span,
                )
                ([payload], nested_match)
              }
            }
          }
        }
        if branch_result is None {
          branch_result = Some(body.ity())
        }
        exceptional.push(
          @mlw.ExceptionalBranch::new(
            exception,
            variables,
            body,
            Some(source_span(branch.body.span)),
          ),
        )
      }
      if regular.is_empty() && exceptional.is_empty() {
        @logic.fail_type(TypeMismatch, span, "match expression has no branches")
      }
      @mlw.Expr::match_with(
        scrutinee,
        regular,
        exceptional,
        self.unit_ity(pure_space, program_space, span),
        program_origin(decoration),
        decoration.attributes,
        span,
      )
    }
    Erecord(fields) =>
      self.program_record_expression(
        pure_space, program_space, locals, fields, decoration, expected,
      )
    Eupdate(source, fields) =>
      self.program_record_update(
        pure_space, program_space, locals, source, fields, decoration, expected,
      )
  }
  if expected is Some(expected) {
    validate_program_ity_skeleton(
      expected,
      typed.ity(),
      span,
      "program expression has a different type than its context expects",
    )
  }
  typed
}

///|
fn validate_program_mask(
  mask : @parser.Mask,
  span : @identity.SourceSpan?,
) -> Unit {
  ignore(span)
  ignore(semantic_program_mask(mask))
}

///|
fn validate_routine_result_pattern(pattern : @parser.Pattern) -> Unit {
  // Result patterns are elaborated by `ProgramPattern` when postconditions are
  // opened. Keeping this boundary permissive is required for named and
  // mixed-ghost tuple results.
  ignore(pattern)
}

///|
priv struct TypedRoutine {
  symbol : @mlw.RoutineSymbol
  computation : @mlw.ProgramComputation
  cexp : @mlw.Cexp
  variants : Array[@mlw.ProgramVariant]
  pure_declarations : Array[@logic.Decl]
}

///|
fn conjoin_program_formulas(
  formulas : ArrayView[@logic.Term],
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  if formulas.is_empty() {
    return @logic.Term::true_formula()
  }
  let mut result = formulas[0]
  for index = 1; index < formulas.length(); index = index + 1 {
    result = @logic.Term::binary(And, result, formulas[index], span)
  }
  result
}

///|
fn copy_spec_term_decoration(
  source : @logic.Term,
  replacement : @logic.Term,
) -> @logic.Term {
  let attributes = replacement.attributes().to_owned()
  attributes.push_iter(source.attributes().iter())
  let source_span = match replacement.source_span() {
    Some(span) => Some(span)
    None => source.source_span()
  }
  let decorated = replacement.source_decorate(source_span, attributes)
  match replacement.origin() {
    Some(origin) => decorated.decorate(origin, attributes)
    None =>
      match source.origin() {
        Some(origin) => decorated.decorate(origin, attributes)
        None => decorated
      }
  }
}

///|
fn insert_program_logic_definition(
  pure_space : @theory.Namespace,
  head : @logic.Term,
  body : @logic.Term,
  _span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let rebuilt = match body.view() {
    Tif(condition, consequent, alternative) =>
      @logic.Term::if_then_else(
        condition,
        insert_program_logic_definition(pure_space, head, consequent, None),
        insert_program_logic_definition(pure_space, head, alternative, None),
        None,
      )
    Tlet(variable, value, inner) =>
      @logic.Term::let_in(
        variable,
        value,
        insert_program_logic_definition(pure_space, head, inner, None),
        None,
      )
    Tcase(scrutinee, branches) =>
      @logic.Term::case(
        scrutinee,
        [
          for branch in branches => {
            let branch = branch.view()
            (
              branch.pattern,
              insert_program_logic_definition(
                pure_space,
                head,
                branch.body,
                None,
              ),
            )
          }
        ],
        None,
      )
    _ =>
      if head == body {
        @logic.Term::true_formula()
      } else {
        match head.ty() {
          Some(_) =>
            @logic.Term::elaborated_apply(
              pure_space.find_logic([b"infix ="], None),
              [head, body],
              None,
              None,
            )
          None =>
            match (head.view(), body.view()) {
              (Ttrue, _) => body
              (_, Ttrue) => head
              _ => @logic.Term::binary(Iff, head, body, None)
            }
        }
      }
  }
  rebuilt
}

///|
fn ProgramTyping::program_logic_definition_axiom(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  ident : @parser.Ident,
  definition : @logic.LogicDefinition,
) -> @logic.Decl raise {
  let span = Some(source_span(ident.span))
  let definition = definition.view()
  let head = @logic.Term::elaborated_apply(
    definition.symbol,
    [
      for parameter in definition.parameters => @logic.Term::variable(parameter)
    ],
    definition.body.ty(),
    None,
  )
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    definition.parameters,
    [],
    insert_program_logic_definition(pure_space, head, definition.body, span),
    None,
  )
  let name = definition.symbol.view().name + b"'def"
  let origin = @identity.Origin::user(name, span, [
    b"W:non_conservative_extension:N",
  ])
  @logic.Decl::proposition(
    self.context,
    origin,
    Paxiom,
    @logic.PrSymbol::new(self.context, name, origin),
    formula,
    span,
  )
}

///|
fn ProgramTyping::program_logic_contract_definition_axiom(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  ident : @parser.Ident,
  cty : @mlw.Cty,
  definition : @logic.LogicDefinition,
) -> @logic.Decl? raise {
  let span = Some(source_span(ident.span))
  let definition = definition.view()
  let view = cty.view()
  let head = @logic.Term::elaborated_apply(
    definition.symbol,
    [
      for parameter in definition.parameters => @logic.Term::variable(parameter)
    ],
    definition.body.ty(),
    span,
  )
  let mut formula = insert_program_logic_definition(
    pure_space,
    head,
    definition.body,
    span,
  )
  if formula.view() is Ttrue {
    return None
  }
  if !view.oldies.is_empty() {
    let mut oldies = @logic.TermSubstitution::new()
    for oldie in view.oldies {
      let oldie = oldie.view()
      oldies = oldies.bind(
        oldie.snapshot.view().pure_symbol,
        @logic.Term::variable(oldie.original.view().pure_symbol),
        None,
      )
    }
    formula = oldies.apply(self.context, formula, None)
  }
  for precondition in view.preconditions.rev() {
    formula = @logic.Term::binary(Implies, precondition, formula, None)
  }
  let free = formula.free_variables()
  let arguments : Array[@logic.VSymbol] = []
  for argument in view.arguments {
    let variable = argument.view().pure_symbol
    if free.any(item => item == variable) {
      arguments.push(variable)
    }
  }
  if !arguments.is_empty() {
    formula = @logic.Term::quantify(
      ForallQuantifier,
      arguments,
      [],
      formula,
      span,
    )
  }
  let remaining = formula.free_variables()
  remaining.sort_by((left, right) => {
    left.semantic_id().local_id().compare(right.semantic_id().local_id())
  })
  if !remaining.is_empty() {
    formula = @logic.Term::quantify(
      ForallQuantifier,
      remaining,
      [],
      formula,
      span,
    )
  }
  let name = definition.symbol.view().name + b"'def"
  let origin = @identity.Origin::user(name, span, [
    b"W:non_conservative_extension:N",
  ])
  Some(
    @logic.Decl::proposition(
      self.context,
      origin,
      Paxiom,
      @logic.PrSymbol::new(self.context, name, origin),
      formula,
      span,
    ),
  )
}

///|
fn ProgramTyping::zero_argument_logic_definition_axiom(
  self : ProgramTyping,
  ident : @parser.Ident,
  cty : @mlw.Cty,
  logic : @logic.LSymbol,
) -> @logic.Decl? raise {
  let span = Some(source_span(ident.span))
  guard logic.view().result_type is Some(result_type) else { return None }
  let application = @logic.Term::elaborated_apply(
    logic,
    [],
    Some(result_type),
    span,
  )
  let formulas : Array[@logic.Term] = []
  for postcondition in cty.view().postconditions {
    let view = postcondition.view()
    formulas.push(
      @logic.TermSubstitution::new()
      .bind(view.result, application, span)
      .apply(self.context, view.formula, span),
    )
  }
  if formulas.is_empty() {
    return None
  }
  let mut formula = formulas[formulas.length() - 1]
  let mut index = formulas.length() - 2
  while index >= 0 {
    formula = @logic.Term::binary(And, formulas[index], formula, span)
    index = index - 1
  }
  if formula.view() is Ttrue {
    return None
  }
  let name = logic.view().name + b"'def"
  let origin = @identity.Origin::user(name, span, [
    b"W:non_conservative_extension:N",
  ])
  Some(
    @logic.Decl::proposition(
      self.context,
      origin,
      Paxiom,
      @logic.PrSymbol::new(self.context, name, origin),
      formula,
      span,
    ),
  )
}

///|
fn is_program_boolean_constant(
  term : @logic.Term,
  symbol : @logic.LSymbol,
) -> Bool {
  term.view() is Tapp(actual, _, arguments) &&
  actual == symbol &&
  arguments.is_empty()
}

///|
fn ProgramTyping::substitute_predicate_spec_result(
  self : ProgramTyping,
  term : @logic.Term,
  result : @logic.VSymbol,
  predicate : @logic.Term,
  equality : @logic.LSymbol,
  boolean_true : @logic.LSymbol,
  boolean_false : @logic.LSymbol,
) -> @logic.Term raise {
  let recurse = fn(child : @logic.Term) -> @logic.Term raise {
    self.substitute_predicate_spec_result(
      child, result, predicate, equality, boolean_true, boolean_false,
    )
  }
  let rebuilt = match term.view() {
    Tvar(variable) =>
      if variable == result {
        let true_value = @logic.Term::elaborated_apply(
          boolean_true,
          [],
          boolean_true.view().result_type,
          None,
        )
        let false_value = @logic.Term::elaborated_apply(
          boolean_false,
          [],
          boolean_false.view().result_type,
          None,
        )
        @logic.Term::if_then_else(predicate, true_value, false_value, None)
      } else {
        return term
      }
    Tconst(_) => return term
    Tapp(symbol, _, arguments) =>
      if symbol == equality &&
        arguments.length() == 2 &&
        arguments[0].view() is Tvar(variable) &&
        variable == result &&
        !arguments[1].free_variables().any(item => item == result) {
        if is_program_boolean_constant(arguments[1], boolean_true) {
          predicate
        } else {
          let true_value = @logic.Term::elaborated_apply(
            boolean_true,
            [],
            boolean_true.view().result_type,
            None,
          )
          let is_true = @logic.Term::elaborated_apply(
            equality,
            [recurse(arguments[1]), true_value],
            None,
            None,
          )
          @logic.Term::binary(Iff, predicate, is_true, None)
        }
      } else {
        @logic.Term::elaborated_apply(
          symbol,
          [
            for argument in arguments => recurse(argument)
          ],
          term.ty(),
          None,
        )
      }
    Tif(condition, then_branch, else_branch) =>
      @logic.Term::if_then_else(
        recurse(condition),
        recurse(then_branch),
        recurse(else_branch),
        None,
      )
    Tlet(variable, value, body) =>
      @logic.Term::let_in(variable, recurse(value), recurse(body), None)
    Tcase(scrutinee, branches) =>
      @logic.Term::case(
        recurse(scrutinee),
        [
          for branch in branches => {
            let branch = branch.view()
            (branch.pattern, recurse(branch.body))
          }
        ],
        None,
      )
    Teps(variable, body) => @logic.Term::epsilon(variable, recurse(body), None)
    Tquant(quantifier, binders, triggers, body) =>
      @logic.Term::quantify(
        quantifier,
        binders,
        [
          for group in triggers => [ for trigger in group => recurse(trigger) ]
        ],
        recurse(body),
        None,
      )
    Tbinop(operator, left, right) =>
      @logic.Term::binary(operator, recurse(left), recurse(right), None)
    Tnot(inner) => @logic.Term::not(recurse(inner), None)
    Ttrue | Tfalse => return term
  }
  copy_spec_term_decoration(term, rebuilt)
}

///|
fn ProgramTyping::routine_logic_spec_axioms(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  ident : @parser.Ident,
  cty : @mlw.Cty,
  logic : @logic.LSymbol,
) -> Array[@logic.Decl] raise {
  let span = Some(source_span(ident.span))
  let view = cty.view()
  if view.postconditions.is_empty() {
    return []
  }
  let arguments = view.arguments.map(argument => {
    @logic.Term::variable(argument.view().pure_symbol)
  })
  let application = @logic.Term::elaborated_apply(
    logic,
    arguments,
    logic.view().result_type,
    None,
  )
  let equality = pure_space.find_logic([b"infix ="], span)
  let boolean_true = pure_space.find_logic([b"True"], span)
  let boolean_false = pure_space.find_logic([b"False"], span)
  let declarations : Array[@logic.Decl] = []
  for index, postcondition in view.postconditions {
    let postcondition = postcondition.view()
    let mut formula = match logic.view().result_type {
      Some(_) =>
        @logic.TermSubstitution::new()
        .bind(postcondition.result, application, None)
        .apply(self.context, postcondition.formula, None)
      None =>
        self.substitute_predicate_spec_result(
          postcondition.formula,
          postcondition.result,
          application,
          equality,
          boolean_true,
          boolean_false,
        )
    }
    if !view.oldies.is_empty() {
      let mut oldies = @logic.TermSubstitution::new()
      for oldie in view.oldies {
        let oldie = oldie.view()
        oldies = oldies.bind(
          oldie.snapshot.view().pure_symbol,
          @logic.Term::variable(oldie.original.view().pure_symbol),
          None,
        )
      }
      formula = oldies.apply(self.context, formula, None)
    }
    for precondition in view.preconditions.rev() {
      formula = @logic.Term::binary(Implies, precondition, formula, None)
    }
    let free = formula.free_variables()
    let binders : Array[@logic.VSymbol] = []
    for argument in view.arguments {
      let variable = argument.view().pure_symbol
      if free.any(item => item == variable) {
        binders.push(variable)
      }
    }
    let remaining = [
      for variable in free if !binders.any(item => item == variable) => variable
    ]
    remaining.sort_by((left, right) => {
      left.semantic_id().local_id().compare(right.semantic_id().local_id())
    })
    binders.push_iter(remaining.iter())
    formula = @logic.Term::quantify(
      ForallQuantifier,
      binders,
      [],
      formula,
      None,
    )
    if formula.view() is Ttrue {
      continue
    }
    let proposition_name = if index + 1 == view.postconditions.length() {
      ident.name + b"'spec"
    } else {
      let output = @buffer.Buffer()
      output.write_bytes(ident.name)
      output.write_bytes(b"'spec'")
      output.write_string_utf8(
        (view.postconditions.length() - index - 2).to_string(),
      )
      output.to_bytes()
    }
    let origin = @identity.Origin::user(proposition_name, span, [
      b"W:non_conservative_extension:N",
    ])
    declarations.push(
      @logic.Decl::proposition(
        self.context,
        origin,
        Paxiom,
        @logic.PrSymbol::new(self.context, proposition_name, origin),
        formula,
        span,
      ),
    )
  }
  declarations
}

///|
fn ProgramTyping::lemma_pure_axiom(
  self : ProgramTyping,
  ident : @parser.Ident,
  cty : @mlw.Cty,
  proposition_name : Bytes,
  conclusion : @logic.Term,
) -> @logic.Decl? raise {
  let span = Some(source_span(ident.span))
  let view = cty.view()
  let mut formula = conclusion
  if !view.oldies.is_empty() {
    let mut oldies = @logic.TermSubstitution::new()
    for oldie in view.oldies {
      let oldie = oldie.view()
      oldies = oldies.bind(
        oldie.snapshot.view().pure_symbol,
        @logic.Term::variable(oldie.original.view().pure_symbol),
        None,
      )
    }
    formula = oldies.apply(self.context, formula, None)
  }
  for precondition in view.preconditions.rev() {
    formula = @logic.Term::binary(Implies, precondition, formula, None)
  }
  let free = formula.free_variables()
  let binders : Array[@logic.VSymbol] = []
  for argument in view.arguments {
    let variable = argument.view().pure_symbol
    if free.any(item => item == variable) {
      binders.push(variable)
    }
  }
  let remaining = [
    for variable in free if !binders.any(item => item == variable) => variable
  ]
  remaining.sort_by((left, right) => {
    left.semantic_id().local_id().compare(right.semantic_id().local_id())
  })
  binders.push_iter(remaining.iter())
  formula = @logic.Term::quantify(ForallQuantifier, binders, [], formula, None)
  if formula.view() is Ttrue {
    return None
  }
  let origin = @identity.Origin::user(proposition_name, span, [
    b"W:non_conservative_extension:N",
  ])
  Some(
    @logic.Decl::proposition(
      self.context,
      origin,
      Paxiom,
      @logic.PrSymbol::new(self.context, proposition_name, origin),
      formula,
      span,
    ),
  )
}

///|
fn ProgramTyping::lemma_pure_declarations(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  ident : @parser.Ident,
  cty : @mlw.Cty,
) -> Array[@logic.Decl] raise {
  let span = Some(source_span(ident.span))
  let view = cty.view()
  if view.postconditions.is_empty() {
    return []
  }
  let tuple0 = pure_space.find_logic([b"Tuple0"], span)
  guard tuple0.view().result_type is Some(unit_type) else {
    abort("unit constructor lost its result type")
  }
  let postconditions : Array[@logic.Term] = []
  if view.result.to_ty(span) == unit_type {
    let unit_value = @logic.Term::elaborated_apply(
      tuple0,
      [],
      Some(unit_type),
      None,
    )
    let declarations : Array[@logic.Decl] = []
    for index, postcondition in view.postconditions {
      let postcondition = postcondition.view()
      let substitution = @logic.TermSubstitution::new().bind(
        postcondition.result,
        unit_value,
        None,
      )
      let proposition_name = if index + 1 == view.postconditions.length() {
        ident.name
      } else {
        let output = @buffer.Buffer()
        output.write_bytes(ident.name)
        output.write_bytes(b"'")
        output.write_string_utf8(
          (view.postconditions.length() - index - 2).to_string(),
        )
        output.to_bytes()
      }
      if self.lemma_pure_axiom(
          ident,
          cty,
          proposition_name,
          substitution.apply(self.context, postcondition.formula, None),
        )
        is Some(declaration) {
        declarations.push(declaration)
      }
    }
    return declarations
  }
  let first = view.postconditions[0].view()
  let result = @logic.Term::variable(first.result)
  postconditions.push(first.formula)
  for index = 1; index < view.postconditions.length(); index = index + 1 {
    let postcondition = view.postconditions[index].view()
    postconditions.push(
      @logic.TermSubstitution::new()
      .bind(postcondition.result, result, None)
      .apply(self.context, postcondition.formula, None),
    )
  }
  let conclusion = @logic.Term::quantify(
    ExistsQuantifier,
    [first.result],
    [],
    conjoin_program_formulas(postconditions, span),
    None,
  )
  match self.lemma_pure_axiom(ident, cty, ident.name, conclusion) {
    Some(declaration) => [declaration]
    None => []
  }
}

///|
fn program_boolean_term(
  pure_space : @theory.Namespace,
  value : Bool,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let symbol = pure_space.find_logic(
    [if value { b"True" } else { b"False" }],
    span,
  )
  @logic.Term::elaborated_apply(symbol, [], symbol.view().result_type, span)
}

///|
fn coerce_program_pure_term(
  pure_space : @theory.Namespace,
  term : @logic.Term,
  formula_expected : Bool,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  match (term.ty(), formula_expected) {
    (Some(_), true) =>
      match term.view() {
        Tif(condition, consequent, alternative) if program_pure_is_boolean_constant(
            consequent, true,
          ) &&
          program_pure_is_boolean_constant(alternative, false) =>
          condition.source_decorate(term.source_span(), term.attributes())
        Tapp(symbol, _, arguments) if arguments.is_empty() &&
          symbol.view().name == b"True" => @logic.Term::true_formula()
        Tapp(symbol, _, arguments) if arguments.is_empty() &&
          symbol.view().name == b"False" => @logic.Term::false_formula()
        _ =>
          @logic.Term::elaborated_apply(
            pure_space.find_logic([b"infix ="], span),
            [term, program_boolean_term(pure_space, true, span)],
            None,
            span,
          )
      }
    (None, false) =>
      @logic.Term::if_then_else(
        term,
        program_boolean_term(pure_space, true, span),
        program_boolean_term(pure_space, false, span),
        span,
      )
    _ => term
  }
}

///|
fn pure_computation_application(
  computation : @mlw.Cexp,
  result : @mlw.Ity,
  span : @identity.SourceSpan?,
  recursive_logic : ArrayView[(@mlw.RoutineSymbol, @logic.LSymbol)],
) -> @logic.Term? raise {
  match computation.view() {
    Cpur(symbol, arguments) =>
      Some(
        @logic.Term::elaborated_apply(
          symbol,
          [
            for argument in arguments => {
              @logic.Term::variable(argument.view().pure_symbol)
            }
          ],
          if symbol.view().result_type is Some(_) {
            Some(result.to_ty(span))
          } else {
            None
          },
          span,
        ),
      )
    Capp(routine, arguments) => {
      let mut mapped : @logic.LSymbol? = None
      for entry in recursive_logic {
        if entry.0 == routine {
          mapped = Some(entry.1)
          break
        }
      }
      let logic = match mapped {
        Some(symbol) => Some(symbol)
        None =>
          match routine.view().logic {
            RLls(symbol) => Some(symbol)
            RLnone | RLpv(_) | RLlemma => None
          }
      }
      match logic {
        Some(symbol) =>
          Some(
            @logic.Term::elaborated_apply(
              symbol,
              [
                for argument in arguments => {
                  @logic.Term::variable(argument.view().pure_symbol)
                }
              ],
              if symbol.view().result_type is Some(_) {
                Some(result.to_ty(span))
              } else {
                None
              },
              span,
            ),
          )
        None => None
      }
    }
    Cfun(_) | Cany => None
  }
}

///|
fn pure_function_computation_term(
  context : @identity.CompilationContext,
  pure_space : @theory.Namespace,
  computation : @mlw.Cexp,
  result : @mlw.Ity,
  span : @identity.SourceSpan?,
  recursive_logic : ArrayView[(@mlw.RoutineSymbol, @logic.LSymbol)],
) -> @logic.Term? raise {
  guard computation.view() is Cfun(body) else { return None }
  let arguments = computation.cty().view().arguments
  if arguments.is_empty() {
    return program_expression_pure_term(
      context,
      pure_space,
      body,
      false,
      span,
      recursive_logic~,
    )
  }
  guard program_expression_pure_term(
      context,
      pure_space,
      body,
      false,
      span,
      recursive_logic~,
    )
    is Some(body_term) else {
    return None
  }
  let closure = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", None, []),
    result.to_ty(span),
    None,
  )
  let application = pure_space.find_logic([b"infix @"], span)
  let mut head = @logic.Term::variable(closure)
  let mut head_type = result.to_ty(span)
  for argument in arguments {
    let next_type = semantic_function_result(head_type, span)
    head = @logic.Term::elaborated_apply(
      application,
      [head, @logic.Term::variable(argument.view().pure_symbol)],
      Some(next_type),
      span,
    )
    head_type = next_type
  }
  let definition = @logic.Term::elaborated_apply(
    pure_space.find_logic([b"infix ="], span),
    [head, body_term],
    None,
    span,
  ).source_decorate(body_term.source_span(), [])
  Some(
    @logic.Term::epsilon(
      closure,
      @logic.Term::quantify(
        ForallQuantifier,
        arguments.map(argument => argument.view().pure_symbol),
        [],
        definition,
        span,
      ),
      span,
    ),
  )
}

///|
fn program_pure_variable_occurrences(
  term : @logic.Term,
  target : @logic.VSymbol,
) -> Int {
  let recurse = fn(child) { program_pure_variable_occurrences(child, target) }
  match term.view() {
    Tvar(variable) => if variable == target { 1 } else { 0 }
    Tconst(_) | Ttrue | Tfalse => 0
    Tapp(_, _, arguments) => {
      let mut count = 0
      for argument in arguments {
        count = count + recurse(argument)
      }
      count
    }
    Tif(condition, consequent, alternative) =>
      recurse(condition) + recurse(consequent) + recurse(alternative)
    Tlet(variable, value, body) => {
      let body_count = if variable == target { 0 } else { recurse(body) }
      recurse(value) + body_count
    }
    Tcase(scrutinee, branches) => {
      let mut count = recurse(scrutinee)
      for branch in branches {
        let view = branch.view()
        if !view.pattern.bound_variables().any(variable => variable == target) {
          count = count + recurse(view.body)
        }
      }
      count
    }
    Teps(variable, body) => if variable == target { 0 } else { recurse(body) }
    Tquant(_, binders, triggers, body) =>
      if binders.any(variable => variable == target) {
        0
      } else {
        let mut count = recurse(body)
        for group in triggers {
          for trigger in group {
            count = count + recurse(trigger)
          }
        }
        count
      }
    Tbinop(_, left, right) => recurse(left) + recurse(right)
    Tnot(inner) => recurse(inner)
  }
}

///|
fn program_pure_let_simplified(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  value : @logic.Term,
  body : @logic.Term,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let occurrences = program_pure_variable_occurrences(body, variable)
  if occurrences == 0 {
    return body
  }
  let small_value = match value.view() {
    Tvar(_) | Tconst(_) => true
    _ => false
  }
  if occurrences == 1 || small_value {
    return @logic.TermSubstitution::new()
      .bind(variable, value, span)
      .apply(context, body, span)
  }
  @logic.Term::let_in(variable, value, body, span)
}

///|
fn program_pure_is_equality(symbol : @logic.LSymbol) -> Bool {
  symbol.view().origin
  .attributes()
  .any(attribute => attribute == b"why3:builtin:equality")
}

///|
fn program_pure_is_boolean_constant(term : @logic.Term, value : Bool) -> Bool {
  let expected_name = if value { b"True" } else { b"False" }
  match term.view() {
    Ttrue => value
    Tfalse => !value
    Tapp(symbol, _, arguments) =>
      arguments.is_empty() && symbol.view().name == expected_name
    _ => false
  }
}

///|
fn program_pure_extract_postcondition_formula(
  pure_space : @theory.Namespace,
  result : @logic.VSymbol,
  formula : @logic.Term,
  formula_expected : Bool,
  span : @identity.SourceSpan?,
) -> @logic.Term? raise {
  match formula.view() {
    Tapp(symbol, _, arguments) if program_pure_is_equality(symbol) &&
      arguments.length() == 2 =>
      match arguments[0].view() {
        Tvar(variable) if variable == result &&
          program_pure_variable_occurrences(arguments[1], result) == 0 =>
          Some(
            coerce_program_pure_term(
              pure_space,
              arguments[1],
              formula_expected,
              span,
            ),
          )
        _ => None
      }
    Tbinop(Iff, left, right) =>
      match left.view() {
        Tapp(symbol, _, arguments) if program_pure_is_equality(symbol) &&
          arguments.length() == 2 =>
          match arguments[0].view() {
            Tvar(variable) if variable == result &&
              program_pure_is_boolean_constant(arguments[1], true) &&
              program_pure_variable_occurrences(right, result) == 0 =>
              Some(
                coerce_program_pure_term(
                  pure_space, right, formula_expected, span,
                ),
              )
            _ => None
          }
        _ => None
      }
    Tbinop(And, left, _) =>
      program_pure_extract_postcondition_formula(
        pure_space, result, left, formula_expected, span,
      )
    _ => None
  }
}

///|
fn program_pure_postcondition_term(
  pure_space : @theory.Namespace,
  postcondition : @mlw.Postcondition,
  formula_expected : Bool,
  span : @identity.SourceSpan?,
) -> @logic.Term? raise {
  let postcondition = postcondition.view()
  program_pure_extract_postcondition_formula(
    pure_space,
    postcondition.result,
    postcondition.formula,
    formula_expected,
    span,
  )
}

///|
fn program_expression_pure_term(
  context : @identity.CompilationContext,
  pure_space : @theory.Namespace,
  expression : @mlw.Expr,
  formula_expected : Bool,
  span : @identity.SourceSpan?,
  recursive_logic? : ArrayView[(@mlw.RoutineSymbol, @logic.LSymbol)] = [],
) -> @logic.Term? raise {
  if !expression.effect().is_pure() {
    return None
  }
  let tuple0 = pure_space.find_logic([b"Tuple0"], span)
  let raw : @logic.Term? = if tuple0.view().result_type is Some(unit_type) &&
    expression.ity().to_ty(span) == unit_type {
    Some(@logic.Term::elaborated_apply(tuple0, [], Some(unit_type), None))
  } else {
    match expression.view() {
      Evar(variable) => Some(@logic.Term::variable(variable.view().pure_symbol))
      Econst(constant) =>
        Some(
          @logic.Term::constant(constant, expression.ity().to_ty(span), span),
        )
      Epure(term) => Some(term)
      Eghost(body) | Eexn(_, body) =>
        program_expression_pure_term(
          context,
          pure_space,
          body,
          formula_expected,
          span,
          recursive_logic~,
        )
      Eexec(computation, cty) => {
        let postconditions = cty.view().postconditions
        match computation.view() {
          Capp(routine, _) if recursive_logic.any(entry => entry.0 == routine) =>
            pure_computation_application(
              computation,
              expression.ity(),
              span,
              recursive_logic,
            )
          Cfun(_) =>
            pure_function_computation_term(
              context,
              pure_space,
              computation,
              expression.ity(),
              span,
              recursive_logic,
            )
          _ if !postconditions.is_empty() =>
            program_pure_postcondition_term(
              pure_space,
              postconditions[0],
              formula_expected,
              span,
            )
          _ =>
            pure_computation_application(
              computation,
              expression.ity(),
              span,
              recursive_logic,
            )
        }
      }
      Elet(definition, body) =>
        match definition.view() {
          LDvar(variable, value) =>
            match
              (
                program_expression_pure_term(
                  context,
                  pure_space,
                  value,
                  false,
                  span,
                  recursive_logic~,
                ),
                program_expression_pure_term(
                  context,
                  pure_space,
                  body,
                  formula_expected,
                  span,
                  recursive_logic~,
                ),
              ) {
              (Some(value), Some(body)) =>
                Some(
                  program_pure_let_simplified(
                    context,
                    variable.view().pure_symbol,
                    value,
                    body,
                    span,
                  ),
                )
              _ => None
            }
          LDsym(symbol, _) =>
            match
              program_expression_pure_term(
                context,
                pure_space,
                body,
                formula_expected,
                span,
                recursive_logic~,
              ) {
              None => None
              Some(term) =>
                match symbol.view().logic {
                  RLpv(_) => None
                  RLls(logic) if term.contains_logic_symbol(logic) => None
                  RLnone | RLls(_) | RLlemma => Some(term)
                }
            }
          LDrec(definitions) =>
            match
              program_expression_pure_term(
                context,
                pure_space,
                body,
                formula_expected,
                span,
                recursive_logic~,
              ) {
              None => None
              Some(term) =>
                if definitions.any(definition => {
                    match definition.view().symbol.view().logic {
                      RLpv(_) => true
                      RLls(logic) => term.contains_logic_symbol(logic)
                      RLnone | RLlemma => false
                    }
                  }) {
                  None
                } else {
                  Some(term)
                }
            }
        }
      Eif(condition, consequent, alternative) =>
        match
          (
            program_expression_pure_term(
              context,
              pure_space,
              condition,
              true,
              span,
              recursive_logic~,
            ),
            program_expression_pure_term(
              context,
              pure_space,
              consequent,
              formula_expected,
              span,
              recursive_logic~,
            ),
            program_expression_pure_term(
              context,
              pure_space,
              alternative,
              formula_expected,
              span,
              recursive_logic~,
            ),
          ) {
          (Some(condition), Some(consequent), Some(alternative)) => {
            let term = if program_pure_is_boolean_constant(consequent, false) &&
              program_pure_is_boolean_constant(alternative, true) {
              @logic.Term::not(condition, span)
            } else if formula_expected &&
              program_pure_is_boolean_constant(alternative, false) {
              @logic.Term::binary(And, condition, consequent, span)
            } else if formula_expected &&
              program_pure_is_boolean_constant(consequent, true) {
              @logic.Term::binary(Or, condition, alternative, span)
            } else {
              @logic.Term::if_then_else(
                condition, consequent, alternative, span,
              )
            }
            Some(term)
          }
          _ => None
        }
      Ematch(scrutinee, regular, exceptional) =>
        if !exceptional.is_empty() {
          None
        } else if regular.is_empty() {
          program_expression_pure_term(
            context,
            pure_space,
            scrutinee,
            formula_expected,
            span,
            recursive_logic~,
          )
        } else {
          match
            program_expression_pure_term(
              context,
              pure_space,
              scrutinee,
              false,
              span,
              recursive_logic~,
            ) {
            None => None
            Some(scrutinee) => {
              let branches : Array[(@logic.Pattern, @logic.Term)] = []
              let mut failed = false
              for branch in regular {
                let view = branch.view()
                match
                  program_expression_pure_term(
                    context,
                    pure_space,
                    view.body,
                    formula_expected,
                    span,
                    recursive_logic~,
                  ) {
                  Some(body) =>
                    branches.push((view.pattern.view().pattern, body))
                  None => {
                    failed = true
                    break
                  }
                }
              }
              if failed {
                None
              } else {
                Some(@logic.Term::case(scrutinee, branches, span))
              }
            }
          }
        }
      Eassign(_)
      | Ewhile(_, _, _, _)
      | Efor(_, _, _, _, _)
      | Eraise(_, _)
      | Eassert(_, _)
      | Eabsurd => None
    }
  }
  match raw {
    Some(term) => {
      let term = coerce_program_pure_term(
        pure_space, term, formula_expected, span,
      )
      let attributes = term.attributes().to_owned()
      attributes.push_iter(expression.attributes().iter())
      Some(
        term.source_decorate(
          match term.source_span() {
            Some(location) => Some(location)
            None => expression.origin().source_span()
          },
          attributes,
        ),
      )
    }
    None => None
  }
}

///|
fn decorate_program_post_formula(
  expression : @mlw.Expr,
  formula : @logic.Term,
) -> @logic.Term {
  let attributes = formula.attributes().to_owned()
  attributes.push_iter(expression.attributes().iter())
  formula.source_decorate(
    match formula.source_span() {
      Some(span) => Some(span)
      None => expression.origin().source_span()
    },
    attributes,
  )
}

///|
/// Mirrors the `post_of_expr` fallback used by Why3's
/// `Pdecl.create_let_decl`. Unlike `program_expression_pure_term`, this can
/// recover a logical definition from the postcondition of an executed
/// computation whose result is not itself representable as a pure
/// application.
fn ProgramTyping::program_expression_post_formula(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  result : @logic.Term,
  expression : @mlw.Expr,
  span : @identity.SourceSpan?,
) -> @logic.Term? raise {
  if !expression.effect().is_pure() {
    return None
  }
  let tuple0 = pure_space.find_logic([b"Tuple0"], span)
  if tuple0.view().result_type is Some(unit_type) &&
    expression.ity().to_ty(span) == unit_type {
    return Some(@logic.Term::true_formula())
  }
  let relate = fn(term : @logic.Term) -> @logic.Term raise {
    insert_program_logic_definition(pure_space, result, term, span)
  }
  match expression.view() {
    Evar(variable) =>
      Some(relate(@logic.Term::variable(variable.view().pure_symbol)))
    Econst(constant) =>
      Some(
        relate(
          @logic.Term::constant(constant, expression.ity().to_ty(span), span),
        ),
      )
    Epure(term) => Some(relate(term))
    Eghost(body) | Eexn(_, body) =>
      self.program_expression_post_formula(pure_space, result, body, span)
    Eexec(_, cty) => {
      let result_value = coerce_program_pure_term(
        pure_space, result, false, span,
      )
      let formulas : Array[@logic.Term] = []
      for postcondition in cty.view().postconditions {
        let postcondition = postcondition.view()
        formulas.push(
          @logic.TermSubstitution::new()
          .bind(postcondition.result, result_value, span)
          .apply(self.context, postcondition.formula, span),
        )
      }
      Some(
        decorate_program_post_formula(
          expression,
          conjoin_program_formulas(formulas, span),
        ),
      )
    }
    Elet(definition, body) => {
      guard self.program_expression_post_formula(pure_space, result, body, span)
        is Some(formula) else {
        return None
      }
      let formula = match definition.view() {
        LDvar(variable, value) => {
          let variable_view = variable.view()
          let value_term = if tuple0.view().result_type is Some(unit_type) &&
            variable_view.ity.to_ty(span) == unit_type {
            @logic.Term::elaborated_apply(tuple0, [], Some(unit_type), None)
          } else {
            guard program_expression_pure_term(
                self.context,
                pure_space,
                value,
                false,
                span,
              )
              is Some(value_term) else {
              return None
            }
            value_term
          }
          program_pure_let_simplified(
            self.context,
            variable_view.pure_symbol,
            value_term,
            formula,
            span,
          )
        }
        LDsym(symbol, _) => {
          guard (match symbol.view().logic {
            RLpv(_) => false
            RLls(logic) => !formula.contains_logic_symbol(logic)
            RLnone | RLlemma => true
          }) else {
            return None
          }
          formula
        }
        LDrec(definitions) => {
          guard !definitions.any(definition => {
            match definition.view().symbol.view().logic {
              RLpv(_) => true
              RLls(logic) => formula.contains_logic_symbol(logic)
              RLnone | RLlemma => false
            }
          }) else {
            return None
          }
          formula
        }
      }
      Some(decorate_program_post_formula(expression, formula))
    }
    Eif(condition, consequent, alternative) => {
      guard program_expression_pure_term(
          self.context,
          pure_space,
          condition,
          true,
          span,
        )
        is Some(condition) &&
        self.program_expression_post_formula(
          pure_space, result, consequent, span,
        )
        is Some(consequent) &&
        self.program_expression_post_formula(
          pure_space, result, alternative, span,
        )
        is Some(alternative) else {
        return None
      }
      Some(@logic.Term::if_then_else(condition, consequent, alternative, span))
    }
    Ematch(scrutinee, regular, exceptional) => {
      guard exceptional.is_empty() else { return None }
      if regular.is_empty() {
        return self.program_expression_post_formula(
          pure_space, result, scrutinee, span,
        )
      }
      guard program_expression_pure_term(
          self.context,
          pure_space,
          scrutinee,
          false,
          span,
        )
        is Some(scrutinee) else {
        return None
      }
      let branches : Array[(@logic.Pattern, @logic.Term)] = []
      for branch in regular {
        let branch = branch.view()
        guard self.program_expression_post_formula(
            pure_space,
            result,
            branch.body,
            span,
          )
          is Some(body) else {
          return None
        }
        branches.push((branch.pattern.view().pattern, body))
      }
      Some(@logic.Term::case(scrutinee, branches, span))
    }
    Eabsurd =>
      Some(
        decorate_program_post_formula(expression, @logic.Term::false_formula()),
      )
    Eassign(_)
    | Ewhile(_, _, _, _)
    | Efor(_, _, _, _, _)
    | Eraise(_, _)
    | Eassert(_, _) => None
  }
}

///|
fn ProgramTyping::program_logic_body_definition_axiom(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  ident : @parser.Ident,
  cty : @mlw.Cty,
  logic : @logic.LSymbol,
  body : @mlw.Expr,
) -> @logic.Decl? raise {
  let span = Some(source_span(ident.span))
  let view = cty.view()
  let head = @logic.Term::elaborated_apply(
    logic,
    [
      for argument in view.arguments => {
        @logic.Term::variable(argument.view().pure_symbol)
      }
    ],
    logic.view().result_type,
    None,
  )
  guard self.program_expression_post_formula(pure_space, head, body, span)
    is Some(formula) &&
    !(formula.view() is Ttrue) else {
    return None
  }
  let mut formula = formula
  if !view.oldies.is_empty() {
    let mut oldies = @logic.TermSubstitution::new()
    for oldie in view.oldies {
      let oldie = oldie.view()
      oldies = oldies.bind(
        oldie.snapshot.view().pure_symbol,
        @logic.Term::variable(oldie.original.view().pure_symbol),
        None,
      )
    }
    formula = oldies.apply(self.context, formula, None)
  }
  for precondition in view.preconditions.rev() {
    formula = @logic.Term::binary(Implies, precondition, formula, None)
  }
  let free = formula.free_variables()
  let arguments : Array[@logic.VSymbol] = []
  for argument in view.arguments {
    let variable = argument.view().pure_symbol
    if free.any(item => item == variable) {
      arguments.push(variable)
    }
  }
  if !arguments.is_empty() {
    formula = @logic.Term::quantify(
      ForallQuantifier,
      arguments,
      [],
      formula,
      span,
    )
  }
  let remaining = formula.free_variables()
  remaining.sort_by((left, right) => {
    left.semantic_id().local_id().compare(right.semantic_id().local_id())
  })
  if !remaining.is_empty() {
    formula = @logic.Term::quantify(
      ForallQuantifier,
      remaining,
      [],
      formula,
      span,
    )
  }
  let name = logic.view().name + b"'def"
  let origin = @identity.Origin::user(name, span, [
    b"W:non_conservative_extension:N",
  ])
  Some(
    @logic.Decl::proposition(
      self.context,
      origin,
      Paxiom,
      @logic.PrSymbol::new(self.context, name, origin),
      formula,
      span,
    ),
  )
}

///|
fn ProgramTyping::local_expression_postcondition(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  body : @mlw.Expr,
  result : @mlw.Ity,
) -> @mlw.Postcondition? raise {
  if !body.effect().is_pure() ||
    result == self.unit_ity(pure_space, program_space, None) {
    return None
  }
  let result_type = result.to_ty(None)
  let formula_expected = match result_type.view() {
    TyApp(symbol, _) if symbol.builtin_kind() is Some(BuiltinBoolean) => true
    _ => false
  }
  guard program_expression_pure_term(
      self.context,
      pure_space,
      body,
      formula_expected,
      None,
    )
    is Some(term) else {
    return None
  }
  let formula_span = term.source_span()
  let result_symbol = @logic.VSymbol::new(
    self.context,
    b"result",
    @identity.Origin::user(b"result", None, []),
    result_type,
    None,
  )
  let result_term = @logic.Term::variable(result_symbol)
  let equality = pure_space.find_logic([b"infix ="], formula_span)
  let formula = match term.ty() {
    Some(_) =>
      @logic.Term::elaborated_apply(
        equality,
        [result_term, term],
        None,
        formula_span,
      ).source_decorate(formula_span, [])
    None => {
      let result_is_true = @logic.Term::elaborated_apply(
        equality,
        [result_term, program_boolean_term(pure_space, true, None)],
        None,
        formula_span,
      ).source_decorate(formula_span, [])
      @logic.Term::binary(Iff, result_is_true, term, formula_span).source_decorate(
        formula_span,
        [],
      )
    }
  }
  Some(@mlw.Postcondition::trusted_new(result_symbol, formula, formula_span))
}

///|
fn ProgramTyping::computation_type_for_execution(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  computation : @mlw.Cexp,
  span : @identity.SourceSpan?,
) -> @mlw.Cty raise {
  let cty = computation.cty()
  if !cty.view().postconditions.is_empty() {
    return cty
  }
  match computation.view() {
    Cfun(body) =>
      match
        self.local_expression_postcondition(
          pure_space,
          program_space,
          body,
          cty.view().result,
        ) {
        Some(postcondition) => cty.add_postconditions([postcondition], span)
        None => cty
      }
    Capp(_, _) | Cpur(_, _) | Cany => cty
  }
}

///|
fn routine_logic_postcondition(
  context : @identity.CompilationContext,
  pure_space : @theory.Namespace,
  cty : @mlw.Cty,
  logic : @logic.LSymbol,
  span : @identity.SourceSpan?,
) -> @mlw.Postcondition raise {
  let view = cty.view()
  let result = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", span, [b"mlw:proxy_symbol"]),
    view.result.to_ty(span),
    span,
  )
  let application = @logic.Term::elaborated_apply(
    logic,
    [
      for argument in view.arguments => {
        @logic.Term::variable(argument.view().pure_symbol)
      }
    ],
    logic.view().result_type,
    span,
  )
  let formula = match logic.view().result_type {
    Some(_) =>
      @logic.Term::elaborated_apply(
        pure_space.find_logic([b"infix ="], span),
        [@logic.Term::variable(result), application],
        None,
        span,
      )
    None => {
      let result_is_true = @logic.Term::elaborated_apply(
        pure_space.find_logic([b"infix ="], span),
        [
          @logic.Term::variable(result),
          program_boolean_term(pure_space, true, span),
        ],
        None,
        span,
      )
      @logic.Term::binary(Iff, result_is_true, application, span)
    }
  }
  @mlw.Postcondition::trusted_new(result, formula, span)
}

///|
fn routine_mapping_ity(
  program_space : @mlw.ProgramNamespace,
  cty : @mlw.Cty,
  span : @identity.SourceSpan?,
) -> @mlw.Ity raise {
  let view = cty.view()
  let function_type = program_space.find_type([b"infix ->"], span)
  let mut result = view.result.purify()
  for argument in view.arguments.rev() {
    result = program_function_ity(
      function_type,
      argument.view().ity.purify(),
      result,
      span,
    )
  }
  result
}

///|
fn routine_mapping_postcondition(
  context : @identity.CompilationContext,
  pure_space : @theory.Namespace,
  cty : @mlw.Cty,
  mapping : @mlw.PVariable,
  span : @identity.SourceSpan?,
) -> @mlw.Postcondition raise {
  let view = cty.view()
  let result = @logic.VSymbol::new(
    context,
    b"result",
    @identity.Origin::user(b"result", span, [b"mlw:proxy_symbol"]),
    view.result.to_ty(span),
    span,
  )
  let application = pure_space.find_logic([b"infix @"], span)
  let mut head = @logic.Term::variable(mapping.view().pure_symbol)
  let mut head_type = mapping.view().ity.to_ty(span)
  for argument in view.arguments {
    let next_type = semantic_function_result(head_type, span)
    head = @logic.Term::elaborated_apply(
      application,
      [head, @logic.Term::variable(argument.view().pure_symbol)],
      Some(next_type),
      span,
    )
    head_type = next_type
  }
  let formula = @logic.Term::elaborated_apply(
    pure_space.find_logic([b"infix ="], span),
    [@logic.Term::variable(result), head],
    None,
    span,
  )
  @mlw.Postcondition::trusted_new(result, formula, span)
}

///|
fn ProgramTyping::type_routine(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  outer_scope : ArrayView[(Bytes, ProgramLocal)],
  ident : @parser.Ident,
  ghost : Bool,
  kind : @parser.RoutineKind,
  parameters : ArrayView[ProgramParameterSource],
  return_type : @parser.Pty?,
  return_pattern : @parser.Pattern,
  mask : @parser.Mask,
  spec : @parser.Spec,
  body : @parser.Expr?,
  inferred_result? : @mlw.Ity? = None,
  recursive? : Bool = false,
  preliminary_reads? : ArrayView[@mlw.PVariable] = [],
  reused_signature? : @mlw.Cty? = None,
  abstract_expression_span? : @parser.Span? = None,
) -> TypedRoutine raise {
  let span = Some(source_span(ident.span))
  validate_program_mask(mask, Some(source_span(return_pattern.span)))
  validate_routine_result_pattern(return_pattern)
  validate_program_spec_shape(spec, recursive~)
  let outer_scope = self.visible_program_locals(
    program_space,
    outer_scope,
    ident.span,
  )
  let effective_ghost = self.ghost_context || ghost || kind == RKlemma
  let pending = self.prepare_spec(
    pure_space,
    program_space,
    parameters,
    spec,
    effective_ghost,
    ident.span,
    outer_scope~,
    reused_arguments=reused_signature.map(signature => {
      signature.view().arguments
    }),
  )
  let declared_result = match reused_signature {
    Some(signature) => Some(signature.view().result)
    None =>
      match return_type {
        Some(return_type) =>
          Some(
            self.program_ity(
              pure_space,
              program_space,
              return_type,
              Some(source_span(return_pattern.span)),
            ),
          )
        None =>
          if kind == RKlemma {
            Some(
              self.unit_ity(
                pure_space,
                program_space,
                Some(source_span(return_pattern.span)),
              ),
            )
          } else if kind == RKpred {
            Some(
              self.boolean_ity(
                pure_space,
                program_space,
                Some(source_span(return_pattern.span)),
              ),
            )
          } else if inferred_result is Some(inferred) {
            Some(inferred)
          } else {
            None
          }
      }
  }
  // Declaration ghostness is applied to the exported routine signature by
  // `cty.ghostify` below. The implementation computation keeps the explicit
  // result mask written on the function.
  let result_mask = semantic_program_mask(mask)
  let (pending, declared_result) = self.apply_program_aliases(
    pure_space, program_space, pending, declared_result, return_pattern, result_mask,
  )
  let typed_body = match body {
    None => None
    Some(body) => {
      let saved_values = self.at_values
      let saved_labels = self.at_labels
      let saved_program_variables = self.at_program_variables
      let saved_ghost_context = self.ghost_context
      self.at_values = pending.at_values.copy()
      self.at_labels = pending.at_labels.copy()
      self.at_program_variables = saved_program_variables.copy()
      self.ghost_context = effective_ghost
      for oldie in pending.oldies {
        if !self.at_program_variables.any(existing => {
            existing == oldie.view().snapshot
          }) {
          self.at_program_variables.push(oldie.view().snapshot)
        }
      }
      let typed = self.type_program_expression_expected(
        pure_space,
        program_space,
        pending.parameter_scope,
        body,
        declared_result,
      ) catch {
        error => {
          self.at_values = saved_values
          self.at_labels = saved_labels
          self.at_program_variables = saved_program_variables
          self.ghost_context = saved_ghost_context
          raise error
        }
      }
      self.at_values = saved_values
      self.at_labels = saved_labels
      self.at_program_variables = saved_program_variables
      self.ghost_context = saved_ghost_context
      Some(typed)
    }
  }
  let result = match declared_result {
    Some(result) =>
      match typed_body {
        Some(body) if body.ity() != result => {
          validate_program_ity_skeleton(
            result,
            body.ity(),
            Some(source_span(ident.span)),
            "routine body and declared result have different types",
          )
          body.ity()
        }
        _ => result
      }
    None =>
      match typed_body {
        Some(body) => body.ity()
        None if recursive =>
          @mlw.Ity::variable(
            @logic.TyVarSymbol::new(
              self.context,
              ident.name + b"'result",
              @identity.Origin::user(
                ident.name + b"'result",
                Some(source_span(ident.span)),
                [],
              ),
            ),
          )
        None =>
          fail_invalid_input(
            InvalidDeclaration,
            ProgramTyping,
            Some(source_span(ident.span)),
            "abstract program routine requires an explicit result type",
          )
      }
  }
  let variants = self.type_program_variants(
    pure_space,
    program_space,
    pending.parameter_scope,
    spec.variant,
    ident.span,
  )
  let preconditions = self.type_preconditions(pure_space, pending)
  let postconditions = self.type_postconditions(
    pure_space, program_space, pending, result, result_mask,
  )
  let exceptional_postconditions = self.type_exceptional_postconditions(
    pure_space, program_space, pending,
  )
  let specified_effect = self.specified_effect(
    program_space,
    pending,
    exceptional_postconditions,
    effective_ghost,
    Some(source_span(ident.span)),
  )
  let specified_effect = if recursive && body is None {
    specified_effect.read_pre(preliminary_reads, Some(source_span(ident.span)))
  } else {
    specified_effect
  }
  if typed_body is Some(typed) && typed.ity() != result {
    @logic.fail_type(
      TypeMismatch,
      Some(source_span(ident.span)),
      "routine body and declared result have different types",
    )
  }
  let specification_variables = program_spec_variables(
    pending,
    self.materialized_snapshots(self.at_program_variables),
  )
  let oldies = self.materialized_oldies(pending.oldies)
  let effect = match typed_body {
    Some(body) =>
      if pending.source.check_reads_writes {
        let actual_checked_effect = @mlw.Cty::new_with_variables(
            specification_variables,
            pending.arguments,
            preconditions,
            postconditions,
            exceptional_postconditions,
            oldies,
            body.effect(),
            result,
            Some(source_span(ident.span)),
            mask=result_mask,
          ).view().effect
        let specified_checked_effect = @mlw.Cty::new_with_variables(
            specification_variables,
            pending.arguments,
            preconditions,
            postconditions,
            exceptional_postconditions,
            oldies,
            specified_effect,
            result,
            Some(source_span(ident.span)),
            mask=result_mask,
          ).view().effect
        validate_checked_program_effect(
          actual_checked_effect,
          specified_checked_effect,
          pending.arguments,
          oldies,
          Some(source_span(ident.span)),
        )
        body.effect()
      } else {
        body.effect()
      }
    None => specified_effect
  }
  let mut cty = @mlw.Cty::new_with_variables(
    specification_variables,
    pending.arguments,
    preconditions,
    postconditions,
    exceptional_postconditions,
    oldies,
    effect,
    result,
    Some(source_span(ident.span)),
    mask=result_mask,
    defensive=typed_body is None,
  )
  let origin = user_origin(ident)
  let emitted_kind : @parser.RoutineKind = if recursive && body is None {
    RKnone
  } else {
    kind
  }
  let implementation_cty = cty
  cty = cty.ghostify(effective_ghost, span)
  let mut abstract_pure_constant : (@mlw.Cty, @mlw.Expr)? = None
  let (routine, pure_declarations) = match emitted_kind {
    RKnone => {
      let routine_cty = if cty.view().postconditions.is_empty() &&
        typed_body is Some(body) &&
        self.local_expression_postcondition(
          pure_space, program_space, body, result,
        )
        is Some(postcondition) {
        cty.add_postconditions(
          [postcondition],
          postcondition.view().formula.source_span(),
        )
      } else {
        cty
      }
      (
        @mlw.RoutineSymbol::new_user(
          self.context,
          ident.name,
          origin,
          routine_cty,
          Some(source_span(ident.span)),
        ),
        [],
      )
    }
    RKlocal => {
      let mapping = @mlw.PVariable::trusted_new(
        self.context,
        semantic_name(ident),
        routine_mapping_ity(program_space, cty, span),
        true,
        span,
      )
      cty = cty.add_postconditions_with_variables(
        [mapping],
        [
          routine_mapping_postcondition(
            self.context,
            pure_space,
            cty,
            mapping,
            span,
          ),
        ],
        span,
      )
      (
        @mlw.RoutineSymbol::new_with_logic(
          self.context,
          ident.name,
          origin,
          cty,
          RLpv(mapping),
          None,
          span,
        ),
        [],
      )
    }
    RKfunc | RKpred => {
      if typed_body is None && pending.arguments.is_empty() {
        // Why3 represents an abstract pure constant as a specification-free
        // Cfun whose body executes the source Cany. The source contract stays
        // on that inner computation, while the exported routine signature
        // receives only the generated logical-result postcondition.
        let wrapper_span = match abstract_expression_span {
          Some(expression_span) => Some(source_span(expression_span))
          None => span
        }
        let body = @mlw.Expr::execute(
          @mlw.Cexp::any(implementation_cty),
          @identity.Origin::user(b"", wrapper_span, []),
          [],
          wrapper_span,
        )
        let wrapper = @mlw.Cexp::function_with_specification(
          [],
          [],
          [],
          [],
          [],
          [],
          body,
          wrapper_span,
        )
        let wrapper_cty = wrapper.cty()
        abstract_pure_constant = Some((wrapper_cty, body))
        cty = wrapper_cty.ghostify(effective_ghost, span)
      }
      let argument_types = pending.arguments.map(argument => {
        argument.view().ity.to_ty(Some(source_span(ident.span)))
      })
      let logic = match emitted_kind {
        RKfunc =>
          @logic.LSymbol::new_function(
            self.context,
            ident.name,
            origin,
            argument_types,
            result.to_ty(Some(source_span(ident.span))),
            Some(source_span(ident.span)),
          )
        RKpred =>
          @logic.LSymbol::new_predicate(
            self.context,
            ident.name,
            origin,
            argument_types,
            Some(source_span(ident.span)),
          )
        _ => abort("routine kind changed while building its logical symbol")
      }
      cty = cty.add_postconditions(
        [
          routine_logic_postcondition(
            self.context,
            pure_space,
            cty,
            logic,
            span,
          ),
        ],
        span,
      )
      let logic_definition = match typed_body {
        Some(body) =>
          match
            program_expression_pure_term(
              self.context,
              pure_space,
              body,
              emitted_kind == RKpred,
              span,
            ) {
            Some(body) =>
              Some(
                @logic.LogicDefinition::new(
                  self.context,
                  logic,
                  pending.arguments.map(argument => argument.view().pure_symbol),
                  body,
                  span,
                ),
              )
            None => None
          }
        None => None
      }
      let pure_declarations : Array[@logic.Decl] = []
      match logic_definition {
        Some(definition) if implementation_cty.view().preconditions.is_empty() =>
          pure_declarations.push(
            @logic.Decl::logic(self.context, origin, [definition], span),
          )
        Some(definition) => {
          pure_declarations.push(
            @logic.Decl::parameter(self.context, origin, logic, span),
          )
          match
            self.program_logic_contract_definition_axiom(
              pure_space, ident, implementation_cty, definition,
            ) {
            Some(axiom) => pure_declarations.push(axiom)
            None => ()
          }
        }
        None =>
          pure_declarations.push(
            @logic.Decl::parameter(self.context, origin, logic, span),
          )
      }
      if logic_definition is None &&
        implementation_cty.view().postconditions.is_empty() &&
        typed_body is Some(body) {
        match
          self.program_logic_body_definition_axiom(
            pure_space, ident, implementation_cty, logic, body,
          ) {
          Some(declaration) => pure_declarations.push(declaration)
          None => ()
        }
      }
      if pending.arguments.is_empty() && typed_body is None {
        match
          self.zero_argument_logic_definition_axiom(
            ident, implementation_cty, logic,
          ) {
          Some(declaration) => pure_declarations.push(declaration)
          None => ()
        }
      } else {
        pure_declarations.push_iter(
          self
          .routine_logic_spec_axioms(
            pure_space, ident, implementation_cty, logic,
          )
          .iter(),
        )
      }
      (
        @mlw.RoutineSymbol::new_with_logic(
          self.context,
          ident.name,
          origin,
          cty,
          RLls(logic),
          None,
          Some(source_span(ident.span)),
        ),
        pure_declarations,
      )
    }
    RKlemma =>
      (
        @mlw.RoutineSymbol::new_with_logic(
          self.context,
          ident.name,
          origin,
          cty,
          RLlemma,
          None,
          Some(source_span(ident.span)),
        ),
        self.lemma_pure_declarations(pure_space, ident, cty),
      )
  }
  let (computation, cexp) = match abstract_pure_constant {
    Some((wrapper_cty, wrapper_body)) =>
      (
        @mlw.ProgramComputation::Cfun(wrapper_cty, Some(wrapper_body)),
        @mlw.Cexp::function(
          wrapper_cty,
          wrapper_body,
          Some(source_span(ident.span)),
        ),
      )
    None => {
      let computation = match body {
        None => @mlw.ProgramComputation::Cany(implementation_cty)
        Some(_) => Cfun(implementation_cty, typed_body)
      }
      let cexp = match typed_body {
        Some(body) =>
          @mlw.Cexp::function(
            implementation_cty,
            body,
            Some(source_span(ident.span)),
          )
        None => @mlw.Cexp::any(implementation_cty)
      }
      (computation, cexp)
    }
  }
  { symbol: routine, computation, cexp, variants, pure_declarations }
}

///|
fn ProgramTyping::constrain_inferred_program_argument(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  locals : ArrayView[(Bytes, DLocal)],
  expression : @parser.Expr,
  expected : Dty,
) -> Unit raise {
  let span = Some(source_span(expression.span))
  match expression.desc {
    Eident(Qident(ident)) =>
      match find_local(locals, ident.name) {
        Some(binding) => self.pure.delayed.unify(binding.ty, expected, span)
        None => ()
      }
    Ecast(inner, annotation) => {
      let annotated = self.pure.dty_of_pty(pure_space, annotation)
      self.pure.delayed.unify(annotated, expected, span)
      self.constrain_inferred_program_argument(
        pure_space, locals, inner, annotated,
      )
    }
    Eghost(inner) | Elabel(_, inner) | Eattr(_, inner) =>
      self.constrain_inferred_program_argument(
        pure_space, locals, inner, expected,
      )
    Etuple(arguments) => {
      let components = arguments.map(_ => self.pure.delayed.fresh())
      let tuple = if arguments.is_empty() {
        self.pure.delayed.app(pure_space.find_type([b"unit"], span), [], span)
      } else {
        self.pure.delayed.app(
          pure_space.find_type([tuple_type_name(arguments.length())], span),
          components,
          span,
        )
      }
      self.pure.delayed.unify(tuple, expected, span)
      for index, argument in arguments {
        self.constrain_inferred_program_argument(
          pure_space,
          locals,
          argument,
          components[index],
        )
      }
    }
    _ => ()
  }
}

///|
fn ProgramTyping::infer_direct_program_call_arguments(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, DLocal)],
  path : ArrayView[Bytes],
  arguments : ArrayView[@parser.Expr],
  span : @identity.SourceSpan?,
) -> Unit raise {
  guard program_space.find_routine_candidates(path) is [routine] else { return }
  let formals = routine.view().cty.view().arguments
  if arguments.length() != formals.length() {
    return
  }
  let variables : Map[@logic.TyVarSymbol, Dty] = Map([])
  for index, argument in arguments {
    let expected = self.pure.delayed.specialize(
      formals[index].view().ity.to_ty(span),
      variables,
      span,
    )
    self.constrain_inferred_program_argument(
      pure_space, locals, argument, expected,
    )
  }
}

///|
fn ProgramTyping::infer_program_parameter_calls(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  locals : ArrayView[(Bytes, DLocal)],
  expression : @parser.Expr,
) -> Unit raise {
  let recurse = fn(child) raise {
    self.infer_program_parameter_calls(pure_space, program_space, locals, child)
  }
  match expression.desc {
    Eidapp(path, arguments) => {
      self.infer_direct_program_call_arguments(
        pure_space,
        program_space,
        locals,
        qualid_segments(path),
        arguments,
        Some(source_span(expression.span)),
      )
      for argument in arguments {
        recurse(argument)
      }
    }
    Eapply(_, _) => {
      let reversed : Array[@parser.Expr] = []
      let head = collect_program_application(expression, reversed)
      let arguments = reversed.rev()
      match head.desc {
        Eident(path) =>
          self.infer_direct_program_call_arguments(
            pure_space,
            program_space,
            locals,
            qualid_segments(path),
            arguments,
            Some(source_span(expression.span)),
          )
        Eidapp(path, initial) => {
          let all = initial.copy()
          all.push_iter(arguments.iter())
          self.infer_direct_program_call_arguments(
            pure_space,
            program_space,
            locals,
            qualid_segments(path),
            all,
            Some(source_span(expression.span)),
          )
        }
        _ => ()
      }
      recurse(head)
      for argument in arguments {
        recurse(argument)
      }
    }
    Elet(_, _, _, value, body) => {
      recurse(value)
      recurse(body)
    }
    Erec(definitions, body) => {
      for definition in definitions {
        recurse(definition.body)
      }
      recurse(body)
    }
    Efun(_, _, _, _, _, body) => recurse(body)
    Eany(_, _, _, _, _, _) => ()
    Einfix(left, _, right)
    | Einnfix(left, _, right)
    | Esequence(left, right)
    | Eand(left, right)
    | Eor(left, right) => {
      recurse(left)
      recurse(right)
    }
    Etuple(arguments) =>
      for argument in arguments {
        recurse(argument)
      }
    Erecord(fields) =>
      for field in fields {
        recurse(field.1)
      }
    Eupdate(source, fields) => {
      recurse(source)
      for field in fields {
        recurse(field.1)
      }
    }
    Eassign(assignments) =>
      for assignment in assignments {
        recurse(assignment.target)
        recurse(assignment.value)
      }
    Eif(condition, consequent, alternative) => {
      recurse(condition)
      recurse(consequent)
      recurse(alternative)
    }
    Ewhile(condition, _, _, body) => {
      recurse(condition)
      recurse(body)
    }
    Efor(_, first, _, last, _, body) => {
      recurse(first)
      recurse(last)
      recurse(body)
    }
    Ematch(scrutinee, regular, exceptional) => {
      recurse(scrutinee)
      for branch in regular {
        let pattern = Some(self.pure.type_pattern(pure_space, branch.pattern)) catch {
          _ => None
        }
        match pattern {
          Some(pattern) => {
            self.constrain_inferred_program_argument(
              pure_space,
              locals,
              scrutinee,
              pattern.ty,
            )
            let nested = locals.to_owned()
            nested.push_iter(pattern.bindings.iter())
            self.infer_program_parameter_calls(
              pure_space,
              program_space,
              nested,
              branch.body,
            )
          }
          None => recurse(branch.body)
        }
      }
      for branch in exceptional {
        recurse(branch.body)
      }
    }
    Eraise(_, payload) => if payload is Some(payload) { recurse(payload) }
    Eexn(_, _, _, body)
    | Eoptexn(_, _, body)
    | Eghost(body)
    | Elabel(_, body)
    | Ecast(body, _)
    | Eattr(_, body) => recurse(body)
    Escope(scope, body) =>
      self.infer_program_parameter_calls(
        pure_space.open_scope(qualid_segments(scope), Some(qualid_span(scope))),
        program_space.open_scope(
          qualid_segments(scope),
          Some(qualid_span(scope)),
        ),
        locals,
        body,
      )
    Enot(body) => recurse(body)
    Eref
    | Etrue
    | Efalse
    | Econst(_)
    | Eident(_)
    | Easref(_)
    | Epure(_)
    | Eidpur(_)
    | Eabsurd
    | Eassert(_, _) => ()
  }
}

///|
fn ProgramTyping::contextual_program_parameters(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  outer_scope : ArrayView[(Bytes, ProgramLocal)],
  binders : ArrayView[@parser.Binder],
  return_type : @parser.Pty?,
  spec : @parser.Spec,
  body : @parser.Expr,
  expected : @mlw.Ity?,
  infer_result? : Bool = false,
) -> (Array[ProgramParameterSource], @mlw.Ity?) raise {
  let parameters : Array[ProgramParameterSource] = []
  let delayed_types : Array[Dty] = []
  let inference_scope = [
    for entry in self.program_logic_mappings(program_space, body.span) => {
      (entry.0, entry.1.delayed)
    }
  ]
  inference_scope.push_iter(
    [ for entry in outer_scope => (entry.0, entry.1.delayed) ].iter(),
  )
  let mut remainder = expected
  let mut requires_inference = false
  for binder in binders {
    let inferred_ity = match remainder {
      Some(function_type) => {
        let (parameter, result) = program_function_parts(
          function_type,
          Some(source_span(binder.span)),
        )
        remainder = Some(result)
        Some(parameter)
      }
      None => None
    }
    let delayed = match binder.binder_type {
      Some(annotation) => {
        let delayed = self.pure.dty_of_pty(pure_space, annotation)
        if inferred_ity is Some(inferred) {
          self.pure.delayed.unify(
            delayed,
            self.pure.delayed.known(
              inferred.to_ty(Some(source_span(binder.span))),
              Some(source_span(binder.span)),
            ),
            Some(source_span(binder.span)),
          )
        }
        delayed
      }
      None =>
        match inferred_ity {
          Some(inferred) =>
            self.pure.delayed.known(
              inferred.to_ty(Some(source_span(binder.span))),
              Some(source_span(binder.span)),
            )
          None => {
            requires_inference = true
            self.pure.delayed.fresh()
          }
        }
    }
    delayed_types.push(delayed)
    if binder.ident is Some(ident) {
      inference_scope.push(
        (ident.name, self.pure.make_local(Some(ident), binder.span, delayed)),
      )
    }
    parameters.push({
      span: binder.span,
      ident: binder.ident,
      ghost: binder.ghost,
      ty: binder.binder_type,
      inferred_ity,
    })
  }
  let delayed_result = match return_type {
    Some(annotation) => self.pure.dty_of_pty(pure_space, annotation)
    None =>
      match remainder {
        Some(inferred) =>
          self.pure.delayed.known(
            inferred.to_ty(Some(source_span(body.span))),
            Some(source_span(body.span)),
          )
        None if infer_result && program_expression_provides_unit_result(body) =>
          self.pure.delayed.known(
            @logic.Ty::app(
              pure_space.find_type([b"unit"], Some(source_span(body.span))),
              [],
              Some(source_span(body.span)),
            ),
            Some(source_span(body.span)),
          )
        None => self.pure.delayed.fresh()
      }
  }
  // A recursive body determines its program result type before a contract
  // view of that result does. In particular, machine integers are routinely
  // coerced to mathematical integers in postconditions; using the
  // postcondition's delayed variable directly would incorrectly turn an
  // omitted `int63` result into `int`.
  let contract_result = if infer_result &&
    return_type is None &&
    remainder is None {
    Some(self.pure.delayed.fresh())
  } else {
    None
  }
  let postcondition_result = contract_result.unwrap_or(delayed_result)
  if requires_inference {
    self.infer_program_parameter_calls(
      pure_space, program_space, inference_scope, body,
    )
  }
  for condition in spec.preconditions {
    self.pure.expect_formula(
      pure_space,
      self.pure.type_term(pure_space, inference_scope, condition),
    )
  }
  for postcondition in spec.postconditions {
    for branch in postcondition.branches {
      let pattern = self.pure.type_pattern(pure_space, branch.0)
      self.pure.delayed.unify(
        pattern.ty,
        postcondition_result,
        Some(source_span(branch.0.span)),
      )
      let branch_scope = inference_scope.copy()
      branch_scope.push_iter(pattern.bindings.iter())
      self.pure.expect_formula(
        pure_space,
        self.pure.type_term(pure_space, branch_scope, branch.1),
      )
    }
  }
  // Calls are not the only contexts that constrain an omitted parameter
  // annotation. Record fields, operators, assignments, and control-flow
  // conditions can determine it as well. Reuse the contextual local scanner
  // before generalizing the delayed parameter, while the name still denotes
  // the source binder rather than a rigid generalized type variable.
  for index, parameter in parameters {
    if parameter.ty is None &&
      parameter.inferred_ity is None &&
      parameter.ident is Some(ident) {
      match
        self.local_initializer_expected(
          pure_space,
          program_space,
          outer_scope,
          ident.name,
          body,
        ) {
        Some(inferred) if !program_ity_has_inference_variables(inferred) =>
          self.pure.delayed.unify(
            delayed_types[index],
            self.pure.delayed.known(
              inferred.to_ty(Some(source_span(parameter.span))),
              Some(source_span(parameter.span)),
            ),
            Some(source_span(parameter.span)),
          )
        Some(_) | None => ()
      }
    }
  }
  for index, parameter in parameters {
    if parameter.ty is None && parameter.inferred_ity is None {
      let (ty, _) = self.pure.delayed.generalize(
        delayed_types[index],
        Some(source_span(parameter.span)),
      )
      parameters[index] = {
        ..parameter,
        inferred_ity: Some(
          @mlw.Ity::from_ty(
            program_space,
            ty,
            Some(source_span(parameter.span)),
          ),
        ),
      }
    }
  }
  if infer_result && return_type is None {
    let result_scope = outer_scope.to_owned()
    for parameter in parameters {
      if parameter.ident is Some(ident) {
        let ity = match (parameter.ty, parameter.inferred_ity) {
          (Some(annotation), _) =>
            self.program_ity(
              pure_space,
              program_space,
              annotation,
              Some(source_span(parameter.span)),
            )
          (None, Some(inferred)) => inferred
          (None, None) =>
            abort("recursive result inference lost a parameter type")
        }
        result_scope.push(
          (
            ident.name,
            self.make_program_local(
              Some(ident),
              parameter.span,
              ity,
              parameter.ghost,
            ),
          ),
        )
      }
    }
    self.constrain_inferred_program_result(
      pure_space, program_space, result_scope, body, delayed_result,
    )
    if contract_result is Some(contract_result) {
      let body_resolved = try {
        ignore(
          self.pure.delayed.finalize_pure(
            delayed_result,
            Some(source_span(body.span)),
          ),
        )
        true
      } catch {
        @logic.TypeError(diagnostic) =>
          if diagnostic.kind == UnresolvedTypeVariable {
            false
          } else {
            raise @logic.TypeError(diagnostic)
          }
      }
      if !body_resolved {
        self.pure.delayed.unify(
          delayed_result,
          contract_result,
          Some(source_span(body.span)),
        )
      }
    }
  }
  let inferred_result = match return_type {
    Some(_) => None
    None =>
      match remainder {
        Some(contextual) => Some(contextual)
        None if infer_result => {
          let (ty, _) = self.pure.delayed.generalize(
            delayed_result,
            Some(source_span(body.span)),
          )
          Some(
            @mlw.Ity::from_ty(program_space, ty, Some(source_span(body.span))),
          )
        }
        None => {
          let finalized = Some(
            self.pure.delayed.finalize_pure(
              delayed_result,
              Some(source_span(body.span)),
            ),
          ) catch {
            @logic.TypeError(diagnostic) =>
              if diagnostic.kind == UnresolvedTypeVariable {
                None
              } else {
                raise @logic.TypeError(diagnostic)
              }
          }
          match finalized {
            Some(ty) =>
              Some(
                @mlw.Ity::from_ty(
                  program_space,
                  ty,
                  Some(source_span(body.span)),
                ),
              )
            None => None
          }
        }
      }
  }
  (parameters, inferred_result)
}

///|
fn ProgramTyping::type_routine_expression(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  outer_scope : ArrayView[(Bytes, ProgramLocal)],
  ident : @parser.Ident,
  ghost : Bool,
  kind : @parser.RoutineKind,
  expression : @parser.Expr,
  expected : @mlw.Ity?,
) -> TypedRoutine raise {
  match expression.desc {
    Efun(binders, return_type, return_pattern, mask, spec, body) => {
      let (parameters, inferred_result) = self.contextual_program_parameters(
        pure_space, program_space, outer_scope, binders, return_type, spec, body,
        expected,
      )
      self.type_routine(
        pure_space,
        program_space,
        outer_scope,
        ident,
        ghost,
        kind,
        parameters,
        return_type,
        return_pattern,
        mask,
        spec,
        Some(body),
        inferred_result~,
      )
    }
    Eany(params, inner_kind, return_type, return_pattern, mask, spec) => {
      let parameters = [
        for parameter in params => {
          ProgramParameterSource::{
            span: parameter.span,
            ident: parameter.ident,
            ghost: parameter.ghost,
            ty: Some(parameter.param_type),
            inferred_ity: None,
          }
        }
      ]
      let effective_kind = if inner_kind != RKnone { inner_kind } else { kind }
      self.type_routine(
        pure_space,
        program_space,
        outer_scope,
        ident,
        ghost,
        effective_kind,
        parameters,
        return_type,
        return_pattern,
        mask,
        spec,
        None,
        abstract_expression_span=Some(expression.span),
      )
    }
    _ if kind != RKnone =>
      self.type_routine(
        pure_space,
        program_space,
        outer_scope,
        ident,
        ghost,
        kind,
        [],
        None,
        @parser.Pattern::{ desc: Pwild, span: expression.span },
        MaskVisible,
        @parser.Spec::empty(),
        Some(expression),
      )
    _ =>
      fail_invalid_input(
        InvalidDeclaration,
        ProgramTyping,
        Some(source_span(expression.span)),
        "program declaration is not a let/val routine",
      )
  }
}

///|
fn direct_program_routine_alias(
  program_space : @mlw.ProgramNamespace,
  expression : @parser.Expr,
) -> @mlw.RoutineSymbol? {
  guard expression.desc is Eident(path) else { return None }
  match program_space.find_routine_candidates(qualid_segments(path)) {
    [routine] if !routine.view().cty.view().arguments.is_empty() =>
      Some(routine)
    _ => None
  }
}

///|
fn ProgramTyping::make_program_routine_alias(
  self : ProgramTyping,
  ident : @parser.Ident,
  source : @mlw.RoutineSymbol,
  ghost : Bool,
) -> (@mlw.RoutineSymbol, @mlw.Cexp) raise {
  let span = Some(source_span(ident.span))
  let source_cty = source.view().cty.view()
  let mut substitution = source_cty.freeze
  let remaining_types : Array[@mlw.Ity] = []
  for argument in source_cty.arguments {
    let (next, instantiated) = instantiate_program_expected(
      self.context,
      substitution,
      argument.view().ity,
      span,
    )
    substitution = next
    remaining_types.push(instantiated)
  }
  let (_, result) = instantiate_program_expected(
    self.context,
    substitution,
    source_cty.result,
    span,
  )
  let computation = @mlw.Cexp::call(source, [], remaining_types, result, span)
  let computation = if ghost {
    @mlw.Cexp::trusted_new(
      computation.view(),
      computation.cty().ghostify(true, span),
      span,
    )
  } else {
    computation
  }
  let alias_routine = @mlw.RoutineSymbol::new_user(
    self.context,
    ident.name,
    user_origin(ident),
    computation.cty(),
    span,
  )
  (alias_routine, computation)
}

///|
fn ProgramTyping::type_recursive_routines(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  outer_scope : ArrayView[(Bytes, ProgramLocal)],
  sources : ArrayView[@parser.FunctionDef],
) -> (
  Array[@mlw.RecursiveDefinition],
  @mlw.ProgramNamespace,
  Array[@logic.Decl],
) raise {
  if sources.is_empty() {
    @logic.fail_type(
      InvalidDeclaration,
      None,
      "recursive routine group cannot be empty",
    )
  }
  let outer_scope = self.visible_program_locals(
    program_space,
    outer_scope,
    sources[0].name.span,
  )
  let parameter_sources : Array[Array[ProgramParameterSource]] = []
  let inferred_results : Array[@mlw.Ity?] = []
  for source in sources {
    let (parameters, inferred_result) = self.contextual_program_parameters(
      pure_space,
      program_space,
      outer_scope,
      source.binders,
      source.return_type,
      source.spec,
      source.body,
      None,
      infer_result=true,
    )
    parameter_sources.push(parameters)
    inferred_results.push(inferred_result)
  }
  let unit = self.unit_ity(
    pure_space,
    program_space,
    Some(source_span(sources[0].name.span)),
  )
  let unit_routines : Array[Bytes] = []
  for index, source in sources {
    let returns_unit = source.kind == RKlemma ||
      (match source.return_type {
        Some(return_type) =>
          self.program_ity(
            pure_space,
            program_space,
            return_type,
            Some(source_span(source.return_pattern.span)),
          ) ==
          unit
        None => inferred_results[index] is Some(result) && result == unit
      })
    if returns_unit {
      unit_routines.push(source.name.name)
    }
  }
  let mut changed = true
  while changed {
    changed = false
    for index, source in sources {
      if unit_routines.any(name => name == source.name.name) ||
        source.return_type is Some(_) {
        continue
      }
      guard inferred_results[index] is Some(result) &&
        result.view() is ItyVar(_) else {
        continue
      }
      if program_expression_provides_named_unit_result(
          source.body,
          unit_routines,
        ) {
        inferred_results[index] = Some(unit)
        unit_routines.push(source.name.name)
        changed = true
      }
    }
  }
  let group_names = sources.map(source => source.name.name)
  let group_results : Array[@mlw.Ity?] = []
  for index, source in sources {
    let result = match source.return_type {
      Some(return_type) =>
        Some(
          self.program_ity(
            pure_space,
            program_space,
            return_type,
            Some(source_span(source.return_pattern.span)),
          ),
        )
      None if source.kind == RKlemma => Some(unit)
      None if source.kind == RKpred =>
        Some(
          self.boolean_ity(
            pure_space,
            program_space,
            Some(source_span(source.return_pattern.span)),
          ),
        )
      None => inferred_results[index]
    }
    group_results.push(result)
  }
  changed = true
  while changed {
    changed = false
    for source_index, source in sources {
      let calls : Array[Bytes] = []
      collect_recursive_result_calls(source.body, group_names, calls)
      for call in calls {
        let mut target_index = -1
        for index, name in group_names {
          if name == call {
            target_index = index
            break
          }
        }
        if target_index < 0 {
          continue
        }
        match (group_results[source_index], group_results[target_index]) {
          (Some(source_result), Some(target_result)) if program_result_needs_group_constraint(
              source_result,
            ) &&
            !program_result_needs_group_constraint(target_result) => {
            group_results[source_index] = Some(target_result)
            if sources[source_index].return_type is None {
              inferred_results[source_index] = Some(target_result)
            }
            changed = true
          }
          (Some(source_result), Some(target_result)) if !program_result_needs_group_constraint(
              source_result,
            ) &&
            program_result_needs_group_constraint(target_result) => {
            group_results[target_index] = Some(source_result)
            if sources[target_index].return_type is None {
              inferred_results[target_index] = Some(source_result)
            }
            changed = true
          }
          _ => ()
        }
      }
    }
  }
  let preliminary : Array[TypedRoutine] = []
  let preliminary_reads = program_recursive_preliminary_reads(
    outer_scope, sources,
  )
  let mut preliminary_space = @mlw.ProgramNamespace::empty()
  for source in sources {
    let recursive_space = program_space.overlay(preliminary_space)
    // Why3's first recursive pass creates only provisional signatures. Our
    // richer provisional Cty is useful for checking recursive calls, but any
    // `old` snapshots forced while building it must not escape into the real
    // body pass and perturb identity-ordered effects.
    let saved_snapshot_replacements = self.snapshot_replacements.copy()
    let typed = self.type_routine(
      pure_space,
      recursive_space,
      outer_scope,
      source.name,
      source.ghost,
      source.kind,
      parameter_sources[preliminary.length()],
      source.return_type,
      source.return_pattern,
      source.mask,
      source.spec,
      None,
      inferred_result=inferred_results[preliminary.length()],
      recursive=true,
      preliminary_reads=preliminary_reads[preliminary.length()],
    ) catch {
      error => {
        self.snapshot_replacements = saved_snapshot_replacements
        raise error
      }
    }
    self.snapshot_replacements = saved_snapshot_replacements
    let variant_terms = typed.variants.map(variant => variant.view().term)
    let decrease_name = b"DECR " + source.name.name
    let decrease = @logic.LSymbol::new_predicate(
      self.context,
      decrease_name,
      @identity.Origin::user(decrease_name, None, []),
      variant_terms.map(term => {
        guard term.ty() is Some(ty) else {
          abort("validated recursive variant lost its value type")
        }
        ty
      }),
      None,
    )
    let decrease_precondition = @logic.Term::apply_predicate(
      decrease,
      variant_terms,
      None,
    )
    let internal_symbol = @mlw.RoutineSymbol::new_user(
      self.context,
      typed.symbol.view().name,
      typed.symbol.view().origin,
      typed.symbol.view().cty.add_preconditions([decrease_precondition], None),
      Some(source_span(source.name.span)),
    )
    let typed = { ..typed, symbol: internal_symbol }
    preliminary.push(typed)
    preliminary_space = preliminary_space.add_routine(
      source.name.name,
      typed.symbol,
      Some(source_span(source.name.span)),
    )
  }
  let recursive_space = program_space.overlay(preliminary_space)
  let definitions : Array[@mlw.RecursiveDefinition] = []
  let typed_routines : Array[TypedRoutine] = []
  let mut visible_locals = @mlw.ProgramNamespace::empty()
  for index = 0; index < sources.length(); index = index + 1 {
    let source = sources[index]
    let typed = self.type_routine(
      pure_space,
      recursive_space,
      outer_scope,
      source.name,
      source.ghost,
      source.kind,
      parameter_sources[index],
      source.return_type,
      source.return_pattern,
      source.mask,
      source.spec,
      Some(source.body),
      inferred_result=inferred_results[index],
      recursive=true,
      reused_signature=Some(preliminary[index].symbol.view().cty),
    )
    definitions.push(
      @mlw.RecursiveDefinition::new(
        typed.symbol,
        preliminary[index].symbol,
        typed.cexp,
        typed.variants,
        Some(source_span(source.name.span)),
      ),
    )
    typed_routines.push(typed)
    visible_locals = visible_locals.add_routine(
      source.name.name,
      typed.symbol,
      Some(source_span(source.name.span)),
    )
  }
  // Recursive declarations and local recursive expressions share Why3's
  // `let_rec` effect fixpoint. Stabilize here, before either the top-level
  // declaration is emitted or an enclosing `in` body is typed.
  ignore(
    @mlw.LetDefinition::recursive(
      definitions,
      Some(source_span(sources[0].name.span)),
    ),
  )
  let recursive_logic : Array[(@mlw.RoutineSymbol, @logic.LSymbol)] = []
  for index, typed in typed_routines {
    if typed.symbol.view().logic is RLls(logic) {
      recursive_logic.push((preliminary[index].symbol, logic))
    }
  }
  let abstractions : Array[@logic.Decl] = []
  let logic_definitions : Array[@logic.LogicDefinition] = []
  let logic_definition_sources : Array[@parser.Ident] = []
  let definition_axioms : Array[@logic.Decl] = []
  let axioms : Array[@logic.Decl] = []
  for index, typed in typed_routines {
    let source = sources[index]
    let span = Some(source_span(source.name.span))
    match typed.symbol.view().logic {
      RLls(logic) => {
        let cty = typed.cexp.cty()
        let definition = match typed.cexp.view() {
          Cfun(body) =>
            match
              program_expression_pure_term(
                self.context,
                pure_space,
                body,
                logic.view().result_type is None,
                span,
                recursive_logic~,
              ) {
              Some(term) =>
                Some(
                  @logic.LogicDefinition::recursive(
                    self.context,
                    logic,
                    cty.view().arguments.map(argument => {
                      argument.view().pure_symbol
                    }),
                    term,
                    span,
                  ),
                )
              None => None
            }
          _ => None
        }
        match definition {
          Some(definition) if cty.view().preconditions.is_empty() => {
            logic_definitions.push(definition)
            logic_definition_sources.push(source.name)
          }
          Some(definition) => {
            abstractions.push(
              @logic.Decl::parameter(
                self.context,
                typed.symbol.view().origin,
                logic,
                span,
              ),
            )
            match
              self.program_logic_contract_definition_axiom(
                pure_space,
                source.name,
                cty,
                definition,
              ) {
              Some(axiom) => definition_axioms.push(axiom)
              None => ()
            }
          }
          None =>
            abstractions.push(
              @logic.Decl::parameter(
                self.context,
                typed.symbol.view().origin,
                logic,
                span,
              ),
            )
        }
        axioms.push_iter(
          self
          .routine_logic_spec_axioms(pure_space, source.name, cty, logic)
          .iter(),
        )
      }
      RLnone | RLpv(_) | RLlemma =>
        axioms.push_iter(typed.pure_declarations.iter())
    }
  }
  let pure_declarations = abstractions
  if !logic_definitions.is_empty() {
    let logic_declaration = Some(
      @logic.Decl::logic(
        self.context,
        user_origin(sources[0].name),
        logic_definitions,
        Some(source_span(sources[0].name.span)),
      ),
    ) catch {
      @logic.TypeError(diagnostic) if diagnostic.kind == NoTerminationProof =>
        None
      @logic.TypeError(diagnostic) => raise @logic.TypeError(diagnostic)
    }
    match logic_declaration {
      Some(declaration) => pure_declarations.push(declaration)
      None =>
        for index, definition in logic_definitions {
          let source = logic_definition_sources[index]
          let view = definition.view()
          pure_declarations.push(
            @logic.Decl::parameter(
              self.context,
              view.symbol.view().origin,
              view.symbol,
              Some(source_span(source.span)),
            ),
          )
          definition_axioms.push(
            self.program_logic_definition_axiom(pure_space, source, definition),
          )
        }
    }
  }
  pure_declarations.push_iter(definition_axioms.iter())
  pure_declarations.push_iter(axioms.iter())
  (definitions, program_space.overlay(visible_locals), pure_declarations)
}

///|
fn ProgramTyping::add_top_level_routine(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  ident : @parser.Ident,
  ghost : Bool,
  kind : @parser.RoutineKind,
  expression : @parser.Expr,
) -> Unit raise {
  if kind == RKnone &&
    direct_program_routine_alias(builder.program_namespace(), expression)
    is Some(source) {
    let (symbol, computation) = self.make_program_routine_alias(
      ident, source, ghost,
    )
    builder.add_program_decl(
      symbol,
      @mlw.ProgramComputation::Cexpression(computation),
      [],
      Some(source_span(ident.span)),
    )
    return
  }
  let routine_shaped = match expression.desc {
    Efun(binders, _, _, _, _, _) => !binders.is_empty() || kind != RKnone
    Eany(parameters, _, _, _, _, _) => !parameters.is_empty() || kind != RKnone
    _ => kind != RKnone
  }
  if !routine_shaped {
    let program_space = builder.program_namespace()
    let visible = self.visible_program_locals(program_space, [], ident.span)
    let (value, pure_declarations) = match expression.desc {
      Eany([], _, _, _, _, _) => {
        let typed = self.type_routine_expression(
          builder.pure_namespace(),
          program_space,
          visible,
          ident,
          false,
          kind,
          expression,
          None,
        )
        (
          @mlw.Expr::execute(
            typed.cexp,
            @identity.Origin::user(b"", Some(source_span(expression.span)), []),
            [],
            Some(source_span(expression.span)),
          ),
          typed.pure_declarations,
        )
      }
      _ =>
        (
          self.type_program_expression_expected(
            builder.pure_namespace(),
            program_space,
            visible,
            expression,
            None,
          ),
          [],
        )
    }
    let variable = @mlw.PVariable::trusted_new(
      self.context,
      semantic_name(ident),
      value.ity(),
      ghost || value.mask().is_ghost(),
      Some(source_span(ident.span)),
    )
    builder.add_variable_decl(
      variable,
      value,
      pure_declarations,
      Some(source_span(ident.span)),
    )
    return
  }
  let program_space = builder.program_namespace()
  let visible = self.visible_program_locals(program_space, [], ident.span)
  let typed = self.type_routine_expression(
    builder.pure_namespace(),
    program_space,
    visible,
    ident,
    ghost,
    kind,
    expression,
    None,
  )
  builder.add_program_decl(
    typed.symbol,
    typed.computation,
    typed.pure_declarations,
    Some(source_span(ident.span)),
  )
}

///|
fn resolve_used_module(
  environment : @environment.Environment,
  current_library_path : ArrayView[Bytes],
  file_modules : ArrayView[(Bytes, @mlw.Pmodule)],
  qualid : @parser.QualId,
) -> @mlw.Pmodule raise {
  let key = theory_key_of_qualid(qualid)
  let span = Some(qualid_span(qualid))
  let key_view = key.view()
  if key_view.path.is_empty() {
    for entry in file_modules {
      if entry.0 == key_view.name {
        return entry.1
      }
    }
  }
  match registered_module(environment, key, span) {
    Some(pmodule) => pmodule
    None => {
      let view = key_view
      if view.path.is_empty() && !current_library_path.is_empty() {
        let current_key = @theory.TheoryKey::new(
          current_library_path,
          view.name,
        )
        match registered_module(environment, current_key, span) {
          Some(pmodule) => return pmodule
          None => ()
        }
      }
      let library_path = @env.LibraryPath::new(view.path)
      environment.read_module(library_path, view.name, load_mlw_library, span)
    }
  }
}

///|
priv struct ProgramCloneState {
  context : @identity.CompilationContext
  source_pure : @theory.Theory
  pure_map : @theory.SymbolMap
  explicit_type_symbols : Map[@logic.TypeSymbol, Unit]
  explicit_logic_symbols : Map[@logic.LSymbol, Unit]
  explicit_variables : Map[@mlw.PVariable, Unit]
  explicit_routines : Map[@mlw.RoutineSymbol, Unit]
  explicit_exceptions : Map[@mlw.XSymbol, Unit]
  equality : @logic.LSymbol
  boolean_true : @logic.LSymbol
  function_application : @logic.LSymbol
  target_namespace : @mlw.ProgramNamespace
  local_types : Map[@mlw.ProgramTypeSymbol, @mlw.ProgramTypeDeclaration]
  cloned_types : Map[@mlw.ProgramTypeSymbol, @mlw.ProgramTypeSymbol]
  local_variables : Map[@mlw.PVariable, Unit]
  local_routines : Map[@mlw.RoutineSymbol, Unit]
  module_routines : Map[@mlw.RoutineSymbol, Unit]
  local_exceptions : Map[@mlw.XSymbol, Unit]
  cloned_variables : Map[@mlw.PVariable, @mlw.PVariable]
  cloned_regions : Map[@mlw.Region, @mlw.Region]
  cloned_routines : Map[@mlw.RoutineSymbol, @mlw.RoutineSymbol]
  cloned_exceptions : Map[@mlw.XSymbol, @mlw.XSymbol]
  mut source_theory_item_cursor : Int
  vc_pending_refinements : Array[
    (@mlw.RoutineSymbol, @mlw.ProgramComputation, Int),
  ]
  vc_refinements : Array[(@mlw.RoutineSymbol, @mlw.Cty, @mlw.Expr, Int)]
  vc_suppressed_routines : Array[@mlw.RoutineSymbol]
  vc_suppressed_types : Array[@mlw.ProgramTypeSymbol]
}

///|
fn clone_program_origin_at(
  origin : @identity.Origin,
  span : @identity.SourceSpan?,
) -> @identity.Origin {
  match origin.view() {
    UserOrigin(name, _, attributes) =>
      @identity.Origin::user(name, span, attributes)
    GeneratedOrigin(stage, name, _, attributes) =>
      @identity.Origin::generated(stage, name, span, attributes)
  }
}

///|
fn record_program_clone_routine_origin(
  routine : @mlw.RoutineSymbol,
  span : @identity.SourceSpan?,
  logic_origins : Map[@logic.LSymbol, @identity.Origin],
) -> Unit {
  let view = routine.view()
  if view.logic is RLls(symbol) {
    logic_origins[symbol] = clone_program_origin_at(view.origin, span)
  }
}

///|
fn record_program_clone_spec_origins(
  declaration : @mlw.ProgramDeclaration,
  span : @identity.SourceSpan?,
  proposition_origins : Map[@logic.PrSymbol, @identity.Origin],
) -> Unit {
  for pure in declaration.pure_declarations() {
    if pure.view() is Dprop(_, proposition, _) {
      proposition_origins[proposition] = clone_program_origin_at(
        proposition.view().origin,
        span,
      )
    }
  }
}

///|
fn collect_program_clone_origin_overrides(
  items : ArrayView[@mlw.ModuleItem],
  span : @identity.SourceSpan?,
  logic_origins : Map[@logic.LSymbol, @identity.Origin],
  proposition_origins : Map[@logic.PrSymbol, @identity.Origin],
) -> Unit {
  for item in items {
    match item {
      Udecl(declaration) =>
        match declaration {
          PDlet(routine, _, _, _) => {
            record_program_clone_routine_origin(routine, span, logic_origins)
            record_program_clone_spec_origins(
              declaration, span, proposition_origins,
            )
          }
          PDrec(definitions, _, _) => {
            for definition in definitions {
              let view = definition.view()
              record_program_clone_routine_origin(
                view.symbol,
                span,
                logic_origins,
              )
              record_program_clone_routine_origin(
                view.internal_symbol,
                span,
                logic_origins,
              )
            }
            record_program_clone_spec_origins(
              declaration, span, proposition_origins,
            )
          }
          PDtype(_, pure, _) =>
            // Program type declarations rebuild their invariant axioms while
            // cloning, so Why3 keeps them as axioms instead of applying the
            // clone's default proposition kind.  Retain the source origin
            // because `clone_type_decl` also preserves the original location.
            for pure_declaration in pure {
              if pure_declaration.view() is Dprop(_, proposition, _) {
                proposition_origins[proposition] = proposition.view().origin
              }
            }
          PDpure(_, _) | PDvar(_, _, _, _) | PDexn(_, _, _) => ()
        }
      Uscope(_, nested) =>
        collect_program_clone_origin_overrides(
          nested, span, logic_origins, proposition_origins,
        )
      Uuse(_) | Uclone(_) | Umeta(_) => ()
    }
  }
}

///|
fn collect_omitted_program_clone_propositions(
  items : ArrayView[@mlw.ModuleItem],
  instantiated_routines : Map[@mlw.RoutineSymbol, @mlw.RoutineSymbol],
  output : Map[@logic.PrSymbol, Unit],
) -> Unit {
  for item in items {
    match item {
      Udecl(PDlet(routine, _, pure, _)) =>
        if instantiated_routines.contains(routine) {
          for declaration in pure {
            if declaration.view() is Dprop(_, proposition, _) {
              output[proposition] = ()
            }
          }
        }
      Uscope(_, nested) =>
        collect_omitted_program_clone_propositions(
          nested, instantiated_routines, output,
        )
      Udecl(PDtype(_, _, _))
      | Udecl(PDpure(_, _))
      | Udecl(PDvar(_, _, _, _))
      | Udecl(PDrec(_, _, _))
      | Udecl(PDexn(_, _, _))
      | Uuse(_)
      | Uclone(_)
      | Umeta(_) => ()
    }
  }
}

///|
fn program_clone_fallback_definition_propositions(
  declarations : ArrayView[@logic.Decl],
  symbol : @logic.LSymbol,
) -> Array[@logic.PrSymbol] {
  let expected_name = symbol.view().name + b"'def"
  [
    for declaration in declarations if declaration.view()
    is Dprop(Paxiom, proposition, _) &&
    proposition.view().name == expected_name => proposition
  ]
}

///|
fn program_clone_has_fallback_parameter(
  declarations : ArrayView[@logic.Decl],
  symbol : @logic.LSymbol,
) -> Bool {
  declarations.any(declaration => {
    declaration.view() is Dparam(parameter) && parameter == symbol
  })
}

///|
fn ProgramTyping::collect_program_clone_logic_definition_overrides(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  items : ArrayView[@mlw.ModuleItem],
  output : Array[(Array[@logic.LogicDefinition], Array[@logic.PrSymbol])],
) -> Unit raise {
  for item in items {
    match item {
      Udecl(PDrec(definitions, pure, _)) => {
        let recursive_logic : Array[(@mlw.RoutineSymbol, @logic.LSymbol)] = []
        for definition in definitions {
          let view = definition.view()
          if view.symbol.view().logic is RLls(logic) {
            recursive_logic.push((view.internal_symbol, logic))
          }
        }
        let logical : Array[@logic.LogicDefinition] = []
        let propositions : Array[@logic.PrSymbol] = []
        for definition in definitions {
          let view = definition.view()
          guard view.symbol.view().logic is RLls(logic) &&
            view.function_.view() is Cfun(body) &&
            view.function_.cty().view().preconditions.is_empty() &&
            program_clone_has_fallback_parameter(pure, logic) else {
            continue
          }
          let span = view.symbol.view().origin.identifier_source_span()
          match
            program_expression_pure_term(
              self.context,
              pure_space,
              body,
              logic.view().result_type is None,
              span,
              recursive_logic~,
            ) {
            Some(term) => {
              let fallback = program_clone_fallback_definition_propositions(
                pure, logic,
              )
              if !fallback.is_empty() {
                logical.push(
                  @logic.LogicDefinition::recursive(
                    self.context,
                    logic,
                    view.function_.cty().view().arguments.map(argument => {
                      argument.view().pure_symbol
                    }),
                    term,
                    span,
                  ),
                )
                propositions.push_iter(fallback.iter())
              }
            }
            None => ()
          }
        }
        if !logical.is_empty() {
          output.push((logical, propositions))
        }
      }
      Uscope(_, nested) =>
        self.collect_program_clone_logic_definition_overrides(
          pure_space, nested, output,
        )
      Udecl(PDlet(_, _, _, _))
      | Udecl(PDtype(_, _, _))
      | Udecl(PDpure(_, _))
      | Udecl(PDvar(_, _, _, _))
      | Udecl(PDexn(_, _, _))
      | Uuse(_)
      | Uclone(_)
      | Umeta(_) => ()
    }
  }
}

///|
fn collect_local_program_symbols(
  items : ArrayView[@mlw.ModuleItem],
  types : Map[@mlw.ProgramTypeSymbol, @mlw.ProgramTypeDeclaration],
  propositions : Map[@logic.PrSymbol, Unit],
  variables : Map[@mlw.PVariable, Unit],
  routines : Map[@mlw.RoutineSymbol, Unit],
  internal_routines : Map[@mlw.RoutineSymbol, Unit],
  exceptions : Map[@mlw.XSymbol, Unit],
) -> Unit {
  for item in items {
    match item {
      Udecl(declaration) =>
        match declaration {
          PDtype(declarations, _, _) =>
            for declaration in declarations {
              let view = declaration.view()
              types[view.symbol] = declaration
              for routine in view.fields {
                routines[routine] = ()
              }
              for routine in view.constructors {
                routines[routine] = ()
              }
            }
          PDpure(declarations, _) =>
            for pure in declarations {
              if pure.view() is Dprop(_, proposition, _) {
                propositions[proposition] = ()
              }
            }
          PDlet(routine, _, _, _) => routines[routine] = ()
          PDvar(variable, _, _, _) => variables[variable] = ()
          PDrec(definitions, _, _) =>
            for definition in definitions {
              let view = definition.view()
              routines[view.symbol] = ()
              routines[view.internal_symbol] = ()
              internal_routines[view.internal_symbol] = ()
            }
          PDexn(exception, _, _) => exceptions[exception] = ()
        }
      Uclone(witness) => {
        let view = witness.view()
        for entry in view.program_variable_instantiations {
          variables[entry.1] = ()
        }
        for entry in view.proposition_instantiations {
          propositions[entry.1] = ()
        }
        for entry in view.routine_instantiations {
          routines[entry.1] = ()
        }
        for entry in view.exception_instantiations {
          exceptions[entry.1] = ()
        }
      }
      Uscope(_, nested) =>
        collect_local_program_symbols(
          nested, types, propositions, variables, routines, internal_routines, exceptions,
        )
      Uuse(_) | Umeta(_) => ()
    }
  }
}

///|
fn program_type_field_named(
  symbol : @mlw.ProgramTypeSymbol,
  name : BytesView,
) -> (@mlw.PVariable, Bool)? {
  let view = symbol.view()
  for field in view.mutable_fields {
    if field.view().name.view().name[:] == name {
      return Some((field, true))
    }
  }
  for field in view.immutable_fields {
    if field.view().name.view().name[:] == name {
      return Some((field, false))
    }
  }
  None
}

///|
fn add_program_clone_logic_instance(
  instances : Array[(@logic.LSymbol, @logic.LSymbol)],
  source : @logic.LSymbol,
  target : @logic.LSymbol,
  span : @identity.SourceSpan?,
) -> Unit raise {
  for existing in instances {
    if existing.0 == source {
      if existing.1 != target {
        fail_invalid_input(
          InvalidDeclaration,
          ProgramTyping,
          span,
          "a logical program symbol has conflicting clone targets",
        )
      }
      return
    }
  }
  instances.push((source, target))
}

///|
fn preseed_program_record_refinement(
  source : @mlw.ProgramTypeDeclaration,
  target : @mlw.ProgramTypeSymbol,
  target_namespace : @mlw.ProgramNamespace,
  cloned_variables : Map[@mlw.PVariable, @mlw.PVariable],
  cloned_routines : Map[@mlw.RoutineSymbol, @mlw.RoutineSymbol],
  pure_logic_instances : Array[(@logic.LSymbol, @logic.LSymbol)],
  span : @identity.SourceSpan?,
) -> Unit raise {
  let source_symbol = source.view().symbol
  let source_symbol_view = source_symbol.view()
  let target_view = target.view()
  if source_symbol_view.flags.mutable_ != target_view.flags.mutable_ {
    fail_invalid_input(
      InvalidDeclaration,
      ProgramTyping,
      span,
      "a cloned record type must preserve mutability",
    )
  }
  for source_routine in source.view().fields {
    guard source_routine.view().field is Some(source_field) else {
      fail_invalid_input(
        InvalidDeclaration,
        ProgramTyping,
        span,
        "a cloned record projection has no program field",
      )
    }
    let source_field_view = source_field.view()
    let source_mutable = source_symbol_view.mutable_fields.any(field => {
      field == source_field
    })
    guard program_type_field_named(target, source_field_view.name.view().name)
      is Some((target_field, target_mutable)) else {
      fail_invalid_input(
        InvalidDeclaration,
        ProgramTyping,
        span,
        "a cloned record target is missing field '\{source_field_view.name.view().name}'",
      )
    }
    if source_mutable != target_mutable {
      fail_invalid_input(
        InvalidDeclaration,
        ProgramTyping,
        span,
        "a cloned record field must preserve mutability",
      )
    }
    if !source_field_view.ghost && target_field.view().ghost {
      fail_invalid_input(
        InvalidDeclaration,
        ProgramTyping,
        span,
        "a visible cloned record field cannot target a ghost field",
      )
    }
    let target_routine = target_namespace.find_projection_by_field(
      target_field, span,
    )
    cloned_variables[source_field] = target_field
    cloned_routines[source_routine] = target_routine
    match (source_routine.view().logic, target_routine.view().logic) {
      (RLls(source_logic), RLls(target_logic)) =>
        add_program_clone_logic_instance(
          pure_logic_instances, source_logic, target_logic, span,
        )
      _ =>
        fail_invalid_input(
          InvalidDeclaration,
          ProgramTyping,
          span,
          "record projections require logical clone targets",
        )
    }
  }
}

///|
fn ProgramCloneState::program_space(
  self : ProgramCloneState,
) -> @mlw.ProgramNamespace raise {
  let mut cloned = @mlw.ProgramNamespace::empty()
  for _, symbol in self.cloned_types {
    // This namespace is used only for semantic lookup by the underlying
    // logical type identity. Cloned modules commonly contain many scoped
    // types named `t`; flattening those names here creates a spurious clash.
    // A context-local semantic id is unique and keeps every counterpart
    // available to `find_type_by_logic` without changing source lookup.
    let key = b"clone-type-\{symbol.semantic_id().local_id()}"
    cloned = cloned.add_type(key, symbol, None)
  }
  self.target_namespace.overlay(cloned)
}

///|
fn ProgramCloneState::program_symbol(
  self : ProgramCloneState,
  source : @mlw.ProgramTypeSymbol,
  span : @identity.SourceSpan?,
) -> @mlw.ProgramTypeSymbol raise {
  match self.cloned_types.get(source) {
    Some(target) => return target
    None => ()
  }
  let source_logic = source.view().logic_type
  match self.pure_map.find_type_symbol(source_logic) {
    Some(target_logic) =>
      if self.explicit_type_symbols.contains(source_logic) {
        let target = self.target_namespace.find_type_by_logic(
          target_logic, span,
        )
        self.cloned_types[source] = target
        target
      } else {
        match self.clone_type(source, span) {
          Some(target) => target
          None =>
            @logic.fail_type(
              InvalidDeclaration,
              span,
              "cloned program type unexpectedly has no target symbol",
            )
        }
      }
    None => source
  }
}

///|
fn ProgramCloneState::clone_ity(
  self : ProgramCloneState,
  source : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> @mlw.Ity raise {
  match source.view() {
    ItyVar(variable) => @mlw.Ity::variable(variable)
    ItyApp(symbol, arguments, regions) => {
      if self.pure_map.find_type(symbol.view().logic_type) is Some(_) {
        return @mlw.Ity::from_ty(
          self.program_space(),
          self.pure_map.translate_type(self.context, source.to_ty(span), span),
          span,
        )
      }
      let target = self.program_symbol(symbol, span)
      let arguments = arguments.map(argument => self.clone_ity(argument, span))
      let regions = regions.map(region => self.clone_ity(region, span))
      // Refining an abstract program type may introduce additional hidden
      // regions in the target representation. A pure source application does
      // not expose any of its region identities, so instantiate the target
      // representation freshly and immediately snapshot it. This mirrors
      // Why3's `ity_app_pure` clone path and avoids forcing the source and
      // target record representations to have the same region arity.
      if self.explicit_type_symbols.contains(symbol.view().logic_type) &&
        regions.all(@mlw.Ity::is_pure) {
        return @mlw.Ity::instantiate(target, arguments, [], span).purify()
      }
      // An explicit clone substitution may map an abstract source type to a
      // named program alias. Ordinary program typing unfolds that alias
      // through `Ity::instantiate`; preserving it here would leave cloned
      // routine formals as `alias` while callers have the equivalent expanded
      // type, causing routine lookup to fall back to the pure symbol.
      match target.view().definition {
        ProgramAlias(_) =>
          @mlw.Ity::instantiate(target, arguments, regions, span)
        ProgramNoDef | ProgramRange(_, _) | ProgramFloat(_, _) =>
          @mlw.Ity::app_with_regions(target, arguments, regions, span)
      }
    }
    ItyReg(region) => @mlw.Ity::region(self.clone_region(region, span))
  }
}

///|
fn ProgramCloneState::clone_region(
  self : ProgramCloneState,
  source : @mlw.Region,
  span : @identity.SourceSpan?,
) -> @mlw.Region raise {
  match self.cloned_regions.get(source) {
    Some(target) => return target
    None => ()
  }
  let view = source.view()
  let target = @mlw.Region::instantiate(
    self.context,
    view.name,
    self.program_symbol(view.symbol, span),
    view.arguments.map(argument => self.clone_ity(argument, span)),
    view.regions.map(region => self.clone_ity(region, span)),
    span,
    inference=view.inference,
  )
  self.cloned_regions[source] = target
  target
}

///|
fn ProgramCloneState::seed_ity_region_mapping(
  self : ProgramCloneState,
  source : @mlw.Ity,
  representative : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> Unit raise {
  match (source.view(), representative.view()) {
    (ItyVar(_), ItyVar(_)) => ()
    (
      ItyApp(_, source_arguments, source_regions),
      ItyApp(_, representative_arguments, representative_regions),
    ) => {
      if source_arguments.length() != representative_arguments.length() ||
        source_regions.length() != representative_regions.length() {
        @logic.fail_type(
          InvalidDeclaration,
          span,
          "recursive routine symbols disagree on a parameter type's region shape",
        )
      }
      for index, argument in source_arguments {
        self.seed_ity_region_mapping(
          argument,
          representative_arguments[index],
          span,
        )
      }
      for index, region in source_regions {
        self.seed_ity_region_mapping(
          region,
          representative_regions[index],
          span,
        )
      }
    }
    (ItyReg(source_region), ItyReg(representative_region)) => {
      let target_region = match self.cloned_regions.get(representative_region) {
        Some(target) => target
        None => self.clone_region(representative_region, span)
      }
      match self.cloned_regions.get(source_region) {
        Some(existing) if existing != target_region =>
          @logic.fail_type(
            InvalidDeclaration,
            span,
            "recursive clone produced conflicting region identities",
          )
        Some(_) => ()
        None => self.cloned_regions[source_region] = target_region
      }
      let source_view = source_region.view()
      let representative_view = representative_region.view()
      if source_view.arguments.length() !=
        representative_view.arguments.length() ||
        source_view.regions.length() != representative_view.regions.length() {
        @logic.fail_type(
          InvalidDeclaration,
          span,
          "recursive routine symbols disagree on a parameter region's shape",
        )
      }
      for index, argument in source_view.arguments {
        self.seed_ity_region_mapping(
          argument,
          representative_view.arguments[index],
          span,
        )
      }
      for index, region in source_view.regions {
        self.seed_ity_region_mapping(
          region,
          representative_view.regions[index],
          span,
        )
      }
    }
    _ =>
      @logic.fail_type(
        InvalidDeclaration,
        span,
        "recursive routine symbols disagree on a parameter type's mutability",
      )
  }
}

///|
fn ProgramCloneState::clone_variable(
  self : ProgramCloneState,
  source : @mlw.PVariable,
  span : @identity.SourceSpan?,
) -> @mlw.PVariable raise {
  match self.cloned_variables.get(source) {
    Some(target) => return target
    None => ()
  }
  for source_type, _ in self.local_types {
    if !self.explicit_type_symbols.contains(source_type.view().logic_type) {
      continue
    }
    let source_view = source_type.view()
    let target = self.program_symbol(source_type, span)
    let target_view = target.view()
    for index, field in source_view.mutable_fields {
      if field == source {
        if index >= target_view.mutable_fields.length() {
          @logic.fail_type(
            InvalidDeclaration,
            span,
            "cloned record type has fewer mutable fields than its source",
          )
        }
        let target = target_view.mutable_fields[index]
        self.cloned_variables[source] = target
        return target
      }
    }
    for index, field in source_view.immutable_fields {
      if field == source {
        if index >= target_view.immutable_fields.length() {
          @logic.fail_type(
            InvalidDeclaration,
            span,
            "cloned record type has fewer immutable fields than its source",
          )
        }
        let target = target_view.immutable_fields[index]
        self.cloned_variables[source] = target
        return target
      }
    }
  }
  let view = source.view()
  let target = @mlw.PVariable::trusted_new(
    self.context,
    view.name,
    self.clone_ity(view.ity, span),
    view.ghost,
    span,
  )
  self.cloned_variables[source] = target
  target
}

///|
fn ProgramCloneState::clone_effect_field(
  self : ProgramCloneState,
  source : @mlw.PVariable,
  span : @identity.SourceSpan?,
) -> @mlw.PVariable raise {
  for symbol, _ in self.local_types {
    let view = symbol.view()
    if view.mutable_fields.any(field => field == source) ||
      view.immutable_fields.any(field => field == source) {
      return self.clone_variable(source, span)
    }
  }
  // Fields owned by a used module keep their canonical identity. In
  // particular, cloning a write through `ref` must still name the exact
  // mutable field stored on the imported reference type symbol.
  source
}

///|
fn ProgramCloneState::logic_variable_instantiations(
  self : ProgramCloneState,
) -> Array[(@logic.VSymbol, @logic.VSymbol)] {
  [
    for source, target in self.cloned_variables => {
      (source.view().pure_symbol, target.view().pure_symbol)
    }
  ]
}

///|
fn ProgramCloneState::clone_type(
  self : ProgramCloneState,
  source : @mlw.ProgramTypeSymbol,
  span : @identity.SourceSpan?,
) -> @mlw.ProgramTypeSymbol? raise {
  let source_view = source.view()
  let source_logic = source_view.logic_type
  if self.pure_map.find_type(source_logic) is Some(_) {
    return None
  }
  match self.pure_map.find_type_symbol(source_logic) {
    None => Some(source)
    Some(target_logic) => {
      match self.cloned_types.get(source) {
        Some(target) =>
          if self.explicit_type_symbols.contains(source_logic) {
            return None
          } else {
            return Some(target)
          }
        None => ()
      }
      let target = if self.explicit_type_symbols.contains(source_logic) {
        self.target_namespace.find_type_by_logic(target_logic, span)
      } else {
        let mutable_fields = source_view.mutable_fields.map(field => {
          self.clone_variable(field, span)
        })
        let immutable_fields = source_view.immutable_fields.map(field => {
          self.clone_variable(field, span)
        })
        let invariants = match self.local_types.get(source) {
          Some(declaration) =>
            declaration.view().invariants.map(invariant => {
              self.pure_map.translate_term(
                self.context,
                invariant,
                self.logic_variable_instantiations(),
                span,
              )
            })
          None => []
        }
        match source_view.definition {
          ProgramNoDef =>
            if !mutable_fields.is_empty() ||
              !immutable_fields.is_empty() ||
              !invariants.is_empty() ||
              source_view.flags.nonfree ||
              source_view.flags.private_ ||
              source_view.flags.mutable_ {
              @mlw.ProgramTypeSymbol::new_record(
                self.context,
                target_logic,
                source_view.origin,
                source_view.flags.private_,
                source_view.flags.mutable_,
                mutable_fields,
                immutable_fields,
                invariants,
                span,
              )
            } else {
              @mlw.ProgramTypeSymbol::new(
                self.context,
                target_logic,
                source_view.origin,
                source_view.flags,
                @mlw.ProgramNoDef,
                [],
                [],
                span,
              )
            }
          ProgramRange(lower, upper) =>
            @mlw.ProgramTypeSymbol::new_range(
              self.context,
              target_logic,
              source_view.origin,
              lower,
              upper,
              span,
            )
          ProgramFloat(exponent_digits, significand_digits) =>
            @mlw.ProgramTypeSymbol::new_float(
              self.context,
              target_logic,
              source_view.origin,
              exponent_digits,
              significand_digits,
              span,
            )
          ProgramAlias(target) =>
            @mlw.ProgramTypeSymbol::new_alias(
              self.context,
              target_logic,
              source_view.origin,
              self.clone_ity(target, span),
              span,
            )
        }
      }
      self.cloned_types[source] = target
      if self.explicit_type_symbols.contains(source_logic) {
        None
      } else {
        Some(target)
      }
    }
  }
}

///|
fn ProgramCloneState::clone_exception(
  self : ProgramCloneState,
  source : @mlw.XSymbol,
  span : @identity.SourceSpan?,
) -> @mlw.XSymbol raise {
  match self.cloned_exceptions.get(source) {
    Some(target) => return target
    None => ()
  }
  let view = source.view()
  let target = @mlw.XSymbol::new(
    self.context,
    view.name,
    self.clone_ity(view.ity, span),
    span,
    mask=view.mask,
  )
  self.cloned_exceptions[source] = target
  target
}

///|
fn ProgramCloneState::clone_postconditions(
  self : ProgramCloneState,
  source : ArrayView[@mlw.Postcondition],
  variables : ArrayView[(@logic.VSymbol, @logic.VSymbol)],
  span : @identity.SourceSpan?,
) -> Array[@mlw.Postcondition] raise {
  [
    for postcondition in source => {
      let view = postcondition.view()
      let result_view = view.result.view()
      let result = @logic.VSymbol::new(
        self.context,
        result_view.name,
        result_view.origin,
        self.pure_map.translate_type(self.context, result_view.ty, span),
        span,
      )
      @mlw.Postcondition::trusted_new(
        result,
        self.pure_map.translate_term(
          self.context,
          view.formula,
          variables.to_owned() + [(view.result, result)],
          span,
        ),
        span,
      )
    }
  ]
}

///|
fn ProgramCloneState::clone_effect(
  self : ProgramCloneState,
  source : @mlw.Effect,
  anchor : @identity.SemanticId,
  spoils : ArrayView[@logic.TyVarSymbol],
  span : @identity.SourceSpan?,
  preserve_ghost? : Bool = true,
) -> @mlw.Effect raise {
  let view = source.view()
  let writes = [
    for write in view.writes => {
      let write = write.view()
      @mlw.EffectWrite::new(
        self.clone_region(write.region, span),
        write.fields.map(field => self.clone_effect_field(field, span)),
        span,
      )
    }
  ]
  let raises = view.raises.map(exception => {
    self.clone_exception(exception, span)
  })
  @mlw.Effect::trusted_new(
    anchor,
    view.reads.map(variable => self.clone_variable(variable, span)),
    writes,
    view.taints.map(region => self.clone_region(region, span)),
    view.covers.map(region => self.clone_region(region, span)),
    view.resets.map(region => self.clone_region(region, span)),
    raises,
    spoils,
    view.termination,
    preserve_ghost && view.ghost,
    span,
  )
}

///|
fn retain_escaping_effect_spoils(
  effect : @mlw.Effect,
  result : @mlw.Ity,
  span : @identity.SourceSpan?,
) -> @mlw.Effect raise {
  let view = effect.view()
  let escaping = result.reachable_type_variables()
  for exception in view.raises {
    append_clone_effect_spoils(
      escaping,
      exception.view().ity.reachable_type_variables(),
    )
  }
  for write in view.writes {
    let write = write.view()
    for field in write.fields {
      append_clone_effect_spoils(
        escaping,
        write.region.member_ity(field, span).reachable_type_variables(),
      )
    }
  }
  let spoils : Array[@logic.TyVarSymbol] = []
  for variable in view.spoils {
    if escaping.any(escaped => escaped == variable) {
      spoils.push(variable)
    }
  }
  @mlw.Effect::trusted_new(
    result.context_anchor(),
    view.reads,
    view.writes,
    view.taints,
    view.covers,
    view.resets,
    view.raises,
    spoils,
    view.termination,
    view.ghost,
    span,
  )
}

///|
fn ProgramCloneState::clone_cty(
  self : ProgramCloneState,
  source : @mlw.Cty,
  span : @identity.SourceSpan?,
  drop_decrease? : Bool = false,
  preserve_effect_ghost? : Bool = true,
) -> @mlw.Cty raise {
  let view = source.view()
  let program_variables = view.program_variables.map(variable => {
    self.clone_variable(variable, span)
  })
  let arguments = view.arguments.map(argument => {
    self.clone_variable(argument, span)
  })
  let result = self.clone_ity(view.result, span)
  let variables = self.logic_variable_instantiations()
  let source_preconditions = if drop_decrease {
    if view.preconditions.is_empty() {
      []
    } else {
      view.preconditions[1:].to_owned()
    }
  } else {
    view.preconditions.to_owned()
  }
  let preconditions = source_preconditions.map(precondition => {
    self.pure_map.translate_term(self.context, precondition, variables, span)
  })
  let postconditions = self.clone_postconditions(
    view.postconditions,
    variables,
    span,
  )
  let exceptional : Array[@mlw.ExceptionalPostconditions] = []
  for entry in view.exceptional_postconditions {
    let entry = entry.view()
    exceptional.push(
      @mlw.ExceptionalPostconditions::new(
        self.clone_exception(entry.exception, span),
        self.clone_postconditions(entry.postconditions, variables, span),
        span,
      ),
    )
  }
  let oldies = [
    for oldie in view.oldies => {
      let oldie = oldie.view()
      @mlw.OldSnapshot::new(
        self.clone_variable(oldie.snapshot, span),
        self.clone_variable(oldie.original, span),
        span,
      )
    }
  ]
  let effect = retain_escaping_effect_spoils(
    self.clone_effect(
      view.effect,
      result.context_anchor(),
      view.effect.view().spoils,
      span,
      preserve_ghost=preserve_effect_ghost,
    ),
    result,
    span,
  )
  let mut freeze = @mlw.ItySubstitution::empty()
  let freeze_view = view.freeze.view()
  for entry in freeze_view.type_variables {
    freeze = freeze.match_ity(
      @mlw.Ity::variable(entry.0),
      self.clone_ity(entry.1, span),
      span,
    )
  }
  for entry in freeze_view.regions {
    freeze = freeze.match_region(
      self.clone_region(entry.0, span),
      self.clone_ity(entry.1, span),
      span,
    )
  }
  @mlw.Cty::trusted_new_full(
    result.context_anchor(),
    program_variables,
    arguments,
    preconditions,
    postconditions,
    exceptional,
    oldies,
    effect,
    result,
    view.mask,
    freeze,
    span,
  )
}

///|
fn ProgramCloneState::clone_routine(
  self : ProgramCloneState,
  source : @mlw.RoutineSymbol,
  span : @identity.SourceSpan?,
) -> @mlw.RoutineSymbol raise {
  match self.cloned_routines.get(source) {
    Some(target) => return target
    None => ()
  }
  // Why3's `cl_find_rs` preserves routines whose identifiers are not local to
  // the cloned module.  In particular, a cloned implementation may call the
  // imported `Tuple0` constructor; cloning it would manufacture an extra
  // routine and computation type at the clone site.
  if !self.local_routines.contains(source) {
    return source
  }
  let view = source.view()
  let logic = match view.logic {
    RLnone => @mlw.RLnone
    RLpv(variable) => @mlw.RLpv(self.clone_variable(variable, span))
    RLls(symbol) =>
      @mlw.RLls(
        match self.pure_map.find_logic_symbol(symbol) {
          Some(target) => target
          None => symbol
        },
      )
    RLlemma => @mlw.RLlemma
  }
  let target = @mlw.RoutineSymbol::new_with_logic(
    self.context,
    view.name,
    if self.module_routines.contains(source) {
      clone_program_origin_at(view.origin, span)
    } else {
      view.origin
    },
    self.clone_cty(view.cty, span),
    logic,
    match view.field {
      Some(field) => Some(self.clone_variable(field, span))
      None => None
    },
    span,
  )
  self.cloned_routines[source] = target
  target
}

///|
fn ProgramCloneState::translated_logic_symbol(
  self : ProgramCloneState,
  source : @logic.LSymbol,
) -> @logic.LSymbol {
  match self.pure_map.find_logic_symbol(source) {
    Some(target) => target
    None => source
  }
}

///|
fn ProgramCloneState::translated_proposition_symbol(
  self : ProgramCloneState,
  source : @logic.PrSymbol,
) -> @logic.PrSymbol {
  match self.pure_map.find_proposition(source) {
    Some(target) => target
    None => source
  }
}

///|
fn ProgramCloneState::clone_term(
  self : ProgramCloneState,
  source : @logic.Term,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  self.pure_map.translate_term(
    self.context,
    source,
    self.logic_variable_instantiations(),
    span,
  )
}

///|
fn ProgramCloneState::clone_variant(
  self : ProgramCloneState,
  source : @mlw.ProgramVariant,
  span : @identity.SourceSpan?,
) -> @mlw.ProgramVariant raise {
  let view = source.view()
  @mlw.ProgramVariant::new(
    self.clone_term(view.term, span),
    match view.relation {
      Some(relation) => Some(self.translated_logic_symbol(relation))
      None => None
    },
    span,
  )
}

///|
fn ProgramCloneState::clone_program_pattern(
  self : ProgramCloneState,
  source : @mlw.ProgramPattern,
  span : @identity.SourceSpan?,
) -> @mlw.ProgramPattern raise {
  let view = source.view()
  let variables = view.variables.map(variable => {
    self.clone_variable(variable, span)
  })
  let pure_variables : Array[(@logic.VSymbol, @logic.VSymbol)] = []
  for index, variable in view.variables {
    pure_variables.push(
      (variable.view().pure_symbol, variables[index].view().pure_symbol),
    )
  }
  @mlw.ProgramPattern::trusted_new(
    self.pure_map.translate_pattern(
      self.context,
      view.pattern,
      pure_variables,
      span,
    ),
    self.clone_ity(view.ity, span),
    view.mask,
    view.failure,
    variables,
    span,
  )
}

///|
fn ProgramCloneState::clone_cexp(
  self : ProgramCloneState,
  source : @mlw.Cexp,
  span : @identity.SourceSpan?,
) -> @mlw.Cexp raise {
  match source.view() {
    Capp(symbol, arguments) => {
      // Why3 rebuilds every routine application with the cloned argument and
      // result types. Besides refreshing recursive `DECR` predicates, this
      // re-instantiates `freeze` and `spoils` when a program-type
      // substitution drops a phantom parameter.
      let cloned_symbol = self.clone_routine(symbol, span)
      let cloned_arguments = arguments.map(argument => {
        self.clone_variable(argument, span)
      })
      let cloned_remaining = source.cty().view().arguments.map(argument => {
        self.clone_ity(argument.view().ity, span)
      })
      let cloned_result = self.clone_ity(source.cty().view().result, span)
      let cloned = @mlw.Cexp::call(
        cloned_symbol, cloned_arguments, cloned_remaining, cloned_result, span,
      )
      return if source.cty().is_ghost() && !cloned.cty().is_ghost() {
        @mlw.Cexp::trusted_new(
          cloned.view(),
          cloned.cty().ghostify(true, span),
          span,
        )
      } else {
        cloned
      }
    }
    Cpur(symbol, arguments) =>
      return @mlw.Cexp::pure_application(
        self.context,
        self.translated_logic_symbol(symbol),
        arguments.map(argument => self.clone_variable(argument, span)),
        self.clone_ity(source.cty().view().result, span),
        self.equality,
        self.boolean_true,
        span,
      )
    Cfun(source_body) => {
      let body = self.clone_expression(source_body, span)
      let contract = self.clone_cty(source.cty(), span)
      let contract_view = contract.view()
      let cty = @mlw.Cty::new_with_variables(
        contract_view.program_variables,
        contract_view.arguments,
        contract_view.preconditions,
        contract_view.postconditions,
        contract_view.exceptional_postconditions,
        contract_view.oldies,
        body.effect(),
        contract_view.result,
        span,
        mask=contract_view.mask,
      )
      return @mlw.Cexp::function(cty, body, span)
    }
    Cany => ()
  }
  @mlw.Cexp::trusted_new(
    Cany,
    self.clone_cty(source.cty(), span, preserve_effect_ghost=false),
    span,
  )
}

///|
fn ProgramCloneState::clone_recursive_definition(
  self : ProgramCloneState,
  source : @mlw.RecursiveDefinition,
  span : @identity.SourceSpan?,
) -> @mlw.RecursiveDefinition raise {
  let view = source.view()
  let internal_view = view.internal_symbol.view()
  let internal_cty = self.clone_cty(internal_view.cty, span, drop_decrease=true)
  let internal_arguments = internal_cty.view().arguments
  let source_internal_arguments = internal_view.cty.view().arguments
  let function_arguments = view.function_.cty().view().arguments
  let public_arguments = view.symbol.view().cty.view().arguments
  if function_arguments.length() != internal_arguments.length() ||
    public_arguments.length() != internal_arguments.length() {
    @logic.fail_type(
      InvalidDeclaration,
      span,
      "recursive clone has inconsistent routine arity",
    )
  }
  for index, argument in function_arguments {
    self.cloned_variables[argument] = internal_arguments[index]
    self.seed_ity_region_mapping(
      argument.view().ity,
      source_internal_arguments[index].view().ity,
      span,
    )
  }
  for index, argument in public_arguments {
    self.cloned_variables[argument] = internal_arguments[index]
    self.seed_ity_region_mapping(
      argument.view().ity,
      source_internal_arguments[index].view().ity,
      span,
    )
  }
  self.seed_ity_region_mapping(
    view.function_.cty().view().result,
    internal_view.cty.view().result,
    span,
  )
  self.seed_ity_region_mapping(
    view.symbol.view().cty.view().result,
    internal_view.cty.view().result,
    span,
  )
  let variants = view.variants.map(variant => self.clone_variant(variant, span))
  let variant_terms = variants.map(variant => variant.view().term)
  let decrease_name = b"DECR " + internal_view.name
  let decrease = @logic.LSymbol::new_predicate(
    self.context,
    decrease_name,
    @identity.Origin::user(decrease_name, None, []),
    variant_terms.map(term => {
      guard term.ty() is Some(ty) else {
        abort("cloned recursive variant lost its value type")
      }
      ty
    }),
    None,
  )
  let internal = @mlw.RoutineSymbol::new_user(
    self.context,
    internal_view.name,
    if self.module_routines.contains(view.internal_symbol) {
      clone_program_origin_at(internal_view.origin, span)
    } else {
      internal_view.origin
    },
    internal_cty.add_preconditions(
      [@logic.Term::apply_predicate(decrease, variant_terms, None)],
      None,
    ),
    span,
  )
  self.cloned_routines[view.internal_symbol] = internal
  let function_ = self.clone_cexp(view.function_, span)
  let symbol = self.clone_routine(view.symbol, span)
  @mlw.RecursiveDefinition::new(symbol, internal, function_, variants, span)
}

///|
fn ProgramCloneState::clone_let_definition(
  self : ProgramCloneState,
  source : @mlw.LetDefinition,
  span : @identity.SourceSpan?,
) -> @mlw.LetDefinition raise {
  match source.view() {
    LDvar(variable, value) =>
      @mlw.LetDefinition::variable(
        self.clone_variable(variable, span),
        self.clone_expression(value, span),
        span,
      )
    LDsym(symbol, computation) => {
      // Module symbol collection does not visit lexically nested `let`
      // definitions. Register the binder before cloning its computation and
      // enclosing body so calls use the translated computation type rather
      // than retaining a source type refined by the outer clone.
      self.local_routines[symbol] = ()
      // A direct routine alias can point at a recursive internal symbol. Its
      // source Cty then contains the source `DECR` predicate, which is not a
      // pure-theory clone symbol. Re-apply the cloned computation first so it
      // acquires the freshly generated target `DECR`, and derive the alias Cty
      // from that computation instead of translating the stale source Cty.
      if computation.view() is Capp(_, _) && symbol.view().logic is RLnone {
        let cloned_computation = self.clone_cexp(computation, span)
        let target = @mlw.RoutineSymbol::new_user(
          self.context,
          symbol.view().name,
          symbol.view().origin,
          cloned_computation.cty(),
          span,
        )
        self.cloned_routines[symbol] = target
        return @mlw.LetDefinition::symbol(target, cloned_computation, span)
      }
      @mlw.LetDefinition::symbol(
        self.clone_routine(symbol, span),
        self.clone_cexp(computation, span),
        span,
      )
    }
    LDrec(definitions) => {
      // Make the whole local recursive group visible before cloning any
      // member, including the internal symbols used by recursive calls.
      for definition in definitions {
        let view = definition.view()
        self.local_routines[view.symbol] = ()
        self.local_routines[view.internal_symbol] = ()
      }
      @mlw.LetDefinition::recursive(
        definitions.map(definition => {
          self.clone_recursive_definition(definition, span)
        }),
        span,
      )
    }
  }
}

///|
fn append_clone_effect_spoils(
  result : Array[@logic.TyVarSymbol],
  values : ArrayView[@logic.TyVarSymbol],
) -> Unit {
  for variable in values {
    if !result.any(existing => existing == variable) {
      result.push(variable)
    }
  }
}

///|
fn cloned_expression_spoils(
  view : @mlw.ExprView,
  ity : @mlw.Ity,
  origin : @identity.Origin,
  attributes : ArrayView[Bytes],
  span : @identity.SourceSpan?,
) -> Array[@logic.TyVarSymbol] raise {
  let result : Array[@logic.TyVarSymbol] = []
  let append_effect = fn(effect : @mlw.Effect) {
    append_clone_effect_spoils(result, effect.view().spoils)
  }
  match view {
    Evar(_) | Econst(_) | Eassert(_, _) | Eabsurd => ()
    Eexec(_, executable) => append_effect(executable.view().effect)
    Eassign(assignments) =>
      append_effect(
        @mlw.Expr::assignment(assignments, ity, origin, attributes, span).effect(),
      )
    Elet(definition, body) => {
      match definition.view() {
        LDvar(_, value) => append_effect(value.effect())
        LDsym(_, _) | LDrec(_) => ()
      }
      append_effect(body.effect())
    }
    Eif(condition, consequent, alternative) => {
      append_effect(condition.effect())
      append_effect(consequent.effect())
      append_effect(alternative.effect())
    }
    Ematch(scrutinee, regular, exceptional) => {
      append_effect(scrutinee.effect())
      for branch in regular {
        append_effect(branch.view().body.effect())
      }
      for branch in exceptional {
        append_effect(branch.view().body.effect())
      }
    }
    Ewhile(condition, _, _, body) => {
      append_effect(condition.effect())
      append_effect(body.effect())
    }
    Efor(_, _, _, _, body) => append_effect(body.effect())
    Eraise(_, payload) => append_effect(payload.effect())
    Eexn(_, body) | Eghost(body) => append_effect(body.effect())
    Epure(term) =>
      if !(term.view() is Tvar(_)) {
        append_clone_effect_spoils(result, ity.reachable_type_variables())
      }
  }
  result
}

///|
fn ProgramCloneState::clone_expression(
  self : ProgramCloneState,
  source : @mlw.Expr,
  span : @identity.SourceSpan?,
) -> @mlw.Expr raise {
  let view : @mlw.ExprView = match source.view() {
    Evar(variable) => Evar(self.clone_variable(variable, span))
    Econst(constant) => Econst(constant)
    Eexec(computation, source_executable) => {
      let computation = self.clone_cexp(computation, span)
      let computation_cty = computation.cty()
      let executable = if computation_cty.view().arguments.is_empty() {
        computation_cty
      } else {
        let function_type = match source_executable.view().result.view() {
          ItyApp(symbol, _, _) if symbol.view().logic_type.name() == b"infix ->" =>
            self.program_symbol(symbol, span)
          _ =>
            @logic.fail_type(
              InvalidDeclaration,
              span,
              "partial application clone lost its function result type",
            )
        }
        computation_cty.execute_as_function(
          self.context,
          function_type,
          self.function_application,
          span,
        )
      }
      Eexec(computation, executable)
    }
    Eassign(assignments) =>
      Eassign(
        assignments.map(assignment => {
          let view = assignment.view()
          @mlw.Assignment::new(
            self.clone_variable(view.region, span),
            self.clone_routine(view.field, span),
            self.clone_variable(view.value, span),
            span,
          )
        }),
      )
    Elet(definition, body) =>
      Elet(
        self.clone_let_definition(definition, span),
        self.clone_expression(body, span),
      )
    Eif(condition, consequent, alternative) =>
      Eif(
        self.clone_expression(condition, span),
        self.clone_expression(consequent, span),
        self.clone_expression(alternative, span),
      )
    Ematch(scrutinee, regular, exceptional) =>
      Ematch(
        self.clone_expression(scrutinee, span),
        regular.map(branch => {
          let view = branch.view()
          @mlw.RegularBranch::new(
            self.clone_program_pattern(view.pattern, span),
            self.clone_expression(view.body, span),
            span,
          )
        }),
        exceptional.map(branch => {
          let view = branch.view()
          @mlw.ExceptionalBranch::new(
            self.clone_exception(view.exception, span),
            view.variables.map(variable => self.clone_variable(variable, span)),
            self.clone_expression(view.body, span),
            span,
          )
        }),
      )
    Ewhile(condition, invariants, variants, body) =>
      Ewhile(
        self.clone_expression(condition, span),
        invariants.map(invariant => self.clone_term(invariant, span)),
        variants.map(variant => self.clone_variant(variant, span)),
        self.clone_expression(body, span),
      )
    Efor(variable, bounds, internal, invariants, body) => {
      let bounds = bounds.view()
      Efor(
        self.clone_variable(variable, span),
        @mlw.ForBounds::new(
          self.clone_variable(bounds.first, span),
          bounds.direction,
          self.clone_variable(bounds.last, span),
          span,
        ),
        self.clone_variable(internal, span),
        invariants.map(invariant => self.clone_term(invariant, span)),
        self.clone_expression(body, span),
      )
    }
    Eraise(exception, payload) =>
      Eraise(
        self.clone_exception(exception, span),
        self.clone_expression(payload, span),
      )
    Eexn(exception, body) =>
      Eexn(
        self.clone_exception(exception, span),
        self.clone_expression(body, span),
      )
    Eassert(kind, formula) => Eassert(kind, self.clone_term(formula, span))
    Eghost(body) => Eghost(self.clone_expression(body, span))
    Epure(term) => Epure(self.clone_term(term, span))
    Eabsurd => Eabsurd
  }
  let ity = self.clone_ity(source.ity(), span)
  let spoils = cloned_expression_spoils(
    view,
    ity,
    source.origin(),
    source.attributes(),
    span,
  )
  @mlw.Expr::trusted_new(
    view,
    ity,
    source.origin(),
    source.attributes(),
    self.clone_effect(source.effect(), ity.context_anchor(), spoils, span),
    source.mask(),
    span,
  )
}

///|
fn ProgramCloneState::clone_program_computation(
  self : ProgramCloneState,
  source : @mlw.ProgramComputation,
  span : @identity.SourceSpan?,
) -> @mlw.ProgramComputation raise {
  match source {
    Cany(cty) => Cany(self.clone_cty(cty, span, preserve_effect_ghost=false))
    Cfun(cty, body) => {
      let contract = self.clone_cty(cty, span)
      match body {
        Some(expression) => {
          let body = self.clone_expression(expression, span)
          let contract_view = contract.view()
          Cfun(
            @mlw.Cty::new_with_variables(
              contract_view.program_variables,
              contract_view.arguments,
              contract_view.preconditions,
              contract_view.postconditions,
              contract_view.exceptional_postconditions,
              contract_view.oldies,
              body.effect(),
              contract_view.result,
              span,
              mask=contract_view.mask,
            ),
            Some(body),
          )
        }
        None => Cfun(contract, None)
      }
    }
    Cexpression(expression) => Cexpression(self.clone_cexp(expression, span))
  }
}

///|
fn program_clone_refinement_name(name : BytesView) -> Bytes {
  let output = @buffer.Buffer()
  output.write_bytes(name)
  output.write_bytes(b"'refn")
  output.contents()
}

///|
fn ProgramCloneState::explicit_refinement_cty(
  self : ProgramCloneState,
  computation : @mlw.ProgramComputation,
  span : @identity.SourceSpan?,
) -> @mlw.Cty raise {
  let source = match computation {
    Cany(cty) => cty
    Cfun(_, Some(body)) =>
      match body.view() {
        Eexec(computation, cty) =>
          if computation.view() is Cany {
            cty
          } else {
            fail_invalid_input(
              InvalidDeclaration,
              ProgramTyping,
              span,
              "only an abstract routine can be instantiated by a clone",
            )
          }
        _ =>
          fail_invalid_input(
            InvalidDeclaration,
            ProgramTyping,
            span,
            "only an abstract routine can be instantiated by a clone",
          )
      }
    Cfun(_, None) | Cexpression(_) =>
      fail_invalid_input(
        InvalidDeclaration,
        ProgramTyping,
        span,
        "only an abstract routine can be instantiated by a clone",
      )
  }
  self.clone_cty(source, span, preserve_effect_ghost=false)
}

///|
fn ProgramCloneState::record_routine_refinement(
  self : ProgramCloneState,
  source : @mlw.RoutineSymbol,
  computation : @mlw.ProgramComputation,
  theory_item_boundary : Int,
  span : @identity.SourceSpan?,
) -> Unit raise {
  guard self.cloned_routines.get(source) is Some(target) else {
    fail_invalid_input(
      InvalidDeclaration,
      ProgramTyping,
      span,
      "an explicit routine clone substitution lost its target",
    )
  }
  let source_view = source.view()
  let cty = self
    .explicit_refinement_cty(computation, span)
    .ghostify(source.is_ghost(), span)
  let cty_view = cty.view()
  let call = @mlw.Cexp::call(
    target,
    cty_view.arguments,
    [],
    cty_view.result,
    span,
  )
  let body = @mlw.Expr::execute(
    call,
    @identity.Origin::generated(@identity.Wp, b"", None, []),
    [],
    None,
  )
  let name = program_clone_refinement_name(source_view.name)
  let origin = @identity.Origin::user(
    name,
    source_view.origin.identifier_source_span(),
    source_view.origin.attributes(),
  )
  let refinement = @mlw.RoutineSymbol::new(
    self.context,
    name,
    origin,
    cty,
    RLnone,
    None,
    span,
  )
  self.vc_refinements.push((refinement, cty, body, theory_item_boundary))
}

///|
fn ProgramCloneState::clone_program_type_declaration(
  self : ProgramCloneState,
  source : @mlw.ProgramTypeDeclaration,
  span : @identity.SourceSpan?,
) -> @mlw.ProgramTypeDeclaration? raise {
  let view = source.view()
  guard self.clone_type(view.symbol, span) is Some(symbol) else { return None }
  // `clone_type` installs the translated invariants on the canonical cloned
  // symbol. Reuse that exact metadata here: retranslating after field/routine
  // maps have grown can produce alpha-distinct terms for the same symbol.
  let invariants = symbol.view().invariants.to_owned()
  Some(
    @mlw.ProgramTypeDeclaration::trusted_new(
      symbol,
      // `clone_type_decl` rebuilds record projections and variant
      // constructors with `id_clone`, which retains each source identifier's
      // location.  Other program declarations use the module-clone location.
      view.fields.map(field => {
        self.clone_routine(field, field.view().origin.source_span())
      }),
      view.constructors.map(constructor_symbol => {
        self.clone_routine(
          constructor_symbol,
          constructor_symbol.view().origin.source_span(),
        )
      }),
      invariants,
      span,
      witness=match view.witness {
        Some(witness) => Some(self.clone_expression(witness, span))
        None => None
      },
    ),
  )
}

///|
fn ProgramCloneState::mapped_declaration_dependency(
  self : ProgramCloneState,
  dependency : @logic.DeclDependency,
) -> @logic.DeclDependency? {
  match dependency {
    TypeDependency(symbol) =>
      if self.pure_map.find_type(symbol) is Some(_) {
        None
      } else {
        match self.pure_map.find_type_symbol(symbol) {
          Some(target) => Some(TypeDependency(target))
          None => None
        }
      }
    LogicDependency(symbol) =>
      if self.explicit_logic_symbols.contains(symbol) {
        None
      } else {
        match self.pure_map.find_logic_symbol(symbol) {
          Some(target) => Some(LogicDependency(target))
          None => None
        }
      }
    PropositionDependency(symbol) =>
      match self.pure_map.find_proposition(symbol) {
        Some(target) => Some(PropositionDependency(target))
        None => None
      }
  }
}

///|
fn ProgramCloneState::cloned_pure_declarations(
  self : ProgramCloneState,
  builder : @mlw.PmoduleBuilder,
  declarations : ArrayView[@logic.Decl],
) -> Array[@logic.Decl] {
  let cloned : Array[@logic.Decl] = []
  let known = builder.pure_known()
  for declaration in declarations {
    for dependency in declaration.introduced_symbols() {
      guard self.mapped_declaration_dependency(dependency) is Some(target) else {
        continue
      }
      match known.find_declaration(target) {
        Some(translated) => cloned.push(translated)
        None => ()
      }
      break
    }
  }
  cloned
}

///|
fn ProgramCloneState::clone_meta(
  self : ProgramCloneState,
  source : @theory.Meta,
  span : @identity.SourceSpan?,
) -> @theory.Meta? raise {
  let view = source.view()
  let arguments : Array[@theory.MetaArgument] = []
  for argument in view.arguments {
    match argument {
      MetaType(ty) =>
        arguments.push(
          MetaType(self.pure_map.translate_type(self.context, ty, span)),
        )
      MetaTypeSymbol(symbol) =>
        match self.pure_map.find_type_symbol(symbol) {
          Some(target) => arguments.push(MetaTypeSymbol(target))
          None =>
            if self.pure_map.find_type(symbol) is Some(_) ||
              self.source_pure.is_local_id(symbol.semantic_id()) {
              return None
            } else {
              arguments.push(MetaTypeSymbol(symbol))
            }
        }
      MetaLogicSymbol(symbol) =>
        match self.pure_map.find_logic_symbol(symbol) {
          Some(target) => arguments.push(MetaLogicSymbol(target))
          None =>
            if self.source_pure.is_local_id(symbol.semantic_id()) {
              return None
            } else {
              arguments.push(MetaLogicSymbol(symbol))
            }
        }
      MetaPropositionSymbol(symbol) =>
        match self.pure_map.find_proposition(symbol) {
          Some(target) => arguments.push(MetaPropositionSymbol(target))
          None =>
            if self.source_pure.is_local_id(symbol.semantic_id()) {
              return None
            } else {
              arguments.push(MetaPropositionSymbol(symbol))
            }
        }
      MetaString(value) => arguments.push(MetaString(value))
      MetaInteger(value) => arguments.push(MetaInteger(value))
      MetaIdentifier(value) => arguments.push(MetaIdentifier(value))
    }
  }
  Some(
    @theory.MetaDescriptor::new(
      view.name,
      view.argument_types,
      view.exclusive,
      b"",
      span,
    ).apply(arguments, span),
  )
}

///|
fn ProgramCloneState::clone_program_declaration(
  self : ProgramCloneState,
  builder : @mlw.PmoduleBuilder,
  source : @mlw.ProgramDeclaration,
  span : @identity.SourceSpan?,
) -> @mlw.ProgramDeclaration? raise {
  let pure = self.cloned_pure_declarations(builder, source.pure_declarations())
  let metas : Array[@theory.Meta] = []
  for meta in source.metas() {
    match self.clone_meta(meta, span) {
      Some(cloned) => metas.push(cloned)
      None => ()
    }
  }
  let anchor = self.context.fresh_id()
  match source {
    PDtype(declarations, _, _) => {
      let cloned : Array[@mlw.ProgramTypeDeclaration] = []
      for declaration in declarations {
        match self.clone_program_type_declaration(declaration, span) {
          Some(declaration) => cloned.push(declaration)
          None => ()
        }
      }
      if cloned.is_empty() {
        None
      } else {
        for declaration in cloned {
          self.vc_suppressed_types.push(declaration.view().symbol)
        }
        Some(
          @mlw.ProgramDeclaration::type_declarations(
            anchor, cloned, pure, metas, span,
          ),
        )
      }
    }
    PDpure(declarations, _) =>
      if !declarations.is_empty() && pure.is_empty() {
        None
      } else {
        Some(@mlw.ProgramDeclaration::pure(anchor, pure, metas, span))
      }
    PDlet(symbol, computation, _, _) =>
      if self.explicit_routines.contains(symbol) {
        // Building the translated contract allocates formal variables and
        // extends clone caches. Delay it until all visible cloned declarations
        // and the witness anchor have been created, so VC-only metadata cannot
        // perturb the canonical program module.
        guard self.pure_map.cloned_item_boundary(self.source_theory_item_cursor)
          is Some(theory_item_boundary) else {
          fail_invalid_input(
            InvalidDeclaration,
            ProgramTyping,
            span,
            "the pure clone lost a program-declaration item boundary",
          )
        }
        self.vc_pending_refinements.push(
          (symbol, computation, theory_item_boundary),
        )
        None
      } else {
        let symbol = self.clone_routine(symbol, span)
        self.vc_suppressed_routines.push(symbol)
        Some(
          @mlw.ProgramDeclaration::routine(
            symbol.semantic_id(),
            symbol,
            self.clone_program_computation(computation, span),
            pure,
            metas,
            span,
          ),
        )
      }
    PDvar(variable, value, _, _) =>
      if self.explicit_variables.contains(variable) {
        @logic.fail_type(
          InvalidDeclaration,
          span,
          "a defined program variable cannot be instantiated",
        )
      } else {
        let variable = self.clone_variable(variable, span)
        Some(
          @mlw.ProgramDeclaration::variable(
            variable.semantic_id(),
            variable,
            self.clone_expression(value, span),
            pure,
            metas,
            span,
          ),
        )
      }
    PDrec(definitions, _, _) => {
      for definition in definitions {
        if self.explicit_routines.contains(definition.view().symbol) {
          @logic.fail_type(
            InvalidDeclaration,
            span,
            "a recursive routine cannot be instantiated",
          )
        }
      }
      let cloned = definitions.map(definition => {
        self.clone_recursive_definition(definition, span)
      })
      for definition in cloned {
        self.vc_suppressed_routines.push(definition.view().symbol)
      }
      Some(
        @mlw.ProgramDeclaration::recursive(
          cloned[0].view().symbol.semantic_id(),
          cloned,
          pure,
          metas,
          span,
        ),
      )
    }
    PDexn(exception, _, _) =>
      if self.explicit_exceptions.contains(exception) {
        None
      } else {
        let exception = self.clone_exception(exception, span)
        Some(
          @mlw.ProgramDeclaration::exception(
            exception.semantic_id(),
            exception,
            pure,
            metas,
            span,
          ),
        )
      }
  }
}

///|
fn ProgramCloneState::clone_nested_witness(
  self : ProgramCloneState,
  source : @mlw.ProgramCloneWitness,
  span : @identity.SourceSpan?,
) -> @mlw.ProgramCloneWitness raise {
  let view = source.view()
  @mlw.ProgramCloneWitness::trusted_new(
    self.context.fresh_id(),
    view.source,
    view.type_instantiations.map(entry => {
      (entry.0, self.clone_ity(entry.1, span))
    }),
    view.program_type_instantiations.map(entry => {
      (entry.0, self.program_symbol(entry.1, span))
    }),
    view.logic_instantiations.map(entry => {
      (entry.0, self.translated_logic_symbol(entry.1))
    }),
    view.proposition_instantiations.map(entry => {
      (entry.0, self.translated_proposition_symbol(entry.1))
    }),
    view.proposition_kinds,
    view.program_variable_instantiations.map(entry => {
      (entry.0, self.clone_variable(entry.1, span))
    }),
    view.routine_instantiations.map(entry => {
      (entry.0, self.clone_routine(entry.1, span))
    }),
    view.exception_instantiations.map(entry => {
      (entry.0, self.clone_exception(entry.1, span))
    }),
    view.default_proposition_kind,
    span,
  )
}

///|
fn ProgramCloneState::consume_source_theory_declaration(
  self : ProgramCloneState,
  span : @identity.SourceSpan?,
) -> Unit raise {
  let items = self.source_pure.view().items
  if self.source_theory_item_cursor >= items.length() ||
    !(items[self.source_theory_item_cursor] is TheoryDecl(_)) {
    fail_invalid_input(
      InvalidDeclaration,
      ProgramTyping,
      span,
      "program and pure declaration streams diverged during cloning",
    )
  }
  self.source_theory_item_cursor = self.source_theory_item_cursor + 1
}

///|
fn ProgramCloneState::consume_source_theory_meta(
  self : ProgramCloneState,
  span : @identity.SourceSpan?,
) -> Unit raise {
  let items = self.source_pure.view().items
  if self.source_theory_item_cursor >= items.length() ||
    !(items[self.source_theory_item_cursor] is TheoryMeta(_)) {
    fail_invalid_input(
      InvalidDeclaration,
      ProgramTyping,
      span,
      "program and pure meta streams diverged during cloning",
    )
  }
  self.source_theory_item_cursor = self.source_theory_item_cursor + 1
}

///|
fn ProgramCloneState::align_source_theory_item(
  self : ProgramCloneState,
  item : @mlw.ModuleItem,
  span : @identity.SourceSpan?,
) -> Unit raise {
  let expected = match item {
    Udecl(declaration) =>
      if !declaration.pure_declarations().is_empty() {
        0
      } else if !declaration.metas().is_empty() {
        1
      } else {
        return
      }
    Uuse(_) => 2
    Uclone(_) => 3
    Umeta(_) => 1
    Uscope(_, _) => return
  }
  let items = self.source_pure.view().items
  for index = self.source_theory_item_cursor
      index < items.length()
      index = index + 1 {
    let matches = match (expected, items[index]) {
      (0, TheoryDecl(_)) | (1, TheoryMeta(_)) => true
      (2, TheoryUse(key)) => item is Uuse(expected_key) && key == expected_key
      (3, TheoryClone(witness)) =>
        item is Uclone(expected_witness) &&
        witness.view().source == expected_witness.view().source
      _ => false
    }
    if matches {
      self.source_theory_item_cursor = index
      return
    }
  }
  if expected == 2 {
    // Repeated program uses remain in the module stream after the pure theory
    // has deduplicated the corresponding TheoryUse item.
    return
  }
  fail_invalid_input(
    InvalidDeclaration,
    ProgramTyping,
    span,
    "program item lost its source-theory clone boundary",
  )
}

///|
fn ProgramCloneState::advance_source_theory_item(
  self : ProgramCloneState,
  item : @mlw.ModuleItem,
  span : @identity.SourceSpan?,
) -> Unit raise {
  match item {
    Udecl(declaration) => {
      for _ in declaration.pure_declarations() {
        self.consume_source_theory_declaration(span)
      }
      for _ in declaration.metas() {
        self.consume_source_theory_meta(span)
      }
    }
    Uuse(key) => {
      let items = self.source_pure.view().items
      if self.source_theory_item_cursor < items.length() &&
        items[self.source_theory_item_cursor] is TheoryUse(source_key) &&
        source_key == key {
        self.source_theory_item_cursor = self.source_theory_item_cursor + 1
      }
    }
    Uclone(witness) => {
      let items = self.source_pure.view().items
      if self.source_theory_item_cursor >= items.length() ||
        !(items[self.source_theory_item_cursor] is TheoryClone(pure_witness) &&
        pure_witness.view().source == witness.view().source) {
        fail_invalid_input(
          InvalidDeclaration,
          ProgramTyping,
          span,
          "program and pure clone streams diverged during cloning",
        )
      }
      self.source_theory_item_cursor = self.source_theory_item_cursor + 1
    }
    Umeta(_) => self.consume_source_theory_meta(span)
    Uscope(_, _) => ()
  }
}

///|
fn ProgramCloneState::clone_module_items(
  self : ProgramCloneState,
  builder : @mlw.PmoduleBuilder,
  owner : @mlw.Pmodule,
  items : ArrayView[@mlw.ModuleItem],
  span : @identity.SourceSpan?,
) -> Unit raise {
  for item in items {
    self.align_source_theory_item(item, span)
    match item {
      Udecl(declaration) =>
        match self.clone_program_declaration(builder, declaration, span) {
          Some(cloned) => builder.add_existing_program_declaration(cloned, span)
          None => ()
        }
      Uuse(key) => {
        guard owner.referenced_module(key) is Some(used) else {
          @logic.fail_type(
            InvalidDeclaration,
            span,
            "cloned module lost a used-module dependency",
          )
        }
        builder.add_use(used, true, span)
      }
      Uclone(witness) => {
        let source_boundary = self.source_theory_item_cursor
        let retained = match
          (
            self.pure_map.cloned_item_boundary(source_boundary),
            self.pure_map.cloned_item_boundary(source_boundary + 1),
          ) {
          (Some(before), Some(after)) => after > before
          _ => false
        }
        if retained {
          let cloned = self.clone_nested_witness(witness, span)
          guard owner.referenced_module(witness.view().source) is Some(used) else {
            @logic.fail_type(
              InvalidDeclaration,
              span,
              "cloned module lost a nested-clone dependency",
            )
          }
          builder.add_existing_clone(used, cloned, span)
        }
      }
      Umeta(meta) =>
        match self.clone_meta(meta, span) {
          Some(cloned) => builder.add_existing_meta(cloned, span)
          None => ()
        }
      Uscope(name, nested) => {
        builder.open_scope(name, span)
        self.clone_module_items(builder, owner, nested, span)
        builder.close_scope(false, span)
      }
    }
    self.advance_source_theory_item(item, span)
  }
}

///|
fn ProgramCloneState::clone_namespace(
  self : ProgramCloneState,
  source : @mlw.ProgramNamespace,
  span : @identity.SourceSpan?,
) -> @mlw.ProgramNamespace raise {
  let mut cloned = @mlw.ProgramNamespace::empty()
  let view = source.view()
  for entry in view.types {
    match self.clone_type(entry.1, span) {
      Some(symbol) => cloned = cloned.add_type(entry.0, symbol, span)
      None => ()
    }
  }
  for entry in view.variables {
    let variable = if self.local_variables.contains(entry.1) {
      self.clone_variable(entry.1, span)
    } else {
      entry.1
    }
    cloned = cloned.add_variable(entry.0, variable, span)
  }
  for entry in view.routines {
    let routine = if self.local_routines.contains(entry.1) {
      self.clone_routine(entry.1, span)
    } else {
      entry.1
    }
    cloned = cloned.add_routine(entry.0, routine, span)
  }
  for entry in view.exceptions {
    let exception = if self.local_exceptions.contains(entry.1) {
      self.clone_exception(entry.1, span)
    } else {
      entry.1
    }
    cloned = cloned.add_exception(entry.0, exception, span)
  }
  for entry in view.subspaces {
    cloned = cloned.add_subspace(
      entry.0,
      self.clone_namespace(entry.1, span),
      span,
    )
  }
  cloned
}

///|
fn ProgramTyping::add_program_clone(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  source_name : @parser.QualId,
  substitutions : ArrayView[@parser.CloneSubstitution],
  span : @identity.SourceSpan?,
) -> Unit raise {
  let source = resolve_used_module(
    self.environment,
    self.library_path,
    self.file_modules,
    source_name,
  )
  let logic_definition_overrides : Array[
    (Array[@logic.LogicDefinition], Array[@logic.PrSymbol]),
  ] = []
  self.collect_program_clone_logic_definition_overrides(
    source.pure_theory().export_namespace(),
    source.view().items,
    logic_definition_overrides,
  )
  let base_pure_instantiation = self.pure.clone_instantiation(
    builder.pure_elaboration_builder(),
    source.pure_theory(),
    substitutions,
    span,
    allow_program_symbols=true,
  )
  let cloned_routines : Map[@mlw.RoutineSymbol, @mlw.RoutineSymbol] = Map([])
  let cloned_variables : Map[@mlw.PVariable, @mlw.PVariable] = Map([])
  let cloned_exceptions : Map[@mlw.XSymbol, @mlw.XSymbol] = Map([])
  let cloned_types : Map[@mlw.ProgramTypeSymbol, @mlw.ProgramTypeSymbol] = Map([])
  let local_types : Map[@mlw.ProgramTypeSymbol, @mlw.ProgramTypeDeclaration] = Map([],
  )
  let local_routines : Map[@mlw.RoutineSymbol, Unit] = Map([])
  let internal_routines : Map[@mlw.RoutineSymbol, Unit] = Map([])
  let local_propositions : Map[@logic.PrSymbol, Unit] = Map([])
  let local_variables : Map[@mlw.PVariable, Unit] = Map([])
  let local_exceptions : Map[@mlw.XSymbol, Unit] = Map([])
  let logic_origin_overrides : Map[@logic.LSymbol, @identity.Origin] = Map([])
  let proposition_origin_overrides : Map[@logic.PrSymbol, @identity.Origin] = Map([],
  )
  collect_local_program_symbols(
    source.view().items,
    local_types,
    local_propositions,
    local_variables,
    local_routines,
    internal_routines,
    local_exceptions,
  )
  let witness_routines = local_routines.copy()
  collect_program_clone_origin_overrides(
    source.view().items,
    span,
    logic_origin_overrides,
    proposition_origin_overrides,
  )
  let pure_logic_instances = base_pure_instantiation.view().inst_ls.to_owned()
  let base_view = base_pure_instantiation.view()
  for source_type, declaration in local_types {
    let source_logic = source_type.view().logic_type
    for type_instance in base_view.inst_ts {
      if type_instance.0 == source_logic {
        let target_type = builder
          .program_namespace()
          .find_type_by_logic(type_instance.1, span)
        cloned_types[source_type] = target_type
        if !declaration.view().fields.is_empty() {
          preseed_program_record_refinement(
            declaration,
            target_type,
            builder.program_namespace(),
            cloned_variables,
            cloned_routines,
            pure_logic_instances,
            span,
          )
        }
        break
      }
    }
  }
  for substitution in substitutions {
    match substitution {
      CSvsym(source_name, target_name) => {
        let source_path = qualid_segments(source_name)
        let target_path = qualid_segments(target_name)
        match source.export_namespace().find_variable_option(source_path) {
          Some(source_variable) => {
            let target_variable = builder
              .program_namespace()
              .find_variable(target_path, Some(qualid_span(target_name)))
            // Explicit substitutions seed the same map used by Cty/effect
            // translation and namespace export.
            // The source symbol is stable across every occurrence.
            cloned_variables[source_variable] = target_variable
          }
          None => {
            let source_routine = source
              .export_namespace()
              .find_routine(source_path, Some(qualid_span(source_name)))
            let target_routine = builder
              .program_namespace()
              .find_routine(target_path, Some(qualid_span(target_name)))
            cloned_routines[source_routine] = target_routine
            match (source_routine.view().logic, target_routine.view().logic) {
              (RLls(source_logic), RLls(target_logic)) =>
                add_program_clone_logic_instance(
                  pure_logic_instances, source_logic, target_logic, span,
                )
              (RLls(_), _) =>
                fail_invalid_input(
                  InvalidDeclaration,
                  ProgramTyping,
                  Some(qualid_span(target_name)),
                  "a logical program routine requires a logical clone target",
                )
              _ => ()
            }
          }
        }
      }
      CSxsym(source_name, target_name) => {
        let source_exception = source
          .export_namespace()
          .find_exception(
            qualid_segments(source_name),
            Some(qualid_span(source_name)),
          )
        let target_exception = builder
          .program_namespace()
          .find_exception(
            qualid_segments(target_name),
            Some(qualid_span(target_name)),
          )
        cloned_exceptions[source_exception] = target_exception
      }
      _ => ()
    }
  }
  let omitted_propositions : Map[@logic.PrSymbol, Unit] = Map([])
  collect_omitted_program_clone_propositions(
    source.view().items,
    cloned_routines,
    omitted_propositions,
  )
  let pure_instantiation = @theory.TheoryInstantiation::new(
    base_view.inst_ty,
    base_view.inst_ts,
    pure_logic_instances,
    base_view.inst_pr,
    base_view.inst_df,
    span,
  )
  let pure_map = builder
    .pure_elaboration_builder()
    .add_clone(
      source.pure_theory(),
      pure_instantiation,
      span,
      logic_origin_overrides=[
        for symbol, origin in logic_origin_overrides => (symbol, origin)
      ],
      proposition_origin_overrides=[
        for symbol, origin in proposition_origin_overrides => (symbol, origin)
      ],
      omitted_propositions=[
        for proposition, _ in omitted_propositions => proposition
      ],
      logic_definition_overrides~,
      omit_empty_source_subspaces=true,
    )
  let explicit_type_symbols : Map[@logic.TypeSymbol, Unit] = Map([])
  for entry in pure_instantiation.view().inst_ts {
    explicit_type_symbols[entry.0] = ()
  }
  let explicit_logic_symbols : Map[@logic.LSymbol, Unit] = Map([])
  for entry in pure_instantiation.view().inst_ls {
    explicit_logic_symbols[entry.0] = ()
  }
  let explicit_variables : Map[@mlw.PVariable, Unit] = Map([])
  for variable, _ in cloned_variables {
    explicit_variables[variable] = ()
  }
  let explicit_routines : Map[@mlw.RoutineSymbol, Unit] = Map([])
  for routine, _ in cloned_routines {
    explicit_routines[routine] = ()
  }
  let explicit_exceptions : Map[@mlw.XSymbol, Unit] = Map([])
  for exception, _ in cloned_exceptions {
    explicit_exceptions[exception] = ()
  }
  let state : ProgramCloneState = {
    context: self.context,
    source_pure: source.pure_theory(),
    pure_map,
    explicit_type_symbols,
    explicit_logic_symbols,
    explicit_variables,
    explicit_routines,
    explicit_exceptions,
    equality: builder.pure_namespace().find_logic([b"infix ="], span),
    boolean_true: builder.pure_namespace().find_logic([b"True"], span),
    function_application: self.environment
    .high_order_module()
    .pure_theory()
    .export_namespace()
    .find_logic([b"infix @"], span),
    target_namespace: builder.program_namespace(),
    local_types,
    cloned_types,
    local_variables,
    local_routines,
    module_routines: witness_routines,
    local_exceptions,
    cloned_variables,
    cloned_regions: Map([]),
    cloned_routines,
    cloned_exceptions,
    source_theory_item_cursor: 0,
    vc_pending_refinements: [],
    vc_refinements: [],
    vc_suppressed_routines: [],
    vc_suppressed_types: [],
  }
  state.clone_module_items(builder, source, source.view().items, span)
  let source_items = source.pure_theory().view().items
  while state.source_theory_item_cursor < source_items.length() &&
        source_items[state.source_theory_item_cursor] is TheoryUse(_) {
    state.source_theory_item_cursor = state.source_theory_item_cursor + 1
  }
  if state.source_theory_item_cursor !=
    source.pure_theory().view().items.length() {
    fail_invalid_input(
      InvalidDeclaration,
      ProgramTyping,
      span,
      "program and pure item streams ended at different clone boundaries",
    )
  }
  let cloned_namespace = state.clone_namespace(source.export_namespace(), span)
  let map_view = pure_map.view()
  let type_instantiations : Array[(@logic.TypeSymbol, @mlw.Ity)] = []
  for entry in map_view.sm_ty {
    type_instantiations.push(
      (entry.0, @mlw.Ity::from_ty(builder.program_namespace(), entry.1, span)),
    )
  }
  let program_type_instantiations : Array[
    (@logic.TypeSymbol, @mlw.ProgramTypeSymbol),
  ] = []
  for source_type, target_type in state.cloned_types {
    let source_logic = source_type.view().logic_type
    if state.source_pure.is_local_id(source_logic.semantic_id()) {
      program_type_instantiations.push((source_logic, target_type))
    }
  }
  program_type_instantiations.sort_by((left, right) => {
    left.0.semantic_id().local_id().compare(right.0.semantic_id().local_id())
  })
  let program_variable_instantiations = [
    for source_variable, target_variable in state.cloned_variables if state.local_variables.contains(
      source_variable,
    ) => (source_variable.view().pure_symbol, target_variable)
  ]
  program_variable_instantiations.sort_by((left, right) => {
    left.0.semantic_id().local_id().compare(right.0.semantic_id().local_id())
  })
  let routine_instantiations = [
    for source_routine, target_routine in state.cloned_routines if witness_routines.contains(
      source_routine,
    ) &&
    !internal_routines.contains(source_routine) => {
      (source_routine, target_routine)
    }
  ]
  routine_instantiations.sort_by((left, right) => {
    left.0.semantic_id().local_id().compare(right.0.semantic_id().local_id())
  })
  let exception_instantiations = [
    for source_exception, target_exception in state.cloned_exceptions if state.local_exceptions.contains(
      source_exception,
    ) => (source_exception, target_exception)
  ]
  exception_instantiations.sort_by((left, right) => {
    left.0.semantic_id().local_id().compare(right.0.semantic_id().local_id())
  })
  let instantiation_view = pure_instantiation.view()
  let proposition_instantiations = [
    for entry in map_view.sm_pr if local_propositions.contains(entry.0) => entry
  ]
  let witness_anchor = self.context.fresh_id()
  for refinement in state.vc_pending_refinements {
    state.record_routine_refinement(
      refinement.0,
      refinement.1,
      refinement.2,
      span,
    )
  }
  let witness = @mlw.ProgramCloneWitness::trusted_new(
    witness_anchor,
    source.key(),
    type_instantiations,
    program_type_instantiations,
    map_view.sm_ls,
    proposition_instantiations,
    instantiation_view.inst_pr,
    program_variable_instantiations,
    routine_instantiations,
    exception_instantiations,
    instantiation_view.inst_df,
    span,
    vc_refinements=state.vc_refinements,
    vc_suppressed_routines=state.vc_suppressed_routines,
    vc_suppressed_types=state.vc_suppressed_types,
  )
  builder.finish_clone(source, witness, cloned_namespace, span)
}

///|
fn registered_module(
  environment : @environment.Environment,
  key : @theory.TheoryKey,
  span : @identity.SourceSpan?,
) -> @mlw.Pmodule? raise {
  Some(environment.resolve_module(key, span)) catch {
    @environment.EnvironmentError(diagnostic) =>
      if diagnostic.kind == ResolveError {
        None
      } else {
        raise @environment.EnvironmentError(diagnostic)
      }
  }
}

///|
fn pty_mentions_program_type_group(
  source : @parser.Pty,
  names : ArrayView[Bytes],
) -> Bool {
  match source {
    PTtyvar(_) => false
    PTtyapp(qualid, arguments) => {
      let path = qualid_segments(qualid)
      (path.length() == 1 && names.any(name => name[:] == path[0][:])) ||
      arguments.any(argument => pty_mentions_program_type_group(argument, names))
    }
    PTtuple(arguments) | PTref(arguments) =>
      arguments.any(argument => pty_mentions_program_type_group(argument, names))
    PTarrow(parameter, result) =>
      pty_mentions_program_type_group(parameter, names) ||
      pty_mentions_program_type_group(result, names)
    PTscope(_, nested) | PTparen(nested) | PTpure(nested) =>
      pty_mentions_program_type_group(nested, names)
  }
}

///|
fn simple_program_type_group(
  declarations : ArrayView[@parser.TypeDecl],
) -> Bool {
  if declarations.is_empty() {
    return false
  }
  let names = declarations.map(declaration => declaration.ident.name)
  for declaration in declarations {
    if !declaration.invariant.terms.is_empty() ||
      declaration.witness is Some(_) ||
      declaration.visibility is Private {
      return false
    }
    match declaration.definition {
      TDalias(target) =>
        if declaration.mutable ||
          declaration.visibility != Public ||
          pty_mentions_program_type_group(target, names) {
          return false
        }
      TDrange(_, _) | TDfloat(_, _) =>
        if declaration.mutable || declaration.visibility != Public {
          return false
        }
      TDalgebraic(cases) => {
        if declaration.mutable || declaration.visibility != Public {
          return false
        }
        for case_ in cases {
          for parameter in case_.params {
            if pty_mentions_program_type_group(parameter.param_type, names) {
              return false
            }
          }
        }
      }
      TDrecord(fields) => {
        if declaration.mutable {
          return false
        }
        if declaration.visibility is Abstract && fields.is_empty() {
          continue
        }
        if declaration.visibility != Public {
          return false
        }
        for field in fields {
          if pty_mentions_program_type_group(field.field_type, names) {
            return false
          }
        }
      }
    }
  }
  true
}

///|
fn nonfree_record_type_group(
  declarations : ArrayView[@parser.TypeDecl],
) -> Bool {
  if declarations.is_empty() {
    return false
  }
  let names = declarations.map(declaration => declaration.ident.name)
  for declaration in declarations {
    guard declaration.definition is TDrecord(fields) else { return false }
    for field in fields {
      if pty_mentions_program_type_group(field.field_type, names) {
        return false
      }
    }
  }
  true
}

///|
fn data_backed_nonfree_record(declaration : @parser.TypeDecl) -> Bool {
  declaration.visibility == Public &&
  declaration.invariant.terms.is_empty() &&
  declaration.definition is TDrecord([_, ..])
}

///|
fn recursive_program_type_group(
  declarations : ArrayView[@parser.TypeDecl],
) -> Bool {
  if declarations.is_empty() {
    return false
  }
  let names = declarations.map(declaration => declaration.ident.name)
  let mut recursive = false
  for declaration in declarations {
    if declaration.visibility != Public ||
      declaration.mutable ||
      !declaration.invariant.terms.is_empty() ||
      declaration.witness is Some(_) {
      return false
    }
    match declaration.definition {
      TDalias(target) =>
        if pty_mentions_program_type_group(target, names) {
          recursive = true
        }
      TDalgebraic(cases) =>
        for case_ in cases {
          for parameter in case_.params {
            if pty_mentions_program_type_group(parameter.param_type, names) {
              recursive = true
            }
          }
        }
      TDrecord(fields) => {
        if fields.is_empty() {
          return false
        }
        for field in fields {
          if field.mutable {
            return false
          }
          if pty_mentions_program_type_group(field.field_type, names) {
            recursive = true
          }
        }
      }
      TDrange(_, _) | TDfloat(_, _) => return false
    }
  }
  recursive
}

///|
fn source_field_name(
  ident : @parser.Ident?,
  _span : @parser.Span,
) -> @theory.SemanticName {
  match ident {
    Some(ident) =>
      @theory.SemanticName::new(
        ident.name,
        [b"is_field_id", b"builtin"],
        Some(source_span(ident.span)),
      )
    // Why3 creates anonymous datatype fields with `id_fresh "a"` and does
    // not attach the surrounding parameter location to that binder.
    None => @theory.SemanticName::new(b"a", [], None)
  }
}

///|
fn ProgramTyping::new_type_field_in_spaces(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  ident : @parser.Ident?,
  fallback_span : @parser.Span,
  source_type : @parser.Pty,
  ghost : Bool,
) -> @mlw.PVariable raise {
  @mlw.PVariable::trusted_new(
    self.context,
    source_field_name(ident, fallback_span),
    self.program_ity(
      pure_space,
      program_space,
      source_type,
      Some(source_span(fallback_span)),
    ),
    ghost,
    Some(source_span(fallback_span)),
  )
}

///|
fn ProgramTyping::new_type_field(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  ident : @parser.Ident?,
  fallback_span : @parser.Span,
  source_type : @parser.Pty,
  ghost : Bool,
) -> @mlw.PVariable raise {
  self.new_type_field_in_spaces(
    builder.pure_namespace(),
    builder.program_namespace(),
    ident,
    fallback_span,
    source_type,
    ghost,
  )
}

///|
fn make_type_argument_ities(symbol : @logic.TypeSymbol) -> Array[@mlw.Ity] {
  symbol.view().parameters.map(@mlw.Ity::variable)
}

///|
fn ProgramTyping::make_program_type_routines(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  program_symbol : @mlw.ProgramTypeSymbol,
  constructor_fields : ArrayView[Array[@mlw.PVariable]],
  span : @identity.SourceSpan?,
) -> (Array[@mlw.RoutineSymbol], Array[@mlw.RoutineSymbol]) raise {
  let logic_type = program_symbol.view().logic_type
  let formal_regions = program_symbol.view().regions.map(@mlw.Ity::region)
  let result = @mlw.Ity::instantiate(
    program_symbol,
    make_type_argument_ities(logic_type),
    formal_regions,
    span,
  )
  let data_constructors = builder
    .pure_known()
    .find_constructors(logic_type, span)
  if data_constructors.length() != constructor_fields.length() {
    @logic.fail_type(
      InvalidDeclaration,
      span,
      "program and logical constructors have different cardinalities",
    )
  }
  let constructors : Array[@mlw.RoutineSymbol] = []
  let projections : Array[@mlw.RoutineSymbol] = []
  let projected : Map[@logic.LSymbol, Unit] = Map([])
  let constructor_effect = match result.view() {
    ItyReg(region) => @mlw.Effect::pure(false).reset([region], span)
    _ => @mlw.Effect::pure(false)
  }
  for index, data_constructor in data_constructors {
    let fields = constructor_fields[index]
    let constructor_logic = data_constructor.view().symbol
    let constructor_view = constructor_logic.view()
    let raw_constructor_cty = @mlw.Cty::new(
      fields,
      [],
      [],
      [],
      [],
      constructor_effect,
      result,
      span,
    )
    let constructor_cty = raw_constructor_cty.add_postconditions(
      [
        routine_logic_postcondition(
          self.context,
          builder.pure_namespace(),
          raw_constructor_cty,
          constructor_logic,
          span,
        ),
      ],
      span,
    )
    constructors.push(
      @mlw.RoutineSymbol::new_with_logic(
        self.context,
        constructor_view.name,
        constructor_view.origin,
        constructor_cty,
        RLls(constructor_logic),
        None,
        span,
      ),
    )
    for field_index, projection in data_constructor.view().projections {
      if projection is Some(projection) && !projected.contains(projection) {
        projected[projection] = ()
        let field = fields[field_index]
        let target = @mlw.PVariable::trusted_new(
          self.context,
          @theory.SemanticName::new(b"self", [], span),
          result,
          false,
          span,
        )
        let projection_view = projection.view()
        let raw_projection_cty = @mlw.Cty::new(
          [target],
          [],
          [],
          [],
          [],
          @mlw.Effect::pure(field.view().ghost),
          field.view().ity,
          span,
        )
        projections.push(
          @mlw.RoutineSymbol::new_with_logic(
            self.context,
            projection_view.name,
            projection_view.origin,
            raw_projection_cty.add_postconditions(
              [
                routine_logic_postcondition(
                  self.context,
                  builder.pure_namespace(),
                  raw_projection_cty,
                  projection,
                  span,
                ),
              ],
              span,
            ),
            RLls(projection),
            Some(field),
            span,
          ),
        )
      }
    }
  }
  (projections, constructors)
}

///|
fn ProgramTyping::simple_program_type_declaration(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  declaration : @parser.TypeDecl,
) -> @mlw.ProgramTypeDeclaration raise {
  let span = Some(source_span(declaration.span))
  let pure_symbol = builder
    .pure_namespace()
    .find_type([declaration.ident.name], span)
  let origin = user_origin(declaration.ident)
  match declaration.definition {
    TDalias(target) => {
      let symbol = @mlw.ProgramTypeSymbol::new_alias(
        self.context,
        pure_symbol,
        origin,
        self.program_ity(
          builder.pure_namespace(),
          builder.program_namespace(),
          target,
          span,
        ),
        span,
      )
      @mlw.ProgramTypeDeclaration::simple(symbol)
    }
    TDrange(lower, upper) =>
      @mlw.ProgramTypeDeclaration::simple(
        @mlw.ProgramTypeSymbol::new_range(
          self.context,
          pure_symbol,
          origin,
          lower,
          upper,
          span,
        ),
      )
    TDfloat(exponent_digits, significand_digits) =>
      @mlw.ProgramTypeDeclaration::simple(
        @mlw.ProgramTypeSymbol::new_float(
          self.context,
          pure_symbol,
          origin,
          exponent_digits.to_int(),
          significand_digits.to_int(),
          span,
        ),
      )
    TDalgebraic(cases) => {
      let named_fields : Map[Bytes, @mlw.PVariable] = Map([])
      let constructor_fields : Array[Array[@mlw.PVariable]] = []
      for case_ in cases {
        let fields : Array[@mlw.PVariable] = []
        for parameter in case_.params {
          let field = match parameter.ident {
            Some(ident) =>
              match named_fields.get(ident.name) {
                Some(field) => field
                None => {
                  let field = self.new_type_field(
                    builder,
                    Some(ident),
                    parameter.span,
                    parameter.param_type,
                    parameter.ghost,
                  )
                  named_fields[ident.name] = field
                  field
                }
              }
            None =>
              self.new_type_field(
                builder,
                None,
                parameter.span,
                parameter.param_type,
                parameter.ghost,
              )
          }
          fields.push(field)
        }
        constructor_fields.push(fields)
      }
      let symbol = @mlw.ProgramTypeSymbol::new_variant(
        self.context,
        pure_symbol,
        origin,
        constructor_fields,
        span,
      )
      let (fields, constructors) = self.make_program_type_routines(
        builder, symbol, constructor_fields, span,
      )
      @mlw.ProgramTypeDeclaration::new(symbol, fields, constructors, [], span)
    }
    TDrecord(fields) => {
      if fields.is_empty() {
        let symbol = @mlw.ProgramTypeSymbol::new_record(
          self.context,
          pure_symbol,
          origin,
          declaration.visibility != Public,
          false,
          [],
          [],
          [],
          span,
        )
        return @mlw.ProgramTypeDeclaration::simple(symbol)
      }
      let mutable_fields : Array[@mlw.PVariable] = []
      let immutable_fields : Array[@mlw.PVariable] = []
      let constructor_fields : Array[@mlw.PVariable] = []
      for field in fields {
        let variable = self.new_type_field(
          builder,
          Some(field.ident),
          field.span,
          field.field_type,
          field.ghost,
        )
        constructor_fields.push(variable)
        if field.mutable {
          mutable_fields.push(variable)
        } else {
          immutable_fields.push(variable)
        }
      }
      let symbol = @mlw.ProgramTypeSymbol::new_record(
        self.context,
        pure_symbol,
        origin,
        declaration.visibility != Public,
        declaration.mutable,
        mutable_fields,
        immutable_fields,
        [],
        span,
      )
      let (projection_routines, constructors) = self.make_program_type_routines(
        builder,
        symbol,
        [constructor_fields],
        span,
      )
      @mlw.ProgramTypeDeclaration::new(
        symbol,
        projection_routines,
        constructors,
        [],
        span,
      )
    }
  }
}

///|
fn add_program_record_model_metas(
  builder : @mlw.PmoduleBuilder,
  declarations : ArrayView[@parser.TypeDecl],
  program_declarations : ArrayView[@mlw.ProgramTypeDeclaration],
) -> Unit raise {
  let projections : Array[@logic.LSymbol] = []
  for index, declaration in declarations {
    guard declaration.definition is TDrecord(_) else { continue }
    for routine in program_declarations[index].view().fields {
      guard routine.view().logic is RLls(projection) else {
        @logic.fail_type(
          InvalidDeclaration,
          Some(source_span(declaration.span)),
          "record projection routine has no logical symbol",
        )
      }
      if !projections.contains(projection) {
        projections.push(projection)
      }
    }
  }
  let span = if declarations.is_empty() {
    None
  } else {
    Some(source_span(declarations[0].span))
  }
  for projection in projections.rev() {
    builder.add_meta(
      @theory.Meta::new(b"model_record", [MetaLogicSymbol(projection)]),
      span,
    )
  }
}

///|
fn ProgramTyping::add_simple_program_types(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  declarations : ArrayView[@parser.TypeDecl],
) -> Unit raise {
  let checkpoint = builder.pure_elaboration_checkpoint()
  let pure_builder = builder.pure_elaboration_builder()
  for declaration in declarations {
    match declaration.definition {
      TDalgebraic(_) =>
        self.pure.add_program_data_type_declaration(pure_builder, declaration)
      TDrecord(fields) if !fields.is_empty() =>
        self.pure.add_program_data_type_declaration(pure_builder, declaration)
      _ => self.pure.add_type_declaration(pure_builder, declaration)
    }
  }
  let end = pure_builder.item_count()
  let pure_declarations : Array[@logic.Decl] = []
  let metas : Array[@theory.Meta] = []
  for index = checkpoint; index < end; index = index + 1 {
    match pure_builder.item_at(index, None) {
      TheoryDecl(declaration) => pure_declarations.push(declaration)
      TheoryMeta(meta) => metas.push(meta)
      TheoryUse(_) | TheoryClone(_) =>
        @logic.fail_type(
          InvalidDeclaration,
          None,
          "type elaboration unexpectedly introduced a use or clone item",
        )
    }
  }
  let program_declarations : Array[@mlw.ProgramTypeDeclaration] = []
  for declaration in declarations {
    program_declarations.push(
      self.simple_program_type_declaration(builder, declaration),
    )
  }
  builder.add_existing_type_declarations(
    program_declarations,
    pure_declarations,
    metas,
    if declarations.is_empty() {
      None
    } else {
      Some(source_span(declarations[0].span))
    },
  )
  add_program_record_model_metas(builder, declarations, program_declarations)
}

///|
fn ProgramTyping::recursive_constructor_fields(
  self : ProgramTyping,
  pure_space : @theory.Namespace,
  program_space : @mlw.ProgramNamespace,
  declaration : @parser.TypeDecl,
) -> Array[Array[@mlw.PVariable]] raise {
  match declaration.definition {
    TDalgebraic(cases) => {
      let named_fields : Map[Bytes, @mlw.PVariable] = Map([])
      [
        for case_ in cases => {
          [
            for parameter in case_.params => {
              match parameter.ident {
                Some(ident) =>
                  match named_fields.get(ident.name) {
                    Some(field) => field
                    None => {
                      let field = self.new_type_field_in_spaces(
                        pure_space,
                        program_space,
                        Some(ident),
                        parameter.span,
                        parameter.param_type,
                        parameter.ghost,
                      )
                      named_fields[ident.name] = field
                      field
                    }
                  }
                None =>
                  self.new_type_field_in_spaces(
                    pure_space,
                    program_space,
                    None,
                    parameter.span,
                    parameter.param_type,
                    parameter.ghost,
                  )
              }
            }
          ]
        }
      ]
    }
    TDrecord(fields) =>
      [
        [
          for field in fields => {
            self.new_type_field_in_spaces(
              pure_space,
              program_space,
              Some(field.ident),
              field.span,
              field.field_type,
              field.ghost,
            )
          }
        ],
      ]
    _ => abort("non-data type passed recursive program elaboration")
  }
}

///|
fn ProgramTyping::add_recursive_program_types(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  declarations : ArrayView[@parser.TypeDecl],
) -> Unit raise {
  let checkpoint = builder.pure_elaboration_checkpoint()
  let pure_builder = builder.pure_elaboration_builder()
  if declarations.length() == 1 {
    self.pure.add_program_data_type_declaration(pure_builder, declarations[0])
  } else {
    self.pure.add_recursive_data_group(
      pure_builder,
      declarations,
      allow_program_fields=true,
    )
  }
  let pure_space = builder.pure_namespace()
  let program_symbols : Array[@mlw.ProgramTypeSymbol?] = [
    for _ in declarations => None
  ]
  let mut recursive_space = @mlw.ProgramNamespace::empty()
  for index, declaration in declarations {
    if declaration.definition is TDalias(_) {
      continue
    }
    let span = Some(source_span(declaration.span))
    let pure_symbol = pure_space.find_type([declaration.ident.name], span)
    let program_symbol = @mlw.ProgramTypeSymbol::new_recursive(
      self.context,
      pure_symbol,
      user_origin(declaration.ident),
      span,
    )
    program_symbols[index] = Some(program_symbol)
    recursive_space = recursive_space.add_type(
      declaration.ident.name,
      program_symbol,
      span,
    )
  }

  let mut unresolved : Array[Int] = []
  for index, declaration in declarations {
    if declaration.definition is TDalias(_) {
      unresolved.push(index)
    }
  }
  while !unresolved.is_empty() {
    let pending_names = unresolved.map(index => declarations[index].ident.name)
    let next : Array[Int] = []
    let mut progress = false
    for index in unresolved {
      let declaration = declarations[index]
      guard declaration.definition is TDalias(target) else {
        abort("non-alias remained in recursive program alias resolution")
      }
      if pty_mentions_pending_type(target, pending_names) {
        next.push(index)
        continue
      }
      let span = Some(source_span(declaration.span))
      let program_space = builder.program_namespace().overlay(recursive_space)
      let program_symbol = @mlw.ProgramTypeSymbol::new_alias(
        self.context,
        pure_space.find_type([declaration.ident.name], span),
        user_origin(declaration.ident),
        self.program_ity(pure_space, program_space, target, span),
        span,
      )
      program_symbols[index] = Some(program_symbol)
      recursive_space = recursive_space.add_type(
        declaration.ident.name,
        program_symbol,
        span,
      )
      progress = true
    }
    if !progress {
      @logic.fail_type(
        InvalidDeclaration,
        Some(source_span(declarations[unresolved[0]].span)),
        "recursive program aliases do not reach a concrete data type",
      )
    }
    unresolved = next
  }

  let program_space = builder.program_namespace().overlay(recursive_space)
  let program_declarations : Array[@mlw.ProgramTypeDeclaration] = []
  for index = 0; index < declarations.length(); index = index + 1 {
    let declaration = declarations[index]
    let span = Some(source_span(declaration.span))
    guard program_symbols[index] is Some(program_symbol) else {
      abort("recursive program type symbol was not initialized")
    }
    if declaration.definition is TDalias(_) {
      program_declarations.push(
        @mlw.ProgramTypeDeclaration::simple(program_symbol),
      )
      continue
    }
    let constructor_fields = self.recursive_constructor_fields(
      pure_space, program_space, declaration,
    )
    let (projections, constructors) = self.make_program_type_routines(
      builder, program_symbol, constructor_fields, span,
    )
    program_declarations.push(
      @mlw.ProgramTypeDeclaration::trusted_new(
        program_symbol,
        projections,
        constructors,
        [],
        span,
      ),
    )
  }
  let pure_declarations : Array[@logic.Decl] = []
  let metas : Array[@theory.Meta] = []
  for index = checkpoint; index < pure_builder.item_count(); index = index + 1 {
    match pure_builder.item_at(index, None) {
      TheoryDecl(declaration) => pure_declarations.push(declaration)
      TheoryMeta(meta) => metas.push(meta)
      TheoryUse(_) | TheoryClone(_) =>
        @logic.fail_type(
          InvalidDeclaration,
          None,
          "type elaboration unexpectedly introduced a use or clone item",
        )
    }
  }
  builder.add_existing_type_declarations(
    program_declarations,
    pure_declarations,
    metas,
    Some(source_span(declarations[0].span)),
  )
  add_program_record_model_metas(builder, declarations, program_declarations)
}

///|
fn ProgramTyping::record_invariants(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  declaration : @parser.TypeDecl,
  fields : ArrayView[(@parser.Field, @mlw.PVariable)],
) -> Array[@logic.Term] raise {
  if declaration.invariant.terms.is_empty() {
    return []
  }
  self.pure.sync_known(builder.pure_known())
  let locals : Array[(Bytes, DLocal)] = []
  let values : Array[(Int, @logic.VSymbol)] = []
  for entry in fields {
    let (field, variable) = entry
    let span = Some(source_span(field.span))
    let delayed = self.pure.delayed.known(
      variable.view().pure_symbol.ty(),
      span,
    )
    let binding = self.pure.make_local(Some(field.ident), field.span, delayed)
    locals.push((field.ident.name, binding))
    values.push((binding.id, variable.view().pure_symbol))
  }
  [
    for invariant in declaration.invariant.terms => {
      self.pure.formula(builder.pure_namespace(), locals, values, invariant)
    }
  ]
}

///|
fn ProgramTyping::add_record_invariant_axiom(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  declaration : @parser.TypeDecl,
  pure_symbol : @logic.TypeSymbol,
  fields : ArrayView[(@parser.Field, @mlw.PVariable)],
  projections : ArrayView[@logic.LSymbol],
  invariants : ArrayView[@logic.Term],
) -> Unit raise {
  if invariants.is_empty() {
    return
  }
  let span = Some(source_span(declaration.span))
  let (identifier_span, identifier_attributes) = ident_parts(declaration.ident)
  let identifier_span = Some(identifier_span)
  let record_type = @logic.Ty::app(
    pure_symbol,
    pure_symbol.view().parameters.map(@logic.Ty::variable),
    span,
  )
  let self_variable = @logic.VSymbol::new(
    self.context,
    b"self",
    @identity.Origin::user(b"self", None, []),
    record_type,
    None,
  )
  let mut substitution = @logic.TermSubstitution::new()
  for index = 0; index < fields.length(); index = index + 1 {
    substitution = substitution.bind(
      fields[index].1.view().pure_symbol,
      @logic.Term::apply_function(
        projections[index],
        [@logic.Term::variable(self_variable)],
        span,
      ),
      span,
    )
  }
  let invariant_variables : Array[@logic.VSymbol] = []
  for invariant in invariants {
    for variable in invariant.free_variables() {
      if !invariant_variables.contains(variable) {
        invariant_variables.push(variable)
      }
    }
  }
  let trigger_fields : Array[Int] = []
  for index, field in fields {
    if invariant_variables.contains(field.1.view().pure_symbol) {
      trigger_fields.push(index)
    }
  }
  trigger_fields.sort_by((left, right) => {
    fields[right].1.view().pure_symbol
    .semantic_id()
    .local_id()
    .compare(fields[left].1.view().pure_symbol.semantic_id().local_id())
  })
  let triggers : Array[Array[@logic.Term]] = []
  for index in trigger_fields {
    triggers.push([
      @logic.Term::apply_function(
        projections[index],
        [@logic.Term::variable(self_variable)],
        None,
      ),
    ])
  }
  let mut body = substitution.apply(self.context, invariants[0], span)
  for index = 1; index < invariants.length(); index = index + 1 {
    body = @logic.Term::binary(
      And,
      body,
      substitution.apply(self.context, invariants[index], span),
      span,
    )
  }
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    [self_variable],
    triggers,
    body,
    span,
  )
  let name = declaration.ident.name + b"'invariant"
  let origin = @identity.Origin::user(
    name, identifier_span, identifier_attributes,
  )
  builder
  .pure_elaboration_builder()
  .add_decl(
    @logic.Decl::proposition(
      self.context,
      origin,
      @logic.Paxiom,
      @logic.PrSymbol::new(self.context, name, origin),
      formula,
      identifier_span,
    ),
    identifier_span,
  )
}

///|
fn type_witness_ghost_value(value : @parser.Expr, ghost : Bool) -> @parser.Expr {
  if ghost {
    { ..value, desc: Eghost(value) }
  } else {
    value
  }
}

///|
fn type_witness_record_tuple(
  source : @parser.Expr,
  fields : ArrayView[(@parser.Field, @mlw.PVariable)],
) -> @parser.Expr raise {
  guard source.desc is Erecord(source_values) else { return source }
  let ordered : Array[@parser.Expr] = []
  let used : Array[Bytes] = []
  for entry in fields {
    let field_name = entry.0.ident.name
    let mut value : @parser.Expr? = None
    for source_value in source_values {
      if qualid_last(source_value.0).name == field_name {
        if value is Some(_) {
          @logic.fail_type(
            BadRecordField,
            Some(qualid_span(source_value.0)),
            "type witness repeats a record field",
          )
        }
        value = Some(source_value.1)
      }
    }
    guard value is Some(value) else {
      @logic.fail_type(
        RecordFieldMissing,
        Some(source_span(source.span)),
        "type witness omits a record field",
      )
    }
    used.push(field_name)
    ordered.push(type_witness_ghost_value(value, entry.1.view().ghost))
  }
  for source_value in source_values {
    let name = qualid_last(source_value.0).name
    if !used.any(field => field == name) {
      @logic.fail_type(
        BadRecordField,
        Some(qualid_span(source_value.0)),
        "type witness contains an unknown record field",
      )
    }
  }
  { ..source, desc: Etuple(ordered) }
}

///|
fn convert_type_witness_result(
  source : @parser.Expr,
  fields : ArrayView[(@parser.Field, @mlw.PVariable)],
) -> @parser.Expr raise {
  let desc : @parser.ExprDesc = match source.desc {
    Erecord(_) => return type_witness_record_tuple(source, fields)
    Escope(scope, body) =>
      Escope(scope, convert_type_witness_result(body, fields))
    Eexn(name, payload, mask, body) =>
      Eexn(name, payload, mask, convert_type_witness_result(body, fields))
    Eoptexn(name, mask, body) =>
      Eoptexn(name, mask, convert_type_witness_result(body, fields))
    Ematch(scrutinee, regular, exceptional) =>
      Ematch(
        scrutinee,
        regular.map(branch => {
          ..branch,
          body: convert_type_witness_result(branch.body, fields),
        }),
        exceptional.map(branch => {
          ..branch,
          body: convert_type_witness_result(branch.body, fields),
        }),
      )
    Erec(definitions, body) =>
      Erec(definitions, convert_type_witness_result(body, fields))
    Elabel(label, body) =>
      Elabel(label, convert_type_witness_result(body, fields))
    Eattr(attribute, body) =>
      Eattr(attribute, convert_type_witness_result(body, fields))
    Eghost(body) => Eghost(convert_type_witness_result(body, fields))
    Ecast(body, annotation) =>
      Ecast(convert_type_witness_result(body, fields), annotation)
    Esequence(first, body) =>
      Esequence(first, convert_type_witness_result(body, fields))
    Eif(condition, consequent, alternative) =>
      Eif(
        condition,
        convert_type_witness_result(consequent, fields),
        convert_type_witness_result(alternative, fields),
      )
    Elet(name, ghost, kind, value, body) =>
      Elet(name, ghost, kind, value, convert_type_witness_result(body, fields))
    _ => return source
  }
  { ..source, desc, }
}

///|
fn type_witness_tuple_ity(
  builder : @mlw.PmoduleBuilder,
  fields : ArrayView[(@parser.Field, @mlw.PVariable)],
  span : @identity.SourceSpan?,
) -> @mlw.Ity raise {
  if fields.is_empty() {
    return @mlw.Ity::instantiate(
      builder.program_namespace().find_type([b"unit"], span),
      [],
      [],
      span,
    )
  }
  @mlw.Ity::app(
    builder
    .program_namespace()
    .find_type([tuple_type_name(fields.length())], span),
    fields.map(entry => entry.1.view().ity),
    span,
  )
}

///|
fn ProgramTyping::data_backed_nonfree_record_type_declaration(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  declaration : @parser.TypeDecl,
  pure_symbol : @logic.TypeSymbol,
) -> @mlw.ProgramTypeDeclaration raise {
  guard declaration.definition is TDrecord(source_fields) else {
    abort("non-record type passed data-backed record elaboration")
  }
  let span = Some(source_span(declaration.span))
  let fields : Array[(@parser.Field, @mlw.PVariable)] = []
  let mutable_fields : Array[@mlw.PVariable] = []
  let immutable_fields : Array[@mlw.PVariable] = []
  for field in source_fields {
    let variable = self.new_type_field(
      builder,
      Some(field.ident),
      field.span,
      field.field_type,
      field.ghost,
    )
    fields.push((field, variable))
    if field.mutable {
      mutable_fields.push(variable)
    } else {
      immutable_fields.push(variable)
    }
  }
  let invariants = self.record_invariants(builder, declaration, fields)
  let symbol = @mlw.ProgramTypeSymbol::new_record(
    self.context,
    pure_symbol,
    user_origin(declaration.ident),
    false,
    declaration.mutable,
    mutable_fields,
    immutable_fields,
    invariants,
    span,
  )
  let (projection_routines, constructors) = self.make_program_type_routines(
    builder,
    symbol,
    [fields.map(entry => entry.1)],
    span,
  )
  self.add_record_invariant_axiom(
    builder,
    declaration,
    pure_symbol,
    fields,
    projection_routines.map(routine => {
      guard routine.view().logic is RLls(projection) else {
        abort("record projection routine lost its logical symbol")
      }
      projection
    }),
    invariants,
  )
  let witness = match declaration.witness {
    None => None
    Some(source) => {
      let converted = convert_type_witness_result(source, fields)
      Some(
        self.type_program_expression_expected(
          builder.pure_namespace(),
          builder.program_namespace(),
          [],
          converted,
          Some(type_witness_tuple_ity(builder, fields, span)),
        ),
      )
    }
  }
  @mlw.ProgramTypeDeclaration::new(
    symbol,
    projection_routines,
    constructors,
    invariants,
    span,
    witness~,
  )
}

///|
fn ProgramTyping::nonfree_record_type_declaration(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  declaration : @parser.TypeDecl,
  pure_symbol : @logic.TypeSymbol,
) -> @mlw.ProgramTypeDeclaration raise {
  guard declaration.definition is TDrecord(source_fields) else {
    abort("non-record type passed nonfree record elaboration")
  }
  let span = Some(source_span(declaration.span))
  let result_type = @logic.Ty::app(
    pure_symbol,
    pure_symbol.view().parameters.map(@logic.Ty::variable),
    span,
  )
  let fields : Array[(@parser.Field, @mlw.PVariable)] = []
  let mutable_fields : Array[@mlw.PVariable] = []
  let immutable_fields : Array[@mlw.PVariable] = []
  let projections : Array[@logic.LSymbol] = []
  for field in source_fields {
    let variable = self.new_type_field(
      builder,
      Some(field.ident),
      field.span,
      field.field_type,
      field.ghost || declaration.visibility is Abstract,
    )
    fields.push((field, variable))
    if field.mutable {
      mutable_fields.push(variable)
    } else {
      immutable_fields.push(variable)
    }
    // Fields of a private/non-free program record are not algebraic
    // projections in the pure theory.  Why3 gives their logical functions
    // the field attributes, while keeping `ls_proj = false`; the routine's
    // `rs_field` still records the program projection relationship.
    let projection = @logic.LSymbol::new_function(
      self.context,
      field.ident.name,
      user_origin_with_attributes(field.ident, [b"is_field_id", b"builtin"]),
      [result_type],
      variable.view().pure_symbol.ty(),
      Some(source_span(field.span)),
    )
    projections.push(projection)
    builder
    .pure_elaboration_builder()
    .add_decl(
      @logic.Decl::parameter(
        self.context,
        // Why3's abstract-record projection declaration reuses the
        // projection identifier, including `builtin` / `is_field_id`.
        projection.view().origin,
        projection,
        Some(source_span(field.span)),
      ),
      Some(source_span(field.span)),
    )
  }
  let invariants = self.record_invariants(builder, declaration, fields)
  let symbol = @mlw.ProgramTypeSymbol::new_record(
    self.context,
    pure_symbol,
    user_origin(declaration.ident),
    declaration.visibility != Public,
    declaration.mutable,
    mutable_fields,
    immutable_fields,
    invariants,
    span,
  )
  let projection_routines : Array[@mlw.RoutineSymbol] = []
  for index = 0; index < fields.length(); index = index + 1 {
    let field = fields[index].1
    // Why3's `create_projection` calls `ity_app` independently for every
    // field. Mutable record applications therefore receive a distinct fresh
    // top region in each projection signature.
    let result = @mlw.Ity::instantiate(
      symbol,
      make_type_argument_ities(pure_symbol),
      symbol.view().regions.map(@mlw.Ity::region),
      span,
    )
    let target = @mlw.PVariable::trusted_new(
      self.context,
      @theory.SemanticName::new(b"self", [], span),
      result,
      false,
      span,
    )
    let projection = projections[index]
    let raw_projection_cty = @mlw.Cty::new(
      [target],
      [],
      [],
      [],
      [],
      @mlw.Effect::pure(field.view().ghost),
      field.view().ity,
      span,
    )
    projection_routines.push(
      @mlw.RoutineSymbol::new_with_logic(
        self.context,
        projection.view().name,
        projection.view().origin,
        raw_projection_cty.add_postconditions(
          [
            routine_logic_postcondition(
              self.context,
              builder.pure_namespace(),
              raw_projection_cty,
              projection,
              span,
            ),
          ],
          span,
        ),
        RLls(projection),
        Some(field),
        span,
      ),
    )
  }
  let constructors : Array[@mlw.RoutineSymbol] = []
  if declaration.visibility == Public && !invariants.is_empty() {
    let result = @mlw.Ity::instantiate(
      symbol,
      make_type_argument_ities(pure_symbol),
      symbol.view().regions.map(@mlw.Ity::region),
      span,
    )
    let result_symbol = @logic.VSymbol::new(
      self.context,
      b"result",
      @identity.Origin::user(b"result", None, [b"mlw:proxy_symbol"]),
      result.to_ty(span),
      None,
    )
    let result_term = @logic.Term::variable(result_symbol)
    let equality = builder.pure_namespace().find_logic([b"infix ="], span)
    let equations : Array[@logic.Term] = []
    for index, field in fields {
      equations.push(
        @logic.Term::elaborated_apply(
          equality,
          [
            @logic.Term::elaborated_apply(
              projections[index],
              [result_term],
              projections[index].view().result_type,
              None,
            ),
            @logic.Term::variable(field.1.view().pure_symbol),
          ],
          None,
          None,
        ),
      )
    }
    let postcondition = @mlw.Postcondition::trusted_new(
      result_symbol,
      conjoin_program_formulas(equations, None),
      span,
    )
    let effect = match result.view() {
      ItyReg(region) => @mlw.Effect::pure(false).reset([region], span)
      ItyVar(_) | ItyApp(_, _, _) => @mlw.Effect::pure(false)
    }
    let constructor_cty = @mlw.Cty::new(
      fields.map(entry => entry.1),
      invariants,
      [postcondition],
      [],
      [],
      effect,
      result,
      span,
    )
    let constructor_name = declaration.ident.name + b"'mk"
    let constructor_span = Some(source_span(declaration.ident.span))
    let constructor_origin = @identity.Origin::user(
      constructor_name,
      constructor_span,
      [b"builtin"],
    )
    constructors.push(
      @mlw.RoutineSymbol::new_with_logic(
        self.context,
        constructor_name,
        constructor_origin,
        constructor_cty,
        RLnone,
        None,
        constructor_span,
      ),
    )
  }
  self.add_record_invariant_axiom(
    builder, declaration, pure_symbol, fields, projections, invariants,
  )
  let witness = match declaration.witness {
    None => None
    Some(source) => {
      let converted = convert_type_witness_result(source, fields)
      Some(
        self.type_program_expression_expected(
          builder.pure_namespace(),
          builder.program_namespace(),
          [],
          converted,
          Some(
            type_witness_tuple_ity(
              builder,
              fields,
              Some(source_span(source.span)),
            ),
          ),
        ),
      )
    }
  }
  @mlw.ProgramTypeDeclaration::new(
    symbol,
    projection_routines,
    constructors,
    invariants,
    span,
    witness~,
  )
}

///|
fn ProgramTyping::add_nonfree_record_types(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  declarations : ArrayView[@parser.TypeDecl],
) -> Unit raise {
  let checkpoint = builder.pure_elaboration_checkpoint()
  let pure_symbols : Array[@logic.TypeSymbol] = []
  for declaration in declarations {
    let span = Some(source_span(declaration.span))
    if data_backed_nonfree_record(declaration) {
      self.pure.add_program_data_type_declaration(
        builder.pure_elaboration_builder(),
        declaration,
      )
      pure_symbols.push(
        builder.pure_namespace().find_type([declaration.ident.name], span),
      )
    } else {
      let symbol = @logic.TypeSymbol::new_abstract(
        self.context,
        declaration.ident.name,
        user_origin(declaration.ident),
        self.pure.type_parameters(declaration.params),
        span,
      )
      pure_symbols.push(symbol)
      builder
      .pure_elaboration_builder()
      .add_decl(
        @logic.Decl::type_declaration(
          self.context,
          user_origin(declaration.ident),
          [symbol],
          span,
        ),
        span,
      )
    }
  }
  let program_declarations : Array[@mlw.ProgramTypeDeclaration] = []
  for index = 0; index < declarations.length(); index = index + 1 {
    program_declarations.push(
      if data_backed_nonfree_record(declarations[index]) {
        self.data_backed_nonfree_record_type_declaration(
          builder,
          declarations[index],
          pure_symbols[index],
        )
      } else {
        self.nonfree_record_type_declaration(
          builder,
          declarations[index],
          pure_symbols[index],
        )
      },
    )
  }
  let pure_builder = builder.pure_elaboration_builder()
  let pure_declarations : Array[@logic.Decl] = []
  let metas : Array[@theory.Meta] = []
  for index = checkpoint; index < pure_builder.item_count(); index = index + 1 {
    match pure_builder.item_at(index, None) {
      TheoryDecl(declaration) => pure_declarations.push(declaration)
      TheoryMeta(meta) => metas.push(meta)
      TheoryUse(_) | TheoryClone(_) =>
        @logic.fail_type(
          InvalidDeclaration,
          None,
          "type elaboration unexpectedly introduced a use or clone item",
        )
    }
  }
  builder.add_existing_type_declarations(
    program_declarations,
    pure_declarations,
    metas,
    Some(source_span(declarations[0].span)),
  )
  add_program_record_model_metas(builder, declarations, program_declarations)
}

///|
fn ProgramTyping::add_module_declaration(
  self : ProgramTyping,
  builder : @mlw.PmoduleBuilder,
  declaration : @parser.Decl,
) -> Unit raise {
  for arity in tuple_declaration_dependencies(declaration) {
    if arity > 0 {
      let tuple_module = self.environment.tuple_module(arity)
      if builder
        .pure_elaboration_builder()
        .knows_theory(tuple_module.pure_theory()) {
        builder.add_hidden_use(tuple_module, None)
      } else {
        builder.add_use(tuple_module, true, None)
      }
    }
  }
  if reference_declaration_dependency(declaration) {
    let reference_module = self.environment.reference_module()
    if builder
      .pure_elaboration_builder()
      .knows_theory(reference_module.pure_theory()) {
      builder.add_hidden_use(reference_module, None)
    } else {
      builder.add_use(reference_module, true, None)
    }
  }
  let high_order = self.environment.high_order_module()
  let function_type = high_order
    .pure_theory()
    .export_namespace()
    .find_type([b"infix ->"], None)
  let direct_high_order = high_order_declaration_dependency(declaration)
  let signature_high_order = signature_high_order_declaration_dependency(
    declaration,
  )
  let indirect_high_order = !direct_high_order &&
    application_declaration_dependency(declaration) &&
    (
      builder.pure_coercions().has_target_symbol(function_type) ||
      self.pure.declaration_applies_function_typed_parameter(
        builder.pure_namespace(),
        declaration,
        function_type,
        builder.pure_coercions(),
      )
    )
  if direct_high_order || indirect_high_order {
    let high_order_pure = high_order.pure_theory().export_namespace()
    let application = high_order_pure.find_logic([b"infix @"], None)
    let application_routine = high_order
      .export_namespace()
      .find_routine([b"infix @"], None)
    let pure_available = try
      builder.pure_namespace().find_logic([b"infix @"], None) == application
    catch {
      _ => false
    }
    let program_available = builder
      .program_namespace()
      .find_routine_candidates([b"infix @"])
      .any(candidate => candidate == application_routine)
    if !pure_available || !program_available {
      if builder
        .pure_elaboration_builder()
        .knows_theory(high_order.pure_theory()) {
        builder.add_hidden_use(high_order, None)
      } else if signature_high_order {
        builder.add_use(high_order, true, None)
      } else {
        builder.add_hidden_use(high_order, None)
      }
    }
  }
  self.pure.sync_known(builder.pure_known())
  self.pure.sync_coercions(builder.pure_coercions())
  match declaration {
    Dlet(ident, ghost, kind, expression) =>
      self.add_top_level_routine(builder, ident, ghost, kind, expression)
    Duseexport(qualid) =>
      builder.add_use(
        resolve_used_module(
          self.environment,
          self.library_path,
          self.file_modules,
          qualid,
        ),
        true,
        Some(qualid_span(qualid)),
      )
    Duseimport(span, import_, uses) =>
      for use_ in uses {
        let (qualid, renaming) = use_
        let scope_name = match renaming {
          Some(renaming) => renaming.name
          None => qualid_last(qualid).name
        }
        builder.add_scoped_use(
          scope_name,
          resolve_used_module(
            self.environment,
            self.library_path,
            self.file_modules,
            qualid,
          ),
          import_ || renaming is None,
          Some(source_span(span)),
        )
      }
    Drec(sources) => {
      let (definitions, _, pure_declarations) = self.type_recursive_routines(
        builder.pure_namespace(),
        builder.program_namespace(),
        [],
        sources,
      )
      builder.add_recursive_decl(
        definitions,
        pure_declarations,
        if sources.is_empty() {
          None
        } else {
          Some(source_span(sources[0].name.span))
        },
      )
    }
    Dexn(ident, payload, mask) => {
      let span = Some(source_span(ident.span))
      let exception = @mlw.XSymbol::new(
        self.context,
        semantic_name(ident),
        self.program_ity(
          builder.pure_namespace(),
          builder.program_namespace(),
          payload,
          span,
        ),
        span,
        mask=semantic_program_mask(mask),
      )
      builder.add_exception_decl(exception, [], span)
    }
    Dprop(kind, ident, body) => {
      let span = Some(source_span(ident.span))
      builder.add_pure_proposition(
        self.pure.proposition_declaration(
          builder.pure_namespace(),
          kind,
          ident,
          body,
        ),
        span,
      )
    }
    Dmeta(ident, arguments) => {
      let span = Some(source_span(ident.span))
      builder.add_meta(
        self.pure.user_meta(
          builder.pure_namespace(),
          builder.pure_known(),
          ident,
          arguments,
          program_space=Some(builder.program_namespace()),
        ),
        span,
      )
    }
    Dind(_, _) | Dlogic(_) => {
      let checkpoint = builder.pure_elaboration_checkpoint()
      self.pure.add_declaration(builder.pure_elaboration_builder(), declaration)
      builder.finish_pure_elaboration(
        checkpoint,
        match declaration {
          Dind(_, declarations) =>
            if declarations.is_empty() {
              None
            } else {
              Some(source_span(declarations[0].span))
            }
          Dlogic(declarations) =>
            if declarations.is_empty() {
              None
            } else {
              Some(source_span(declarations[0].span))
            }
          _ => None
        },
      )
    }
    Dcloneexport(source_span_, source, substitutions) =>
      self.add_program_clone(
        builder,
        source,
        substitutions,
        Some(source_span(source_span_)),
      )
    Dcloneimport(source_span_, import_, source, alias_name, substitutions) => {
      let scope_ident = match alias_name {
        Some(alias_name) => alias_name
        None => qualid_last(source)
      }
      let span = Some(source_span(source_span_))
      builder.open_scope(scope_ident.name, span)
      self.add_program_clone(builder, source, substitutions, span)
      builder.close_scope(import_ || alias_name is None, span)
    }
    Dtype(declarations) =>
      if simple_program_type_group(declarations) {
        self.add_simple_program_types(builder, declarations)
      } else if nonfree_record_type_group(declarations) {
        self.add_nonfree_record_types(builder, declarations)
      } else if recursive_program_type_group(declarations) {
        self.add_recursive_program_types(builder, declarations)
      } else {
        fail_invalid_input(
          InvalidTypeDeclaration,
          ProgramTyping,
          if declarations.is_empty() {
            None
          } else {
            Some(source_span(declarations[0].span))
          },
          "recursive, stateful, private, ghost, invariant, or witnessed program type",
        )
      }
    Dimport(qualid) =>
      builder.import_scope(qualid_segments(qualid), Some(qualid_span(qualid)))
    Dscope(span, import_, ident, declarations) => {
      let semantic_span = Some(source_span(span))
      builder.open_scope(ident.name, semantic_span)
      for declaration in declarations {
        self.add_module_declaration(builder, declaration)
      }
      builder.close_scope(import_, semantic_span)
    }
  }
}

///|
fn add_implicit_program_prelude(
  environment : @environment.Environment,
  builder : @mlw.PmoduleBuilder,
) -> Unit raise {
  for name in [b"BuiltIn", b"Bool", b"Unit"] {
    let key = @theory.TheoryKey::new([], name)
    builder.add_use(environment.resolve_module(key, None), true, None)
  }
}

///|
fn elaborate_program_unit_raw(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  unit : @parser.MlwModule,
) -> @mlw.Pmodule raise {
  elaborate_program_unit_at_path_raw(context, environment, unit, [], [], [])
}

///|
fn elaborate_program_unit_at_path_raw(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  unit : @parser.MlwModule,
  path : ArrayView[Bytes],
  file_theories : ArrayView[(Bytes, @theory.Theory)],
  file_modules : ArrayView[(Bytes, @mlw.Pmodule)],
) -> @mlw.Pmodule raise {
  if unit.kind != Module {
    fail_invalid_input(
      InvalidUnit,
      ProgramTyping,
      Some(source_span(unit.span)),
      "theory unit was sent to the program elaborator",
    )
  }
  let builder = @mlw.PmoduleBuilder::new(
    context,
    @theory.TheoryKey::new(path, unit.name.name),
    semantic_name(unit.name),
  )
  add_implicit_program_prelude(environment, builder)
  let typing = ProgramTyping::new(
    context,
    environment,
    library_path=path,
    file_theories~,
    file_modules~,
  )
  for declaration in unit.declarations {
    typing.add_module_declaration(builder, declaration)
  }
  let implementation = @vc.generate_type_module(context, builder.close())
  match unit.interface {
    None => implementation
    Some(interface_name) => {
      let interface_module = resolve_used_module(
        environment, path, file_modules, interface_name,
      )
      ignore(
        implementation.match_interface(
          interface_module,
          Some(qualid_span(interface_name)),
        ),
      )
      implementation
    }
  }
}

///|
fn[A] normalize_program_elaboration_errors(
  action : () -> A raise,
  type_stage? : ElabStage = ProgramTyping,
) -> A raise ElabError {
  action() catch {
    @logic.TypeError(diagnostic) => {
      let normalized = type_failure_diagnostic(diagnostic)
      raise ElabError({ ..normalized, stage: type_stage })
    }
    @theory.TheoryError(diagnostic) =>
      raise ElabError(theory_failure_diagnostic(diagnostic))
    @environment.EnvironmentError(diagnostic) =>
      raise ElabError(environment_failure_diagnostic(diagnostic, ProgramTyping))
    @env.SourceError(diagnostic) =>
      raise ElabError(source_failure_diagnostic(diagnostic, ProgramTyping))
    @mlw.MlwError(diagnostic) =>
      raise ElabError(program_failure_diagnostic(diagnostic))
    ElabError(diagnostic) => raise ElabError(diagnostic)
    _ => abort("unexpected program elaboration error escaped a typed boundary")
  }
}

///|
pub fn elaborate_program_unit(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  unit : @parser.MlwModule,
) -> @mlw.Pmodule raise ElabError {
  normalize_program_elaboration_errors(() => {
    elaborate_program_unit_raw(context, environment, unit)
  })
}

///|
pub(all) enum ElaboratedUnitView {
  ElaboratedTheory(@theory.Theory)
  ElaboratedModule(@mlw.Pmodule)
}

///|
struct ElaboratedFile {
  units : Array[ElaboratedUnitView]
  typed_library : @environment.TypedLibrary
}

///|
pub fn ElaboratedFile::units(
  self : ElaboratedFile,
) -> ArrayView[ElaboratedUnitView] {
  self.units[:]
}

///|
fn elaborate_file_raw(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  file : @parser.MlwFile,
) -> ElaboratedFile raise {
  elaborate_file_at_path_raw(context, environment, file, [])
}

///|
fn anonymous_top_module(
  declarations : ArrayView[@parser.Decl],
) -> @parser.MlwModule {
  let position = @parser.SourcePos::{
    filename: b"",
    byte_offset: 0,
    line: 1L,
    column: 0L,
  }
  let span = @parser.Span::{ start: position, end: position }
  {
    kind: Module,
    name: { name: b"Top", attributes: [], span },
    interface: None,
    declarations: declarations.to_owned(),
    span,
  }
}

///|
fn elaborate_file_at_path_raw(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  file : @parser.MlwFile,
  path : ArrayView[Bytes],
) -> ElaboratedFile raise {
  let source_units = match file {
    Modules(source_units) => source_units
    Decls(declarations) => {
      if !path.is_empty() {
        fail_invalid_input(
          InvalidUnit,
          FileRegistration,
          None,
          "library declarations must be enclosed in a module or theory",
        )
      }
      [anonymous_top_module(declarations)]
    }
  }
  let units : Array[ElaboratedUnitView] = []
  let file_theories : Array[(Bytes, @theory.Theory)] = []
  let file_modules : Array[(Bytes, @mlw.Pmodule)] = []
  for unit in source_units {
    match unit.kind {
      Theory => {
        // Why3's typing layer represents both source theories and source
        // modules as Pmodules. Keep the source-level distinction in
        // ElaboratedUnitView, while retaining the Pmodule counterpart so a
        // later module can `use` a preceding theory and library clients can
        // resolve pure-theory program symbols by semantic identity.
        let module_unit = @parser.MlwModule::{
          kind: Module,
          name: unit.name,
          interface: None,
          declarations: unit.declarations,
          span: unit.span,
        }
        let pre_vc_module = normalize_program_elaboration_errors(
          () => {
            elaborate_program_unit_at_path_raw(
              context, environment, module_unit, path, file_theories, file_modules,
            )
          },
          type_stage=PureTyping,
        )
        // Why3 generates top-level routine VCs while closing a source
        // `theory`. Source `module` records deliberately remain pre-WP and
        // receive their routine VCs later in the proof pipeline.
        let pmodule = normalize_program_elaboration_errors(
          () => @vc.generate_module(context, pre_vc_module),
          type_stage=PureTyping,
        )
        let theory = pmodule.pure_theory()
        file_theories.push((unit.name.name, theory))
        file_modules.push((unit.name.name, pmodule))
        units.push(ElaboratedTheory(theory))
      }
      Module => {
        let pmodule = normalize_program_elaboration_errors(() => {
          elaborate_program_unit_at_path_raw(
            context, environment, unit, path, file_theories, file_modules,
          )
        })
        file_theories.push((unit.name.name, pmodule.pure_theory()))
        file_modules.push((unit.name.name, pmodule))
        units.push(ElaboratedModule(pmodule))
      }
    }
  }
  let typed_library = @environment.TypedLibrary::new(
    file_theories, file_modules,
  )
  environment.register_typed_library(typed_library, true, None)
  { units, typed_library }
}

///|
/// Elaborates pure theories and program modules in their original file order.
pub fn elaborate_file(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  file : @parser.MlwFile,
) -> ElaboratedFile raise ElabError {
  normalize_program_elaboration_errors(() => {
    elaborate_file_raw(context, environment, file)
  })
}

///|
/// Elaborates a library file using its full logical library path. This is the
/// path stored in every resulting theory/module key.
pub fn elaborate_file_at_path(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  file : @parser.MlwFile,
  path : ArrayView[Bytes],
) -> ElaboratedFile raise ElabError {
  normalize_program_elaboration_errors(() => {
    elaborate_file_at_path_raw(context, environment, file, path)
  })
}
