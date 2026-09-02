// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
priv enum TypeinvCap {
  ValidCap
  PinCap(Int)
  ConstructorCap(Array[TypeinvConstructorCap])
  RecordCap(Array[TypeinvFieldCap])
}

///|
priv struct TypeinvFieldCap {
  projection : @logic.LSymbol
  cap : TypeinvCap
}

///|
priv struct TypeinvConstructorCap {
  declaration : @logic.DataConstructor
  fields : Array[TypeinvCap]
}

///|
priv struct TypeinvProjectionStep {
  projection : @logic.LSymbol
  decorated : @logic.Term
}

///|
priv struct TypeinvInjectField {
  projection : @logic.LSymbol
  variable : @logic.VSymbol
  cap : TypeinvCap
}

///|
priv struct TypeinvInjectPin {
  fields : Array[TypeinvInjectField]
  invariants : Array[@logic.Term]
}

///|
priv struct TypeinvInspectPin {
  fields : Array[TypeinvFieldCap]
  stem : Array[(@logic.Term, @logic.Pattern)]
  leaf : @logic.Term
}

///|
priv struct TypeinvInspectState {
  pins : Array[TypeinvInspectPin]
  variable_caps : Map[@logic.VSymbol, TypeinvCap]
  commits : Array[Int]
}

///|
fn typeinv_cap_is_valid(cap : TypeinvCap) -> Bool {
  cap is ValidCap
}

///|
fn typeinv_constructor_cap(
  constructors : Array[TypeinvConstructorCap],
) -> TypeinvCap {
  if constructors.all(entry => entry.fields.all(typeinv_cap_is_valid)) {
    ValidCap
  } else {
    ConstructorCap(constructors)
  }
}

///|
fn typeinv_record_cap(fields : Array[TypeinvFieldCap]) -> TypeinvCap {
  if fields.all(field => typeinv_cap_is_valid(field.cap)) {
    ValidCap
  } else {
    RecordCap(fields)
  }
}

///|
fn typeinv_program_type(
  environment : VcEnvironment,
  ty : @logic.Ty,
) -> @mlw.ProgramTypeSymbol? {
  guard ty.view() is TyApp(symbol, _) else { return None }
  Some(environment.program_space.find_type_by_logic(symbol, None)) catch {
    @mlw.MlwError(_) => None
  }
}

///|
fn typeinv_program_type_is_solid(symbol : @mlw.ProgramTypeSymbol) -> Bool {
  let flags = symbol.view().flags
  !flags.fragile &&
  flags.argument_flags.all(flag => flag.frozen) &&
  flags.region_flags.all(flag => flag.frozen)
}

///|
fn typeinv_type_is_fragile(environment : VcEnvironment, ty : @logic.Ty) -> Bool {
  @mlw.Ity::from_ty(environment.program_space, ty, None).is_fragile() catch {
    _ => false
  }
}

///|
fn typeinv_is_trusted_constructor(
  environment : VcEnvironment,
  symbol : @logic.LSymbol,
) -> Bool {
  guard symbol.view().role is Constructor(_) &&
    symbol.view().result_type is Some(result) &&
    typeinv_program_type(environment, result) is Some(program_type) else {
    return false
  }
  !typeinv_program_type_is_solid(program_type)
}

///|
fn typeinv_is_trusted_projection(
  environment : VcEnvironment,
  symbol : @logic.LSymbol,
  result_type : @logic.Ty?,
) -> Bool raise {
  let view = symbol.view()
  let is_program_projection = view.role is Projection ||
    (
      view.role is Ordinary &&
      view.origin.attributes().any(attribute => attribute == b"is_field_id")
    )
  guard is_program_projection &&
    view.argument_types is [owner_type] &&
    typeinv_program_type(environment, owner_type) is Some(owner) else {
    return false
  }
  if typeinv_program_type_is_solid(owner) {
    return false
  }
  let result_is_fragile = match result_type {
    Some(ty) => typeinv_type_is_fragile(environment, ty)
    None => false
  }
  !result_is_fragile ||
  environment.known.find_constructors(owner.view().logic_type, None).length() <=
  1
}

///|
fn typeinv_projection_result_type(
  projection : @logic.LSymbol,
  owner_type : @logic.Ty,
) -> @logic.Ty raise {
  let view = projection.view()
  guard view.argument_types is [formal_owner] &&
    view.result_type is Some(formal_result) else {
    abort("validated program projection has an invalid logical type")
  }
  @logic.TySubstitution::new()
  .match_type(formal_owner, owner_type, None)
  .apply(formal_result, None)
}

///|
fn typeinv_constructor_argument_types(
  declaration : @logic.DataConstructor,
  result_type : @logic.Ty,
) -> Array[@logic.Ty] raise {
  let symbol = declaration.view().symbol
  guard symbol.view().result_type is Some(formal_result) else {
    abort("validated constructor lost its result type")
  }
  let substitution = @logic.TySubstitution::new().match_type(
    formal_result,
    result_type,
    None,
  )
  symbol.view().argument_types.map(argument => {
    substitution.apply(argument, None)
  })
}

///|
fn typeinv_field_descriptors(
  environment : VcEnvironment,
  symbol : @mlw.ProgramTypeSymbol,
  owner_type : @logic.Ty,
) -> Array[(@mlw.PVariable, @logic.LSymbol, @logic.Ty)] raise {
  let view = symbol.view()
  let fields = view.mutable_fields.to_owned() + view.immutable_fields.to_owned()
  fields.map(field => {
    let routine = environment.program_space.find_projection_by_field(
      field,
      None,
    )
    guard routine.view().logic is RLls(projection) else {
      abort("validated program field lost its logical projection")
    }
    (field, projection, typeinv_projection_result_type(projection, owner_type))
  })
}

///|
fn typeinv_validity(
  environment : VcEnvironment,
  value : @logic.Term,
) -> @logic.Term raise {
  @logic.Term::apply_predicate(
    environment.validity,
    [value],
    value.source_span(),
  )
}

///|
fn typeinv_fresh_variable(
  environment : VcEnvironment,
  source : @logic.VSymbol,
  suffix : BytesView,
  ty : @logic.Ty,
) -> @logic.VSymbol raise {
  let view = source.view()
  @logic.VSymbol::new(
    environment.context,
    append_bytes(append_bytes(view.name, b"_"), suffix),
    @identity.Origin::generated(
      @identity.Wp,
      view.name,
      view.origin.source_span(),
      view.origin.attributes(),
    ),
    ty,
    view.origin.source_span(),
  )
}

///|
fn typeinv_cap_field(
  fields : ArrayView[TypeinvFieldCap],
  projection : @logic.LSymbol,
) -> TypeinvCap? {
  for field in fields {
    if field.projection == projection {
      return Some(field.cap)
    }
  }
  None
}

///|
fn typeinv_inject_field(
  fields : ArrayView[TypeinvInjectField],
  projection : @logic.LSymbol,
) -> TypeinvInjectField? {
  for field in fields {
    if field.projection == projection {
      return Some(field)
    }
  }
  None
}

///|
fn typeinv_constructor_entry(
  constructors : ArrayView[TypeinvConstructorCap],
  symbol : @logic.LSymbol,
) -> TypeinvConstructorCap? {
  for entry in constructors {
    if entry.declaration.view().symbol == symbol {
      return Some(entry)
    }
  }
  None
}

///|
fn typeinv_constructor_projection_cap(
  entry : TypeinvConstructorCap,
  projection : @logic.LSymbol,
) -> TypeinvCap? {
  for index, field in entry.declaration.view().projections {
    if field is Some(candidate) && candidate == projection {
      return Some(entry.fields[index])
    }
  }
  None
}

///|
fn typeinv_inspect_variable(
  environment : VcEnvironment,
  name : BytesView,
  ty : @logic.Ty,
  span : @identity.SourceSpan?,
) -> @logic.VSymbol raise {
  @logic.VSymbol::new(
    environment.context,
    name,
    @identity.Origin::generated(@identity.Wp, name, span, []),
    ty,
    span,
  )
}

///|
fn typeinv_prepend_stem(
  stem : ArrayView[(@logic.Term, @logic.Pattern)],
  scrutinee : @logic.Term,
  pattern : @logic.Pattern,
) -> Array[(@logic.Term, @logic.Pattern)] {
  let result = [(scrutinee, pattern)]
  for entry in stem {
    result.push(entry)
  }
  result
}

///|
fn typeinv_inspect_cap_for_type(
  environment : VcEnvironment,
  state : TypeinvInspectState,
  stem : ArrayView[(@logic.Term, @logic.Pattern)],
  leaf : @logic.Term,
  ty : @logic.Ty,
) -> TypeinvCap raise {
  guard typeinv_program_type(environment, ty) is Some(symbol) else {
    return ValidCap
  }
  if typeinv_program_type_is_solid(symbol) {
    return ValidCap
  }
  let view = symbol.view()
  if view.flags.nonfree {
    let fields = typeinv_field_descriptors(environment, symbol, ty).map(descriptor => {
      let projected = typeinv_projection_term(leaf, descriptor.1)
      {
        projection: descriptor.1,
        cap: typeinv_inspect_cap_for_type(
          environment,
          state,
          stem,
          projected,
          descriptor.2,
        ),
      }
    })
    if view.flags.fragile {
      state.pins.push({ fields, stem: stem.to_owned(), leaf })
      return PinCap(state.pins.length())
    }
    return typeinv_record_cap(fields)
  }
  let declarations = environment.known.find_constructors(view.logic_type, None)
  let entries = declarations.map(declaration => {
    let declaration_view = declaration.view()
    let argument_types = typeinv_constructor_argument_types(declaration, ty)
    let fields = []
    for index, argument_type in argument_types {
      let projection = declaration_view.projections[index]
      if declarations.length() == 1 {
        let extracted = match projection {
          Some(projection) => typeinv_projection_term(leaf, projection)
          None => {
            let selected = typeinv_inspect_variable(
              environment,
              b"typeinv_field",
              argument_type,
              leaf.source_span(),
            )
            let patterns = argument_types.map(@logic.Pattern::wild)
            patterns[index] = @logic.Pattern::variable(selected)
            @logic.Term::case(
              leaf,
              [
                (
                  @logic.Pattern::app(
                    declaration_view.symbol,
                    patterns,
                    ty,
                    leaf.source_span(),
                  ),
                  @logic.Term::variable(selected),
                ),
              ],
              leaf.source_span(),
            )
          }
        }
        fields.push(
          typeinv_inspect_cap_for_type(
            environment, state, stem, extracted, argument_type,
          ),
        )
      } else {
        let selected = typeinv_inspect_variable(
          environment,
          b"typeinv_field",
          argument_type,
          leaf.source_span(),
        )
        let patterns = argument_types.map(@logic.Pattern::wild)
        patterns[index] = @logic.Pattern::variable(selected)
        let pattern = @logic.Pattern::app(
          declaration_view.symbol,
          patterns,
          ty,
          leaf.source_span(),
        )
        fields.push(
          typeinv_inspect_cap_for_type(
            environment,
            state,
            typeinv_prepend_stem(stem, leaf, pattern),
            @logic.Term::variable(selected),
            argument_type,
          ),
        )
      }
    }
    { declaration, fields }
  })
  typeinv_constructor_cap(entries)
}

///|
fn typeinv_inspect_variable_cap(
  environment : VcEnvironment,
  state : TypeinvInspectState,
  variable : @logic.VSymbol,
) -> TypeinvCap raise {
  match state.variable_caps.get(variable) {
    Some(cap) => cap
    None => {
      let cap = typeinv_inspect_cap_for_type(
        environment,
        state,
        [],
        @logic.Term::variable(variable),
        variable.ty(),
      )
      state.variable_caps[variable] = cap
      cap
    }
  }
}

///|
fn typeinv_add_commit(commits : Array[Int], index : Int) -> Unit {
  if !commits.any(existing => existing == index) {
    commits.push(index)
  }
}

///|
fn typeinv_inspect_commit(
  state : TypeinvInspectState,
  cap : TypeinvCap,
) -> Unit {
  match cap {
    ValidCap => ()
    PinCap(index) => {
      let pin = state.pins[index - 1]
      for field in pin.fields {
        typeinv_inspect_commit(state, field.cap)
      }
      typeinv_add_commit(state.commits, index)
    }
    ConstructorCap(entries) =>
      for entry in entries {
        for field in entry.fields {
          typeinv_inspect_commit(state, field)
        }
      }
    RecordCap(fields) =>
      for field in fields {
        typeinv_inspect_commit(state, field.cap)
      }
  }
}

///|
fn typeinv_inspect_join(
  state : TypeinvInspectState,
  left : TypeinvCap,
  right : TypeinvCap,
) -> TypeinvCap {
  match (left, right) {
    (ValidCap, cap) | (cap, ValidCap) => {
      typeinv_inspect_commit(state, cap)
      ValidCap
    }
    (PinCap(left), PinCap(right)) =>
      if left == right {
        PinCap(left)
      } else {
        typeinv_inspect_commit(state, PinCap(left))
        typeinv_inspect_commit(state, PinCap(right))
        ValidCap
      }
    (ConstructorCap(left), ConstructorCap(right)) => {
      let result = left.copy()
      for right_entry in right {
        let symbol = right_entry.declaration.view().symbol
        let mut merged = false
        for position, left_entry in result {
          if left_entry.declaration.view().symbol == symbol {
            result[position] = {
              declaration: left_entry.declaration,
              fields: [
                for index, cap in left_entry.fields => {
                  typeinv_inspect_join(state, cap, right_entry.fields[index])
                }
              ],
            }
            merged = true
            break
          }
        }
        if !merged {
          result.push(right_entry)
        }
      }
      typeinv_constructor_cap(result)
    }
    (RecordCap(left), RecordCap(right)) => {
      let result = left.copy()
      for position, field in result {
        guard typeinv_cap_field(right, field.projection) is Some(right_cap) else {
          abort("record cap fields changed across inspected branches")
        }
        result[position] = {
          projection: field.projection,
          cap: typeinv_inspect_join(state, field.cap, right_cap),
        }
      }
      typeinv_record_cap(result)
    }
    _ => abort("incompatible caps reached one inspected value")
  }
}

///|
fn typeinv_inspect_pattern_caps(
  state : TypeinvInspectState,
  caps : Map[@logic.VSymbol, TypeinvCap],
  cap : TypeinvCap,
  pattern : @logic.Pattern,
) -> Map[@logic.VSymbol, TypeinvCap] {
  if typeinv_cap_is_valid(cap) {
    return caps
  }
  match pattern.view() {
    Pwild(_) => caps
    Pvar(variable) => {
      let nested = caps.copy()
      nested[variable] = cap
      nested
    }
    Papp(symbol, arguments, _) =>
      match cap {
        ConstructorCap(entries) =>
          match typeinv_constructor_entry(entries, symbol) {
            Some(entry) => {
              let mut nested = caps
              for index, argument in arguments {
                nested = typeinv_inspect_pattern_caps(
                  state,
                  nested,
                  entry.fields[index],
                  argument,
                )
              }
              nested
            }
            None => caps
          }
        _ => abort("non-constructor cap reached an inspected pattern")
      }
    Por(left, _, _) => {
      typeinv_inspect_commit(state, cap)
      typeinv_inspect_pattern_caps(state, caps, ValidCap, left)
    }
    Pas(inner, variable, _) => {
      let nested = typeinv_inspect_pattern_caps(state, caps, cap, inner)
      nested[variable] = cap
      nested
    }
  }
}

///|
fn typeinv_inspect_projection_cap(
  state : TypeinvInspectState,
  cap : TypeinvCap,
  path : ArrayView[@logic.LSymbol],
) -> TypeinvCap {
  if path.is_empty() || typeinv_cap_is_valid(cap) {
    return cap
  }
  let projection = path[0]
  let remaining = [
    for index = 1; index < path.length(); index = index + 1 => path[index]
  ]
  match cap {
    ValidCap => ValidCap
    PinCap(index) => {
      guard typeinv_cap_field(state.pins[index - 1].fields, projection)
        is Some(field_cap) else {
        abort("inspected pin lost a projection")
      }
      typeinv_inspect_projection_cap(state, field_cap, remaining)
    }
    RecordCap(fields) => {
      guard typeinv_cap_field(fields, projection) is Some(field_cap) else {
        abort("inspected record cap lost a projection")
      }
      typeinv_inspect_projection_cap(state, field_cap, remaining)
    }
    ConstructorCap(entries) => {
      let mut result : TypeinvCap? = None
      for entry in entries {
        match typeinv_constructor_projection_cap(entry, projection) {
          Some(field_cap) => {
            let selected = typeinv_inspect_projection_cap(
              state, field_cap, remaining,
            )
            result = match result {
              Some(current) =>
                Some(typeinv_inspect_join(state, current, selected))
              None => Some(selected)
            }
          }
          None => ()
        }
      }
      match result {
        Some(result) => result
        None => abort("constructor caps lost an inspected projection")
      }
    }
  }
}

///|
fn typeinv_inspect_term(
  environment : VcEnvironment,
  state : TypeinvInspectState,
  caps : Map[@logic.VSymbol, TypeinvCap],
  path : ArrayView[@logic.LSymbol],
  term : @logic.Term,
) -> TypeinvCap raise {
  match term.view() {
    Tvar(variable) => {
      let cap = match caps.get(variable) {
        Some(cap) => cap
        None => typeinv_inspect_variable_cap(environment, state, variable)
      }
      typeinv_inspect_projection_cap(state, cap, path)
    }
    Tconst(_) => ValidCap
    Tapp(symbol, _, [left, right]) if symbol == environment.equality => {
      let left = typeinv_inspect_term(environment, state, caps, path, left)
      let right = typeinv_inspect_term(environment, state, caps, path, right)
      ignore(typeinv_inspect_join(state, left, right))
      ValidCap
    }
    Tapp(symbol, _, [argument]) if typeinv_is_trusted_projection(
        environment,
        symbol,
        term.ty(),
      ) => {
      let nested = [symbol]
      for projection in path {
        nested.push(projection)
      }
      typeinv_inspect_term(environment, state, caps, nested, argument)
    }
    Tapp(symbol, _, arguments) if typeinv_is_trusted_constructor(
        environment, symbol,
      ) => {
      guard find_constructor_declaration(environment, symbol)
        is Some(declaration) else {
        abort("trusted constructor is absent from the known map")
      }
      if !path.is_empty() {
        let projection = path[0]
        let mut selected = -1
        for index, field in declaration.view().projections {
          if field is Some(candidate) && candidate == projection {
            selected = index
            break
          }
        }
        if selected < 0 {
          abort("trusted constructor lost an inspected projection")
        }
        return typeinv_inspect_term(
          environment,
          state,
          caps,
          [
            for index = 1; index < path.length(); index = index + 1 => {
              path[index]
            }
          ],
          arguments[selected],
        )
      }
      typeinv_constructor_cap([
        {
          declaration,
          fields: arguments.map(argument => {
            typeinv_inspect_term(environment, state, caps, [], argument)
          }),
        },
      ])
    }
    Tapp(_, _, arguments) => {
      for argument in arguments {
        typeinv_inspect_commit(
          state,
          typeinv_inspect_term(environment, state, caps, [], argument),
        )
      }
      ValidCap
    }
    Tif(condition, yes, no) => {
      typeinv_inspect_commit(
        state,
        typeinv_inspect_term(environment, state, caps, [], condition),
      )
      typeinv_inspect_join(
        state,
        typeinv_inspect_term(environment, state, caps, path, yes),
        typeinv_inspect_term(environment, state, caps, path, no),
      )
    }
    Tlet(variable, value, body) => {
      let value_cap = typeinv_inspect_term(environment, state, caps, [], value)
      let nested = caps.copy()
      nested[variable] = value_cap
      typeinv_inspect_term(environment, state, nested, path, body)
    }
    Tcase(scrutinee, branches) => {
      let scrutinee_cap = typeinv_inspect_term(
        environment,
        state,
        caps,
        [],
        scrutinee,
      )
      let mut result : TypeinvCap? = None
      for branch in branches {
        let view = branch.view()
        let nested = typeinv_inspect_pattern_caps(
          state,
          caps,
          scrutinee_cap,
          view.pattern,
        )
        let branch_cap = typeinv_inspect_term(
          environment,
          state,
          nested,
          path,
          view.body,
        )
        result = match result {
          Some(current) =>
            Some(typeinv_inspect_join(state, current, branch_cap))
          None => Some(branch_cap)
        }
      }
      match result {
        Some(result) => result
        None => abort("validated inspected case has no branches")
      }
    }
    Teps(variable, body) => {
      let nested = caps.copy()
      nested[variable] = ValidCap
      typeinv_inspect_commit(
        state,
        typeinv_inspect_term(environment, state, nested, [], body),
      )
      ValidCap
    }
    Tquant(_, binders, triggers, body) => {
      let nested = caps.copy()
      for binder in binders {
        nested[binder] = ValidCap
      }
      for group in triggers {
        for trigger in group {
          typeinv_inspect_commit(
            state,
            typeinv_inspect_term(environment, state, nested, [], trigger),
          )
        }
      }
      typeinv_inspect_commit(
        state,
        typeinv_inspect_term(environment, state, nested, [], body),
      )
      ValidCap
    }
    Tbinop(_, left, right) => {
      typeinv_inspect_commit(
        state,
        typeinv_inspect_term(environment, state, caps, [], left),
      )
      typeinv_inspect_commit(
        state,
        typeinv_inspect_term(environment, state, caps, [], right),
      )
      ValidCap
    }
    Tnot(inner) => {
      typeinv_inspect_commit(
        state,
        typeinv_inspect_term(environment, state, caps, [], inner),
      )
      ValidCap
    }
    Ttrue | Tfalse => ValidCap
  }
}

///|
fn typeinv_inspect_markers(
  environment : VcEnvironment,
  state : TypeinvInspectState,
) -> Array[@logic.Term] raise {
  state.commits.map(index => {
    let pin = state.pins[index - 1]
    let mut marker = typeinv_validity(environment, pin.leaf)
    for entry in pin.stem {
      marker = @logic.Term::case(
        entry.0,
        [
          (entry.1, marker),
          (@logic.Pattern::wild(entry.1.ty()), @logic.Term::true_formula()),
        ],
        entry.0.source_span(),
      )
    }
    marker
  })
}

///|
fn typeinv_inspect_terms(
  environment : VcEnvironment,
  terms : ArrayView[@logic.Term],
) -> Array[@logic.Term] raise {
  let state = { pins: [], variable_caps: Map([]), commits: [] }
  for term in terms {
    typeinv_inspect_commit(
      state,
      typeinv_inspect_term(environment, state, Map([]), [], term),
    )
  }
  typeinv_inspect_markers(environment, state)
}

///|
fn typeinv_require_values(
  environment : VcEnvironment,
  values : ArrayView[@logic.Term],
) -> Array[@logic.Term] raise {
  let state = { pins: [], variable_caps: Map([]), commits: [] }
  for value in values {
    typeinv_inspect_commit(
      state,
      typeinv_inspect_term(environment, state, Map([]), [], value),
    )
  }
  typeinv_inspect_markers(environment, state)
}

///|
fn typeinv_cap_valid_under(parents : ArrayView[Int], cap : TypeinvCap) -> Bool {
  fn root(parents : ArrayView[Int], index : Int) -> Int {
    let mut current = index
    while current > 0 &&
          current < parents.length() &&
          parents[current] != current {
      current = parents[current]
    }
    current
  }
  match cap {
    ValidCap => true
    PinCap(index) => root(parents, index) == 0
    ConstructorCap(constructors) =>
      constructors.all(entry => {
        entry.fields.all(cap => typeinv_cap_valid_under(parents, cap))
      })
    RecordCap(fields) =>
      fields.all(field => typeinv_cap_valid_under(parents, field.cap))
  }
}

///|
fn typeinv_type_substitution(
  symbol : @mlw.ProgramTypeSymbol,
  arguments : ArrayView[@logic.Ty],
) -> @logic.TySubstitution raise {
  let parameters = symbol.view().logic_type.view().parameters
  if parameters.length() != arguments.length() {
    abort("program type and logical type disagree on arity")
  }
  let mut substitution = @logic.TySubstitution::new()
  for index, parameter in parameters {
    substitution = substitution.bind(parameter, arguments[index], None)
  }
  substitution
}

///|
fn typeinv_add_bound_variable(
  environment : VcEnvironment,
  pins : Array[TypeinvInjectPin],
  binders : Array[@logic.VSymbol],
  variable : @logic.VSymbol,
) -> TypeinvCap raise {
  fn descend(
    environment : VcEnvironment,
    pins : Array[TypeinvInjectPin],
    binders : Array[@logic.VSymbol],
    root : @logic.VSymbol,
    ty : @logic.Ty,
  ) -> TypeinvCap raise {
    guard ty.view() is TyApp(_, arguments) &&
      typeinv_program_type(environment, ty) is Some(symbol) else {
      return ValidCap
    }
    if typeinv_program_type_is_solid(symbol) {
      return ValidCap
    }
    let view = symbol.view()
    if view.flags.nonfree {
      let descriptors = typeinv_field_descriptors(environment, symbol, ty)
      if view.flags.fragile {
        let fields = []
        let replacements : Map[@logic.VSymbol, @logic.Term] = Map([])
        for descriptor in descriptors {
          let field_variable = typeinv_fresh_variable(
            environment,
            root,
            descriptor.0.view().name.view().name,
            descriptor.2,
          )
          binders.push(field_variable)
          let cap = descend(
            environment,
            pins,
            binders,
            field_variable,
            descriptor.2,
          )
          fields.push({
            projection: descriptor.1,
            variable: field_variable,
            cap,
          })
          replacements[descriptor.0.view().pure_symbol] = @logic.Term::variable(
            field_variable,
          )
        }
        let substitution = typeinv_type_substitution(symbol, arguments)
        let invariants = view.invariants.map(invariant => {
          instantiate_eval_match_term(
            environment,
            substitution,
            replacements.copy(),
            invariant,
          )
        })
        pins.push({ fields, invariants })
        return PinCap(pins.length())
      }
      return typeinv_record_cap(
        descriptors.map(descriptor => {
          let projected = typeinv_fresh_variable(
            environment,
            root,
            descriptor.0.view().name.view().name,
            descriptor.2,
          )
          {
            projection: descriptor.1,
            cap: descend(environment, pins, binders, projected, descriptor.2),
          }
        }),
      )
    }
    let constructors = environment.known.find_constructors(
      view.logic_type,
      None,
    )
    typeinv_constructor_cap(
      constructors.map(declaration => {
        let argument_types = typeinv_constructor_argument_types(declaration, ty)
        {
          declaration,
          fields: argument_types.map(argument_type => {
            let nested = typeinv_fresh_variable(
              environment, root, b"field", argument_type,
            )
            descend(environment, pins, binders, nested, argument_type)
          }),
        }
      }),
    )
  }
  let cap = descend(environment, pins, binders, variable, variable.ty())
  cap
}

///|
fn typeinv_ensure_parents(parents : Array[Int], pin_count : Int) -> Unit {
  while parents.length() <= pin_count {
    parents.push(parents.length())
  }
}

///|
fn typeinv_root(parents : ArrayView[Int], index : Int) -> Int {
  let mut current = index
  while current > 0 && current < parents.length() && parents[current] != current {
    current = parents[current]
  }
  current
}

///|
fn typeinv_commit_pin(parents : Array[Int], index : Int) -> Unit {
  let root = typeinv_root(parents, index)
  if root > 0 {
    parents[root] = 0
  }
}

///|
fn typeinv_union_pins(parents : Array[Int], left : Int, right : Int) -> Int {
  let left = typeinv_root(parents, left)
  let right = typeinv_root(parents, right)
  if left == right {
    return left
  }
  if left == 0 {
    parents[right] = 0
    return 0
  }
  if right == 0 {
    parents[left] = 0
    return 0
  }
  let root = left.min(right)
  let child = left.max(right)
  parents[child] = root
  root
}

///|
fn typeinv_intersect_parents(
  left : ArrayView[Int],
  right : ArrayView[Int],
  pin_count : Int,
) -> Array[Int] {
  let result = [0]
  for index = 1; index <= pin_count; index = index + 1 {
    result.push(index)
  }
  let pair_left : Array[Int] = [0]
  let pair_right : Array[Int] = [0]
  let representatives : Array[Int] = [0]
  for index = 1; index <= pin_count; index = index + 1 {
    let left_root = typeinv_root(left, index)
    let right_root = typeinv_root(right, index)
    let mut representative = -1
    for position = 0; position < pair_left.length(); position = position + 1 {
      if pair_left[position] == left_root && pair_right[position] == right_root {
        representative = representatives[position]
        break
      }
    }
    if representative < 0 {
      representative = if left_root == 0 && right_root == 0 { 0 } else { index }
      pair_left.push(left_root)
      pair_right.push(right_root)
      representatives.push(representative)
    }
    result[index] = representative
  }
  result
}

///|
fn typeinv_add_cap(
  caps : Map[@logic.VSymbol, TypeinvCap],
  variable : @logic.VSymbol,
  cap : TypeinvCap,
) -> Map[@logic.VSymbol, TypeinvCap] {
  if typeinv_cap_is_valid(cap) {
    caps
  } else {
    let nested = caps.copy()
    nested[variable] = cap
    nested
  }
}

///|
fn typeinv_join_caps(
  parents : ArrayView[Int],
  left : TypeinvCap,
  right : TypeinvCap,
) -> TypeinvCap {
  match (left, right) {
    (ValidCap, cap) | (cap, ValidCap) => {
      if !typeinv_cap_valid_under(parents, cap) {
        abort("type-invariant cap join lost a required commitment")
      }
      ValidCap
    }
    (PinCap(left), PinCap(right)) => {
      let left = typeinv_root(parents, left)
      let right = typeinv_root(parents, right)
      if left != right {
        abort("type-invariant cap join found unrelated pins")
      }
      if left == 0 {
        ValidCap
      } else {
        PinCap(left)
      }
    }
    (ConstructorCap(left_constructors), ConstructorCap(right_constructors)) => {
      let result = left_constructors.copy()
      for right_entry in right_constructors {
        let symbol = right_entry.declaration.view().symbol
        let mut merged = false
        for position, left_entry in result {
          if left_entry.declaration.view().symbol == symbol {
            if left_entry.fields.length() != right_entry.fields.length() {
              abort("constructor cap arity changed across branches")
            }
            result[position] = {
              declaration: left_entry.declaration,
              fields: [
                for index, cap in left_entry.fields => {
                  typeinv_join_caps(parents, cap, right_entry.fields[index])
                }
              ],
            }
            merged = true
            break
          }
        }
        if !merged {
          result.push(right_entry)
        }
      }
      typeinv_constructor_cap(result)
    }
    (RecordCap(left_fields), RecordCap(right_fields)) => {
      let result = left_fields.copy()
      for position, left_field in result {
        guard typeinv_cap_field(right_fields, left_field.projection)
          is Some(right_cap) else {
          abort("record cap fields changed across branches")
        }
        result[position] = {
          projection: left_field.projection,
          cap: typeinv_join_caps(parents, left_field.cap, right_cap),
        }
      }
      typeinv_record_cap(result)
    }
    _ => abort("incompatible type-invariant caps reached one value")
  }
}

///|
fn typeinv_add_pattern_caps(
  parents : ArrayView[Int],
  caps : Map[@logic.VSymbol, TypeinvCap],
  cap : TypeinvCap,
  pattern : @logic.Pattern,
) -> Map[@logic.VSymbol, TypeinvCap] {
  if typeinv_cap_is_valid(cap) {
    return caps
  }
  match pattern.view() {
    Pwild(_) => caps
    Pvar(variable) => typeinv_add_cap(caps, variable, cap)
    Papp(symbol, arguments, _) =>
      match cap {
        ConstructorCap(constructors) =>
          match typeinv_constructor_entry(constructors, symbol) {
            Some(entry) => {
              let mut nested = caps
              for index, argument in arguments {
                nested = typeinv_add_pattern_caps(
                  parents,
                  nested,
                  entry.fields[index],
                  argument,
                )
              }
              nested
            }
            None => caps
          }
        _ => abort("non-constructor cap reached a constructor pattern")
      }
    Por(left, _, _) => {
      if !typeinv_cap_valid_under(parents, cap) {
        abort("or-pattern observes an uncommitted type invariant")
      }
      typeinv_add_pattern_caps(parents, caps, ValidCap, left)
    }
    Pas(inner, variable, _) =>
      typeinv_add_cap(
        typeinv_add_pattern_caps(parents, caps, cap, inner),
        variable,
        cap,
      )
  }
}

///|
fn typeinv_drop_projection_step(
  path : ArrayView[TypeinvProjectionStep],
) -> Array[TypeinvProjectionStep] {
  [
    for index = 1; index < path.length(); index = index + 1 => path[index]
  ]
}

///|
fn typeinv_prepend_projection_step(
  path : ArrayView[TypeinvProjectionStep],
  step : TypeinvProjectionStep,
) -> Array[TypeinvProjectionStep] {
  let result = [step]
  for existing in path {
    result.push(existing)
  }
  result
}

///|
fn typeinv_apply_projection_step(
  value : @logic.Term,
  step : TypeinvProjectionStep,
) -> @logic.Term raise {
  copy_term_decoration(
    step.decorated,
    @logic.Term::apply_function(
      step.projection,
      [value],
      step.decorated.source_span(),
    ),
  )
}

///|
fn typeinv_unroll_projection_path(
  value : @logic.Term,
  path : ArrayView[TypeinvProjectionStep],
) -> @logic.Term raise {
  let mut result = value
  for step in path {
    result = typeinv_apply_projection_step(result, step)
  }
  result
}

///|
fn typeinv_fresh_projection_variable(
  environment : VcEnvironment,
  step : TypeinvProjectionStep,
) -> @logic.VSymbol raise {
  guard step.decorated.ty() is Some(ty) else {
    abort("validated projection result is a formula")
  }
  @logic.VSymbol::new(
    environment.context,
    b"typeinv_field",
    @identity.Origin::generated(
      @identity.Wp,
      b"typeinv_field",
      step.decorated.source_span(),
      step.decorated.attributes(),
    ),
    ty,
    step.decorated.source_span(),
  )
}

///|
fn typeinv_cap_of_term(
  environment : VcEnvironment,
  parents : ArrayView[Int],
  pins : ArrayView[TypeinvInjectPin],
  caps : Map[@logic.VSymbol, TypeinvCap],
  term : @logic.Term,
) -> (@logic.Term, TypeinvCap) raise {
  fn unwind(
    environment : VcEnvironment,
    parents : ArrayView[Int],
    pins : ArrayView[TypeinvInjectPin],
    term : @logic.Term,
    cap : TypeinvCap,
    path : ArrayView[TypeinvProjectionStep],
  ) -> (@logic.Term, TypeinvCap) raise {
    if path.is_empty() {
      return (term, cap)
    }
    let step = path[0]
    let remaining = typeinv_drop_projection_step(path)
    match cap {
      ValidCap => (typeinv_unroll_projection_path(term, path), ValidCap)
      PinCap(index) => {
        let index = typeinv_root(parents, index)
        if index == 0 {
          return (typeinv_unroll_projection_path(term, path), ValidCap)
        }
        guard index <= pins.length() &&
          typeinv_inject_field(pins[index - 1].fields, step.projection)
          is Some(field) else {
          abort("type-invariant pin lost a projected field")
        }
        unwind(
          environment,
          parents,
          pins,
          copy_term_decoration(
            step.decorated,
            @logic.Term::variable(field.variable),
          ),
          field.cap,
          remaining,
        )
      }
      RecordCap(fields) => {
        guard typeinv_cap_field(fields, step.projection) is Some(field_cap) else {
          abort("type-invariant record cap lost a projected field")
        }
        unwind(
          environment,
          parents,
          pins,
          typeinv_apply_projection_step(term, step),
          field_cap,
          remaining,
        )
      }
      ConstructorCap(constructors) => {
        if constructors.length() == 1 {
          guard typeinv_constructor_projection_cap(
              constructors[0],
              step.projection,
            )
            is Some(field_cap) else {
            abort("constructor cap lost a projected field")
          }
          return unwind(
            environment,
            parents,
            pins,
            typeinv_apply_projection_step(term, step),
            field_cap,
            remaining,
          )
        }
        guard term.ty() is Some(owner_type) else {
          abort("constructor cap is attached to a formula")
        }
        let branches : Array[(@logic.Pattern, @logic.Term)] = []
        let mut joined : TypeinvCap? = None
        for entry in constructors {
          let declaration_view = entry.declaration.view()
          let argument_types = typeinv_constructor_argument_types(
            entry.declaration,
            owner_type,
          )
          let patterns = argument_types.map(@logic.Pattern::wild)
          let mut selected_index = -1
          for index, projection in declaration_view.projections {
            if projection is Some(candidate) && candidate == step.projection {
              selected_index = index
              break
            }
          }
          if selected_index < 0 {
            continue
          }
          let selected = typeinv_fresh_projection_variable(environment, step)
          patterns[selected_index] = @logic.Pattern::variable(selected)
          let (body, branch_cap) = unwind(
            environment,
            parents,
            pins,
            copy_term_decoration(
              step.decorated,
              @logic.Term::variable(selected),
            ),
            entry.fields[selected_index],
            remaining,
          )
          branches.push(
            (
              @logic.Pattern::app(
                declaration_view.symbol,
                patterns,
                owner_type,
                term.source_span(),
              ),
              body,
            ),
          )
          joined = match joined {
            Some(current) =>
              Some(typeinv_join_caps(parents, current, branch_cap))
            None => Some(branch_cap)
          }
        }
        guard joined is Some(joined) && !branches.is_empty() else {
          abort("projection is absent from every constructor cap")
        }
        let constructor_count = match
          constructors[0].declaration.view().symbol.view().role {
          Constructor(count) => count
          Ordinary | Projection => 0
        }
        if constructors.length() < constructor_count {
          branches.push(
            (
              @logic.Pattern::wild(owner_type),
              typeinv_unroll_projection_path(term, path),
            ),
          )
          if !typeinv_cap_valid_under(parents, joined) {
            abort("partial constructor cap exposes an uncommitted field")
          }
        }
        let joined = if constructors.length() < constructor_count {
          ValidCap
        } else {
          joined
        }
        (
          copy_term_decoration(
            step.decorated,
            @logic.Term::case(term, branches, term.source_span()),
          ),
          joined,
        )
      }
    }
  }

  fn descend(
    environment : VcEnvironment,
    parents : ArrayView[Int],
    pins : ArrayView[TypeinvInjectPin],
    caps : Map[@logic.VSymbol, TypeinvCap],
    path : ArrayView[TypeinvProjectionStep],
    term : @logic.Term,
  ) -> (@logic.Term, TypeinvCap) raise {
    let rebuilt = match term.view() {
      Tvar(variable) => {
        let cap = match caps.get(variable) {
          Some(cap) => cap
          None => ValidCap
        }
        return unwind(environment, parents, pins, term, cap, path)
      }
      Tconst(_) => return (typeinv_unroll_projection_path(term, path), ValidCap)
      Tapp(symbol, _, [left, right]) if symbol == environment.equality => {
        let (left, left_cap) = descend(
          environment, parents, pins, caps, path, left,
        )
        let (right, right_cap) = descend(
          environment, parents, pins, caps, path, right,
        )
        ignore(typeinv_join_caps(parents, left_cap, right_cap))
        return (
          copy_term_decoration(
            term,
            @logic.Term::elaborated_apply(
              environment.equality,
              [left, right],
              None,
              term.source_span(),
            ),
          ),
          ValidCap,
        )
      }
      Tapp(symbol, _, [argument]) if typeinv_is_trusted_projection(
          environment,
          symbol,
          term.ty(),
        ) =>
        return descend(
          environment,
          parents,
          pins,
          caps,
          typeinv_prepend_projection_step(path, {
            projection: symbol,
            decorated: term,
          }),
          argument,
        )
      Tapp(symbol, _, arguments) if typeinv_is_trusted_constructor(
          environment, symbol,
        ) => {
        if !path.is_empty() {
          let step = path[0]
          guard find_constructor_declaration(environment, symbol)
            is Some(declaration) else {
            abort("trusted constructor is absent from the known map")
          }
          let projections = declaration.view().projections
          let mut selected = -1
          for index, projection in projections {
            if projection is Some(candidate) && candidate == step.projection {
              selected = index
              break
            }
          }
          if selected < 0 {
            abort("trusted constructor does not expose the projection")
          }
          return descend(
            environment,
            parents,
            pins,
            caps,
            typeinv_drop_projection_step(path),
            arguments[selected],
          )
        }
        guard find_constructor_declaration(environment, symbol)
          is Some(declaration) else {
          abort("trusted constructor is absent from the known map")
        }
        let rebuilt_arguments = []
        let field_caps = []
        for argument in arguments {
          let (argument, cap) = descend(
            environment,
            parents,
            pins,
            caps,
            [],
            argument,
          )
          rebuilt_arguments.push(argument)
          field_caps.push(cap)
        }
        return (
          copy_term_decoration(
            term,
            @logic.Term::elaborated_apply(
              symbol,
              rebuilt_arguments,
              term.ty(),
              term.source_span(),
            ),
          ),
          typeinv_constructor_cap([{ declaration, fields: field_caps }]),
        )
      }
      Tapp(symbol, _, arguments) => {
        let rebuilt_arguments = []
        for argument in arguments {
          let (argument, cap) = descend(
            environment,
            parents,
            pins,
            caps,
            [],
            argument,
          )
          if !typeinv_cap_valid_under(parents, cap) {
            abort("ordinary logic application observes a broken invariant")
          }
          rebuilt_arguments.push(argument)
        }
        @logic.Term::elaborated_apply(
          symbol,
          rebuilt_arguments,
          term.ty(),
          term.source_span(),
        )
      }
      Tif(condition, yes, no) => {
        let (condition, condition_cap) = descend(
          environment,
          parents,
          pins,
          caps,
          [],
          condition,
        )
        if !typeinv_cap_valid_under(parents, condition_cap) {
          abort("conditional observes a broken invariant")
        }
        let (yes, yes_cap) = descend(
          environment, parents, pins, caps, path, yes,
        )
        let (no, no_cap) = descend(environment, parents, pins, caps, path, no)
        return (
          copy_term_decoration(
            term,
            @logic.Term::if_then_else(condition, yes, no, term.source_span()),
          ),
          typeinv_join_caps(parents, yes_cap, no_cap),
        )
      }
      Tlet(variable, value, body) => {
        let (value, value_cap) = descend(
          environment,
          parents,
          pins,
          caps,
          [],
          value,
        )
        let nested = typeinv_add_cap(caps, variable, value_cap)
        let (body, body_cap) = descend(
          environment, parents, pins, nested, path, body,
        )
        return (
          copy_term_decoration(
            term,
            @logic.Term::let_in(variable, value, body, term.source_span()),
          ),
          body_cap,
        )
      }
      Tcase(scrutinee, branches) => {
        let (scrutinee, scrutinee_cap) = descend(
          environment,
          parents,
          pins,
          caps,
          [],
          scrutinee,
        )
        let rebuilt_branches = []
        let mut joined : TypeinvCap? = None
        for branch in branches {
          let view = branch.view()
          let nested = typeinv_add_pattern_caps(
            parents,
            caps,
            scrutinee_cap,
            view.pattern,
          )
          let (body, branch_cap) = descend(
            environment,
            parents,
            pins,
            nested,
            path,
            view.body,
          )
          rebuilt_branches.push((view.pattern, body))
          joined = match joined {
            Some(current) =>
              Some(typeinv_join_caps(parents, current, branch_cap))
            None => Some(branch_cap)
          }
        }
        guard joined is Some(joined) else {
          abort("validated case expression has no branches")
        }
        return (
          copy_term_decoration(
            term,
            @logic.Term::case(scrutinee, rebuilt_branches, term.source_span()),
          ),
          joined,
        )
      }
      Teps(variable, body) => {
        let nested = caps.copy()
        nested[variable] = ValidCap
        let (body, _) = descend(environment, parents, pins, nested, [], body)
        @logic.Term::epsilon(variable, body, term.source_span())
      }
      Tquant(quantifier, binders, triggers, body) => {
        let nested = caps.copy()
        for binder in binders {
          nested[binder] = ValidCap
        }
        let rebuilt_triggers = triggers.map(group => {
          group.map(trigger => {
            descend(environment, parents, pins, nested, [], trigger).0
          })
        })
        let (body, _) = descend(environment, parents, pins, nested, [], body)
        @logic.Term::quantify(
          quantifier,
          binders,
          rebuilt_triggers,
          body,
          term.source_span(),
        )
      }
      Tbinop(operator, left, right) => {
        let (left, _) = descend(environment, parents, pins, caps, [], left)
        let (right, _) = descend(environment, parents, pins, caps, [], right)
        @logic.Term::binary(operator, left, right, term.source_span())
      }
      Tnot(inner) => {
        let (inner, _) = descend(environment, parents, pins, caps, [], inner)
        @logic.Term::not(inner, term.source_span())
      }
      Ttrue => @logic.Term::true_formula()
      Tfalse => @logic.Term::false_formula()
    }
    (
      typeinv_unroll_projection_path(copy_term_decoration(term, rebuilt), path),
      ValidCap,
    )
  }
  descend(environment, parents, pins, caps, [], term)
}

///|
fn typeinv_projection_term(
  value : @logic.Term,
  projection : @logic.LSymbol,
) -> @logic.Term raise {
  @logic.Term::apply_function(projection, [value], value.source_span())
}

///|
fn typeinv_constructor_field_terms(
  environment : VcEnvironment,
  entry : TypeinvConstructorCap,
  value : @logic.Term,
) -> Array[@logic.Term] raise {
  guard value.ty() is Some(owner_type) else {
    abort("constructor cap is attached to a formula")
  }
  let view = entry.declaration.view()
  let argument_types = typeinv_constructor_argument_types(
    entry.declaration,
    owner_type,
  )
  [
    for index, argument_type in argument_types => {
      match view.projections[index] {
        Some(projection) => typeinv_projection_term(value, projection)
        None => {
          let selected = @logic.VSymbol::new(
            environment.context,
            b"typeinv_argument",
            @identity.Origin::generated(
              @identity.Wp,
              b"typeinv_argument",
              value.source_span(),
              [],
            ),
            argument_type,
            value.source_span(),
          )
          let patterns = argument_types.map(@logic.Pattern::wild)
          patterns[index] = @logic.Pattern::variable(selected)
          @logic.Term::case(
            value,
            [
              (
                @logic.Pattern::app(
                  view.symbol,
                  patterns,
                  owner_type,
                  value.source_span(),
                ),
                @logic.Term::variable(selected),
              ),
            ],
            value.source_span(),
          )
        }
      }
    }
  ]
}

///|
fn typeinv_commit_cap(
  environment : VcEnvironment,
  parents : Array[Int],
  pins : ArrayView[TypeinvInjectPin],
  value : @logic.Term,
  cap : TypeinvCap,
) -> Array[@logic.Term] raise {
  match cap {
    ValidCap => []
    PinCap(index) => {
      let index = typeinv_root(parents, index)
      if index == 0 {
        return []
      }
      guard index <= pins.length() else {
        abort("type-invariant union-find references an absent pin")
      }
      let pin = pins[index - 1]
      typeinv_commit_pin(parents, index)
      let formulas = []
      for field in pin.fields {
        let field_value = @logic.Term::variable(field.variable)
        for
          formula in typeinv_commit_cap(
            environment,
            parents,
            pins,
            field_value,
            field.cap,
          ) {
          formulas.push(formula)
        }
        formulas.push(
          @logic.Term::elaborated_apply(
            environment.equality,
            [field_value, typeinv_projection_term(value, field.projection)],
            None,
            value.source_span(),
          ),
        )
      }
      formulas
    }
    RecordCap(fields) => {
      let formulas = []
      for field in fields {
        for
          formula in typeinv_commit_cap(
            environment,
            parents,
            pins,
            typeinv_projection_term(value, field.projection),
            field.cap,
          ) {
          formulas.push(formula)
        }
      }
      formulas
    }
    ConstructorCap(constructors) => {
      if constructors.length() == 1 {
        let field_terms = typeinv_constructor_field_terms(
          environment,
          constructors[0],
          value,
        )
        let formulas = []
        for index, field in field_terms {
          for
            formula in typeinv_commit_cap(
              environment,
              parents,
              pins,
              field,
              constructors[0].fields[index],
            ) {
            formulas.push(formula)
          }
        }
        return formulas
      }
      guard value.ty() is Some(owner_type) else {
        abort("constructor cap is attached to a formula")
      }
      let branches : Array[(@logic.Pattern, @logic.Term)] = []
      for entry in constructors {
        let argument_types = typeinv_constructor_argument_types(
          entry.declaration,
          owner_type,
        )
        let variables = argument_types.map(argument_type => {
          @logic.VSymbol::new(
            environment.context,
            b"typeinv_argument",
            @identity.Origin::generated(
              @identity.Wp,
              b"typeinv_argument",
              value.source_span(),
              [],
            ),
            argument_type,
            value.source_span(),
          )
        })
        let branch_parents = parents.copy()
        let formulas = []
        for index, variable in variables {
          for
            formula in typeinv_commit_cap(
              environment,
              branch_parents,
              pins,
              @logic.Term::variable(variable),
              entry.fields[index],
            ) {
            formulas.push(formula)
          }
        }
        branches.push(
          (
            @logic.Pattern::app(
              entry.declaration.view().symbol,
              variables.map(@logic.Pattern::variable),
              owner_type,
              value.source_span(),
            ),
            conjunction(formulas),
          ),
        )
      }
      let constructor_count = match
        constructors[0].declaration.view().symbol.view().role {
        Constructor(count) => count
        Ordinary | Projection => 0
      }
      if constructors.length() < constructor_count {
        branches.push(
          (@logic.Pattern::wild(owner_type), @logic.Term::true_formula()),
        )
      }
      [@logic.Term::case(value, branches, value.source_span())]
    }
  }
}

///|
fn typeinv_equality_formula(
  environment : VcEnvironment,
  parents : Array[Int],
  pins : ArrayView[TypeinvInjectPin],
  original : @logic.Term,
  left : @logic.Term,
  left_cap : TypeinvCap,
  right : @logic.Term,
  right_cap : TypeinvCap,
) -> @logic.Term raise {
  let formulas = [
    copy_term_decoration(
      original,
      @logic.Term::elaborated_apply(
        environment.equality,
        [left, right],
        None,
        original.source_span(),
      ),
    ),
  ]
  fn append_commits(
    destination : Array[@logic.Term],
    source : ArrayView[@logic.Term],
  ) -> Unit {
    for formula in source {
      destination.push(formula)
    }
  }
  match (left_cap, right_cap) {
    (ValidCap, cap) =>
      append_commits(
        formulas,
        typeinv_commit_cap(environment, parents, pins, right, cap),
      )
    (cap, ValidCap) =>
      append_commits(
        formulas,
        typeinv_commit_cap(environment, parents, pins, left, cap),
      )
    (PinCap(left_index), PinCap(right_index)) => {
      let left_index = typeinv_root(parents, left_index)
      let right_index = typeinv_root(parents, right_index)
      if left_index == 0 {
        append_commits(
          formulas,
          typeinv_commit_cap(
            environment,
            parents,
            pins,
            right,
            PinCap(right_index),
          ),
        )
      } else if right_index == 0 {
        append_commits(
          formulas,
          typeinv_commit_cap(
            environment,
            parents,
            pins,
            left,
            PinCap(left_index),
          ),
        )
      } else if left_index != right_index {
        let left_pin = pins[left_index - 1]
        let right_pin = pins[right_index - 1]
        ignore(typeinv_union_pins(parents, left_index, right_index))
        for left_field in left_pin.fields {
          guard typeinv_inject_field(right_pin.fields, left_field.projection)
            is Some(right_field) else {
            abort("equal type-invariant pins have different fields")
          }
          formulas.push(
            typeinv_equality_formula(
              environment,
              parents,
              pins,
              original,
              @logic.Term::variable(left_field.variable),
              left_field.cap,
              @logic.Term::variable(right_field.variable),
              right_field.cap,
            ),
          )
        }
      }
    }
    (ConstructorCap(left_constructors), ConstructorCap(right_constructors)) if left_constructors.length() ==
      1 &&
      right_constructors.length() == 1 => {
      let left_fields = typeinv_constructor_field_terms(
        environment,
        left_constructors[0],
        left,
      )
      let right_fields = typeinv_constructor_field_terms(
        environment,
        right_constructors[0],
        right,
      )
      for index, left_field in left_fields {
        formulas.push(
          typeinv_equality_formula(
            environment,
            parents,
            pins,
            original,
            left_field,
            left_constructors[0].fields[index],
            right_fields[index],
            right_constructors[0].fields[index],
          ),
        )
      }
    }
    (RecordCap(left_fields), RecordCap(right_fields)) =>
      for left_field in left_fields {
        guard typeinv_cap_field(right_fields, left_field.projection)
          is Some(right_field_cap) else {
          abort("equal record caps have different fields")
        }
        formulas.push(
          typeinv_equality_formula(
            environment,
            parents,
            pins,
            original,
            typeinv_projection_term(left, left_field.projection),
            left_field.cap,
            typeinv_projection_term(right, left_field.projection),
            right_field_cap,
          ),
        )
      }
    (left_cap, right_cap) => {
      append_commits(
        formulas,
        typeinv_commit_cap(environment, parents, pins, left, left_cap),
      )
      append_commits(
        formulas,
        typeinv_commit_cap(environment, parents, pins, right, right_cap),
      )
    }
  }
  conjunction(formulas)
}

///|
fn typeinv_inject_formula(
  environment : VcEnvironment,
  pins : Array[TypeinvInjectPin],
  caps : Map[@logic.VSymbol, TypeinvCap],
  parents : Array[Int],
  positive : Bool,
  formula : @logic.Term,
) -> (@logic.Term, Array[Int]) raise {
  match formula.view() {
    Tapp(symbol, _, [value]) if symbol == environment.validity => {
      let (value, cap) = typeinv_cap_of_term(
        environment, parents, pins, caps, value,
      )
      if positive {
        let index = match cap {
          ValidCap => 0
          PinCap(index) => typeinv_root(parents, index)
          ConstructorCap(_) | RecordCap(_) =>
            abort("validity marker does not identify one pin")
        }
        if index == 0 {
          return (
            copy_term_decoration(formula, @logic.Term::true_formula()),
            parents,
          )
        }
        guard index <= pins.length() else {
          abort("validity marker references an absent pin")
        }
        let pin = pins[index - 1]
        for field in pin.fields {
          if !typeinv_cap_valid_under(parents, field.cap) {
            abort("outer invariant is checked before a nested invariant")
          }
        }
        return (
          asymmetric_conjunction(
            pin.invariants.map(invariant => {
              copy_term_decoration(formula, invariant)
            }),
          ),
          parents,
        )
      }
      let committed = typeinv_commit_cap(environment, parents, pins, value, cap)
      (copy_term_decoration(formula, conjunction(committed)), parents)
    }
    Tapp(symbol, _, [left, right]) if !positive &&
      symbol == environment.equality => {
      let (left, left_cap) = typeinv_cap_of_term(
        environment, parents, pins, caps, left,
      )
      let (right, right_cap) = typeinv_cap_of_term(
        environment, parents, pins, caps, right,
      )
      (
        typeinv_equality_formula(
          environment, parents, pins, formula, left, left_cap, right, right_cap,
        ),
        parents,
      )
    }
    Tapp(_, _, _) if formula
      .attributes()
      .any(attribute => attribute == annotation_attribute) => {
      let (formula, _) = typeinv_cap_of_term(
        environment, parents, pins, caps, formula,
      )
      (formula, parents)
    }
    Tapp(_, _, _) => {
      let (formula, _) = typeinv_cap_of_term(
        environment, parents, pins, caps, formula,
      )
      (formula, parents)
    }
    Tif(condition, yes, no) => {
      let (condition, _) = typeinv_cap_of_term(
        environment, parents, pins, caps, condition,
      )
      let (yes, yes_parents) = typeinv_inject_formula(
        environment,
        pins,
        caps,
        parents.copy(),
        positive,
        yes,
      )
      let (no, no_parents) = typeinv_inject_formula(
        environment,
        pins,
        caps,
        parents.copy(),
        positive,
        no,
      )
      typeinv_ensure_parents(yes_parents, pins.length())
      typeinv_ensure_parents(no_parents, pins.length())
      (
        copy_term_decoration(
          formula,
          @logic.Term::if_then_else(condition, yes, no, formula.source_span()),
        ),
        typeinv_intersect_parents(yes_parents, no_parents, pins.length()),
      )
    }
    Tlet(variable, value, body) => {
      let (value, value_cap) = typeinv_cap_of_term(
        environment, parents, pins, caps, value,
      )
      let nested = typeinv_add_cap(caps, variable, value_cap)
      let (body, parents) = typeinv_inject_formula(
        environment, pins, nested, parents, positive, body,
      )
      (
        copy_term_decoration(
          formula,
          @logic.Term::let_in(variable, value, body, formula.source_span()),
        ),
        parents,
      )
    }
    Tcase(scrutinee, branches) => {
      let (scrutinee, scrutinee_cap) = typeinv_cap_of_term(
        environment, parents, pins, caps, scrutinee,
      )
      let rebuilt = []
      let mut joined_parents : Array[Int]? = None
      for branch in branches {
        let view = branch.view()
        let nested = typeinv_add_pattern_caps(
          parents,
          caps,
          scrutinee_cap,
          view.pattern,
        )
        let (body, branch_parents) = typeinv_inject_formula(
          environment,
          pins,
          nested,
          parents.copy(),
          positive,
          view.body,
        )
        rebuilt.push((view.pattern, body))
        typeinv_ensure_parents(branch_parents, pins.length())
        joined_parents = match joined_parents {
          Some(current) => {
            typeinv_ensure_parents(current, pins.length())
            Some(
              typeinv_intersect_parents(current, branch_parents, pins.length()),
            )
          }
          None => Some(branch_parents)
        }
      }
      guard joined_parents is Some(joined_parents) else {
        abort("validated case formula has no branches")
      }
      (
        copy_term_decoration(
          formula,
          @logic.Term::case(scrutinee, rebuilt, formula.source_span()),
        ),
        joined_parents,
      )
    }
    Tquant(quantifier, binders, triggers, body) => {
      let valid_binders = match quantifier {
        ForallQuantifier => !positive
        ExistsQuantifier => positive
      }
      let nested = caps.copy()
      let retained = []
      if valid_binders {
        for binder in binders {
          retained.push(binder)
        }
      } else {
        for binder in binders {
          retained.push(binder)
          let cap = typeinv_add_bound_variable(
            environment, pins, retained, binder,
          )
          nested[binder] = cap
          typeinv_ensure_parents(parents, pins.length())
        }
      }
      let rebuilt_triggers = triggers.map(group => {
        group.map(trigger => {
          typeinv_cap_of_term(environment, parents, pins, nested, trigger).0
        })
      })
      let (body, parents) = typeinv_inject_formula(
        environment, pins, nested, parents, positive, body,
      )
      (
        copy_term_decoration(
          formula,
          @logic.Term::quantify(
            quantifier,
            retained,
            rebuilt_triggers,
            body,
            formula.source_span(),
          ),
        ),
        parents,
      )
    }
    Tbinop(And, left, right) => {
      let (left, parents) = typeinv_inject_formula(
        environment, pins, caps, parents, positive, left,
      )
      let (right, parents) = typeinv_inject_formula(
        environment, pins, caps, parents, positive, right,
      )
      (
        copy_term_decoration(
          formula,
          @logic.Term::binary(And, left, right, formula.source_span()),
        ),
        parents,
      )
    }
    Tbinop(Implies, left, right) => {
      let initial = parents.copy()
      let (left, parents) = typeinv_inject_formula(
        environment,
        pins,
        caps,
        parents,
        !positive,
        left,
      )
      let (right, _) = typeinv_inject_formula(
        environment, pins, caps, parents, positive, right,
      )
      (
        copy_term_decoration(
          formula,
          @logic.Term::binary(Implies, left, right, formula.source_span()),
        ),
        initial,
      )
    }
    Tbinop(Or, left, right) => {
      let (left, left_parents) = typeinv_inject_formula(
        environment,
        pins,
        caps,
        parents.copy(),
        positive,
        left,
      )
      let (right, right_parents) = typeinv_inject_formula(
        environment,
        pins,
        caps,
        parents.copy(),
        positive,
        right,
      )
      typeinv_ensure_parents(left_parents, pins.length())
      typeinv_ensure_parents(right_parents, pins.length())
      (
        copy_term_decoration(
          formula,
          @logic.Term::binary(Or, left, right, formula.source_span()),
        ),
        typeinv_intersect_parents(left_parents, right_parents, pins.length()),
      )
    }
    Tbinop(Iff, _, _) => {
      let (formula, _) = typeinv_cap_of_term(
        environment, parents, pins, caps, formula,
      )
      (formula, parents)
    }
    Tnot(inner) => {
      let initial = parents.copy()
      let (inner, _) = typeinv_inject_formula(
        environment,
        pins,
        caps,
        parents,
        !positive,
        inner,
      )
      (
        copy_term_decoration(
          formula,
          @logic.Term::not(inner, formula.source_span()),
        ),
        initial,
      )
    }
    Ttrue | Tfalse => (formula, parents)
    Tvar(_) | Tconst(_) | Teps(_, _) => {
      let (formula, _) = typeinv_cap_of_term(
        environment, parents, pins, caps, formula,
      )
      (formula, parents)
    }
  }
}

///|
fn typeinv_inject(
  environment : VcEnvironment,
  formula : @logic.Term,
) -> @logic.Term raise {
  let pins : Array[TypeinvInjectPin] = []
  typeinv_inject_formula(environment, pins, Map([]), [0], true, formula).0
}
