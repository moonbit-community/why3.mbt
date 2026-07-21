// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn collect_select_kept_types(
  term : @logic.Term,
  selected : Array[@logic.Ty],
) -> Unit {
  let add = fn(ty : @logic.Ty) {
    if ty.is_closed() && !selected.contains(ty) {
      selected.push(ty)
    }
  }
  let visit = fn(child) { collect_select_kept_types(child, selected) }
  match term.view() {
    Tapp(_, _, arguments) =>
      for argument in arguments {
        if argument.ty() is Some(ty) {
          add(ty)
        }
        visit(argument)
      }
    Tif(condition, then_branch, else_branch) => {
      visit(condition)
      visit(then_branch)
      visit(else_branch)
    }
    Tlet(_, value, body) => {
      visit(value)
      visit(body)
    }
    Tcase(scrutinee, branches) => {
      if scrutinee.ty() is Some(ty) {
        add(ty)
      }
      visit(scrutinee)
      for branch in branches {
        visit(branch.view().body)
      }
    }
    Teps(_, body) => visit(body)
    Tquant(_, _, triggers, body) => {
      for group in triggers {
        for trigger in group {
          visit(trigger)
        }
      }
      visit(body)
    }
    Tbinop(_, left, right) => {
      visit(left)
      visit(right)
    }
    Tnot(inner) => visit(inner)
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => ()
  }
}

///|
fn collect_select_kept_declaration(
  declaration : @logic.Decl,
  selected : Array[@logic.Ty],
) -> Unit {
  match declaration.view() {
    Dlogic(definitions) =>
      for definition in definitions {
        collect_select_kept_types(definition.view().body, selected)
      }
    Dind(declarations) =>
      for declaration in declarations {
        for case_ in declaration.view().cases {
          collect_select_kept_types(case_.view().formula, selected)
        }
      }
    Dprop(_, _, formula) => collect_select_kept_types(formula, selected)
    Dtype(_) | Ddata(_) | Dparam(_) => ()
  }
}

///|
pub fn encoding_monomorphise_goal(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.EncodingMonomorphiseGoal
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return task
  }
  let items = task.view().items
  guard !items.is_empty() &&
    items[items.length() - 1] is TheoryDecl(goal) &&
    goal.view() is Dprop(Pgoal, _, formula) else {
    return fail_transform(InvalidTask, stage, "task has no final goal")
  }
  if !formula.free_type_variables().is_empty() {
    return fail_transform(
      InvariantFailure,
      stage,
      "discriminate left a free type variable in the goal",
    )
  }
  task
}

///|
pub fn encoding_select_kept(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.SelectKept
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return task
  }
  let selected : Array[@logic.Ty] = []
  for item in task.view().items {
    if item is TheoryDecl(declaration) {
      collect_select_kept_declaration(declaration, selected)
    }
  }
  if selected.is_empty() {
    return task
  }
  let items = task.view().items.to_owned()
  guard !items.is_empty() else {
    return fail_transform(InvalidTask, stage, "empty task")
  }
  let (type_symbol_order, _) = discrimination_declaration_order(items)
  selected.sort_by((left, right) => {
    compare_discriminated_type(left, right, type_symbol_order)
  })
  let mut insertion = items.length() - 1
  for ty in selected.rev() {
    items.insert(
      insertion,
      TheoryMeta(@theory.Meta::new(b"encoding:kept", [MetaType(ty)])),
    )
    insertion = insertion + 1
  }
  checked_task(task.context_anchor(), items, stage)
}

///|
pub fn encoding_keep_field_types(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.KeepFieldTypes
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return task
  }
  let kept : Array[@logic.Ty] = []
  for item in task.view().items {
    if item is TheoryMeta(meta) &&
      meta.view() is { name: b"encoding:kept", arguments: [MetaType(ty)] } &&
      !kept.contains(ty) {
      kept.push(ty)
    }
  }
  let additions : Array[@logic.Ty] = []
  for item in task.view().items {
    guard item is TheoryDecl(declaration) &&
      declaration.view() is Ddata(data_declarations) else {
      continue
    }
    for data_declaration in data_declarations {
      let data = data_declaration.view()
      let instances = [
        for ty in kept if ty.view() is TyApp(symbol, _) &&
        symbol == data.type_symbol => ty
      ]
      if instances.is_empty() {
        return fail_transform(
          UnsupportedStructure,
          stage,
          "algebraic declaration has no selected kept instance",
        )
      }
      let formal = @logic.Ty::app(
        data.type_symbol,
        [
          for parameter in data.type_symbol.view().parameters => {
            @logic.Ty::variable(parameter)
          }
        ],
        None,
      ) catch {
        _ =>
          return fail_transform(
            InvariantFailure,
            stage,
            "cannot construct an algebraic field type",
          )
      }
      for instance in instances {
        let substitution = @logic.TySubstitution::new().match_type(
          formal,
          instance,
          None,
        ) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              stage,
              "kept algebraic instance does not match its declaration",
            )
        }
        for data_constructor in data.constructors {
          for field in data_constructor.view().symbol.view().argument_types {
            let field = substitution.apply(field, None) catch {
              _ =>
                return fail_transform(
                  InvariantFailure,
                  stage,
                  "cannot instantiate an algebraic field type",
                )
            }
            if !kept.contains(field) && !additions.contains(field) {
              additions.push(field)
            }
          }
        }
      }
    }
  }
  if additions.is_empty() {
    return task
  }
  let items = task.view().items.to_owned()
  guard !items.is_empty() else {
    return fail_transform(InvalidTask, stage, "empty task")
  }
  let (type_symbol_order, _) = discrimination_declaration_order(items)
  additions.sort_by((left, right) => {
    compare_discriminated_type(left, right, type_symbol_order)
  })
  let mut insertion = items.length() - 1
  for ty in additions.rev() {
    items.insert(
      insertion,
      TheoryMeta(@theory.Meta::new(b"encoding:kept", [MetaType(ty)])),
    )
    insertion = insertion + 1
  }
  checked_task(task.context_anchor(), items, stage)
}

///|
fn kept_type_set(task : @theory.Task) -> Map[@logic.Ty, Unit] {
  let kept : Map[@logic.Ty, Unit] = Map([])
  for item in task.view().items {
    if item is TheoryMeta(meta) &&
      meta.view() is { name: b"encoding:kept", arguments: [MetaType(ty)] } {
      kept[ty] = ()
    }
  }
  kept
}

///|
priv struct TwinBridge {
  ty : @logic.Ty
  protect : @logic.LSymbol
  unprotect : @logic.LSymbol
  declarations : Array[@theory.TheoryItem]
}

///|
fn twin_origin(
  name : BytesView,
  attributes : ArrayView[Bytes],
) -> @identity.Origin {
  @identity.Origin::generated(@identity.Twin, name, None, attributes)
}

///|
fn twin_parameter_item(
  context : @identity.CompilationContext,
  symbol : @logic.LSymbol,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Twin
  let declaration = @logic.Decl::parameter(
    context,
    symbol.view().origin,
    symbol,
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "cannot declare a twin bridge")
  }
  TheoryDecl(declaration)
}

///|
fn twin_equality(
  equality : @logic.LSymbol,
  left : @logic.Term,
  right : @logic.Term,
) -> @logic.Term raise TransformError {
  @logic.Term::elaborated_apply(equality, [left, right], None, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.Twin,
        "cannot construct a bridge equality",
      )
  }
}

///|
fn twin_bridge_axiom(
  context : @identity.CompilationContext,
  name : BytesView,
  ty : @logic.Ty,
  protect : @logic.LSymbol,
  unprotect : @logic.LSymbol,
  equality : @logic.LSymbol,
  left_bridge : Bool,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Twin
  let variable_name = if left_bridge { b"i" } else { b"j" }
  let variable_attributes : Array[Bytes] = if left_bridge {
    []
  } else {
    [b"encoding:unprotected"]
  }
  let variable = @logic.VSymbol::new(
    context,
    variable_name,
    twin_origin(variable_name, variable_attributes),
    ty,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot create a bridge binder",
      )
  }
  let value = @logic.Term::variable(variable)
  let (first, second) = if left_bridge {
    (protect, unprotect)
  } else {
    (unprotect, protect)
  }
  let inner = @logic.Term::elaborated_apply(first, [value], Some(ty), None) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot apply an inner bridge",
      )
  }
  let outer = @logic.Term::elaborated_apply(second, [inner], Some(ty), None) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot apply an outer bridge",
      )
  }
  let formula = twin_equality(equality, outer, value)
  let trigger = if left_bridge { inner } else { outer }
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    [variable],
    [[trigger]],
    formula,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot quantify a bridge axiom",
      )
  }
  let origin = twin_origin(name, [])
  let proposition = @logic.PrSymbol::new(context, name, origin)
  let declaration = @logic.Decl::proposition(
    context,
    origin,
    Paxiom,
    proposition,
    formula,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot declare a bridge axiom",
      )
  }
  TheoryDecl(declaration)
}

///|
fn make_twin_bridge(
  context : @identity.CompilationContext,
  ty : @logic.Ty,
  equality : @logic.LSymbol,
) -> TwinBridge raise TransformError {
  let stage = @identity.Twin
  let protect_origin = twin_origin(b"t2tb", [b"encoding:unprotected"])
  let unprotect_origin = twin_origin(b"tb2t", [b"encoding:unprotecting"])
  let protect = @logic.LSymbol::new_function(
    context,
    b"t2tb",
    protect_origin,
    [ty],
    ty,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot create a protecting bridge",
      )
  }
  let unprotect = @logic.LSymbol::new_function(
    context,
    b"tb2t",
    unprotect_origin,
    [ty],
    ty,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot create an unprotecting bridge",
      )
  }
  {
    ty,
    protect,
    unprotect,
    declarations: [
      twin_parameter_item(context, protect),
      twin_parameter_item(context, unprotect),
      twin_bridge_axiom(
        context, b"BridgeL", ty, protect, unprotect, equality, true,
      ),
      twin_bridge_axiom(
        context, b"BridgeR", ty, protect, unprotect, equality, false,
      ),
    ],
  }
}

///|
fn find_twin_bridge(
  bridges : ArrayView[TwinBridge],
  ty : @logic.Ty,
) -> TwinBridge? {
  for bridge in bridges {
    if bridge.ty == ty {
      return Some(bridge)
    }
  }
  None
}

///|
fn mark_twin_bridge(seen : Array[@logic.Ty], ty : @logic.Ty) -> Unit {
  if !seen.contains(ty) {
    seen.push(ty)
  }
}

///|
fn twin_rewrite_term(
  term : @logic.Term,
  bridges : ArrayView[TwinBridge],
  seen : Array[@logic.Ty],
) -> @logic.Term raise TransformError {
  let stage = @identity.Twin
  let recurse = fn(child) -> @logic.Term raise TransformError {
    twin_rewrite_term(child, bridges, seen)
  }
  match term.view() {
    Tapp(symbol, _, arguments) => {
      let mapped = [ for argument in arguments => recurse(argument) ]
      let view = symbol.view()
      let replacement = if is_builtin_equality(symbol) ||
        view.role is Constructor(_) ||
        view.role is Projection {
        @logic.Term::elaborated_apply(symbol, mapped, term.ty(), None) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              stage,
              "cannot rebuild an exempt twin application",
            )
        }
      } else {
        if mapped.length() != view.argument_types.length() {
          return fail_transform(
            InvariantFailure,
            stage,
            "twin application arity mismatch",
          )
        }
        let converted : Array[@logic.Term] = []
        for index, argument in mapped {
          guard argument.ty() is Some(actual) else {
            return fail_transform(
              InvariantFailure,
              stage,
              "twin application has a formula argument",
            )
          }
          let formal = view.argument_types[index]
          if actual == formal {
            converted.push(argument)
          } else {
            match find_twin_bridge(bridges, actual) {
              None => converted.push(argument)
              Some(bridge) => {
                mark_twin_bridge(seen, actual)
                match argument.view() {
                  Tapp(inner_symbol, _, inner_arguments) if inner_symbol ==
                    bridge.unprotect &&
                    inner_arguments.length() == 1 =>
                    converted.push(inner_arguments[0])
                  _ => {
                    let protected_argument = @logic.Term::elaborated_apply(
                      bridge.protect,
                      [argument],
                      Some(actual),
                      None,
                    ) catch {
                      _ =>
                        return fail_transform(
                          InvariantFailure,
                          stage,
                          "cannot protect a twin argument",
                        )
                    }
                    converted.push(protected_argument)
                  }
                }
              }
            }
          }
        }
        let application = @logic.Term::elaborated_apply(
          symbol,
          converted,
          term.ty(),
          None,
        ) catch {
          _ =>
            return fail_transform(
              InvariantFailure,
              stage,
              "cannot rebuild a twin application",
            )
        }
        match (term.ty(), view.result_type) {
          (Some(actual), Some(formal)) if actual != formal =>
            match find_twin_bridge(bridges, actual) {
              None => application
              Some(bridge) => {
                mark_twin_bridge(seen, actual)
                @logic.Term::elaborated_apply(
                  bridge.unprotect,
                  [application],
                  Some(actual),
                  None,
                ) catch {
                  _ =>
                    return fail_transform(
                      InvariantFailure,
                      stage,
                      "cannot unprotect a twin result",
                    )
                }
              }
            }
          _ => application
        }
      }
      copy_term_decoration(term, replacement)
    }
    _ => map_plain(term, recurse, stage)
  }
}

///|
fn twin_rewrite_proposition(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  kind : @logic.PropositionKind,
  proposition : @logic.PrSymbol,
  formula : @logic.Term,
  bridges : ArrayView[TwinBridge],
  seen : Array[@logic.Ty],
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Twin
  let formula = twin_rewrite_term(formula, bridges, seen)
  let declaration = @logic.Decl::proposition(
    context,
    declaration.origin(),
    kind,
    proposition,
    formula,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot rebuild a twin proposition",
      )
  }
  TheoryDecl(declaration)
}

///|
pub fn encoding_twin(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.Twin
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return task
  }
  let kept = kept_type_set(task)
  let mut equality : @logic.LSymbol? = None
  for item in task.view().items {
    if item is TheoryDecl(declaration) &&
      declaration.view() is Dparam(symbol) &&
      is_builtin_equality(symbol) {
      equality = Some(symbol)
    }
  }
  guard equality is Some(equality) else {
    return fail_transform(
      InvariantFailure,
      stage,
      "task has no equality declaration",
    )
  }
  let kept_types = [ for entry in kept => entry.0 ]
  let (type_symbol_order, _) = discrimination_declaration_order(
    task.view().items,
  )
  kept_types.sort_by((left, right) => {
    compare_discriminated_type(left, right, type_symbol_order)
  })
  let bridges : Array[TwinBridge] = []
  for ty in kept_types {
    bridges.push(make_twin_bridge(context, ty, equality))
  }
  let emitted : Map[@logic.Ty, Unit] = Map([])
  let result : Array[@theory.TheoryItem] = []
  for item in task.view().items {
    let seen : Array[@logic.Ty] = []
    let rewritten = match item {
      TheoryDecl(declaration) =>
        match declaration.view() {
          Dprop(kind, proposition, formula) =>
            twin_rewrite_proposition(
              context, declaration, kind, proposition, formula, bridges, seen,
            )
          Dlogic(_) | Dind(_) =>
            return fail_transform(
              UnsupportedStructure,
              stage,
              "logic or inductive declaration requires the full twin definition branch",
            )
          Dtype(_) | Ddata(_) | Dparam(_) => item
        }
      TheoryUse(_) | TheoryClone(_) | TheoryMeta(_) => item
    }
    for ty in seen.rev() {
      if emitted.contains(ty) {
        continue
      }
      guard find_twin_bridge(bridges, ty) is Some(bridge) else {
        return fail_transform(
          InvariantFailure,
          stage,
          "missing selected twin bridge",
        )
      }
      for declaration in bridge.declarations {
        result.push(declaration)
      }
      emitted[ty] = ()
    }
    result.push(rewritten)
  }
  checked_task(task.context_anchor(), result, stage)
}

///|
priv struct GuardSymbolEncoding {
  original : @logic.LSymbol
  encoded : @logic.LSymbol
  add_type_arguments : Bool
}

///|
priv struct GuardTypeRepresentation {
  type_symbol : @logic.TypeSymbol
  encoded : @logic.LSymbol
}

///|
fn guard_origin(
  name : BytesView,
  span : @identity.SourceSpan?,
  attributes : ArrayView[Bytes],
) -> @identity.Origin {
  @identity.Origin::generated(@identity.Guards, name, span, attributes)
}

///|
fn guard_abstract_type(
  context : @identity.CompilationContext,
  name : BytesView,
) -> (@logic.TypeSymbol, @logic.Ty) raise TransformError {
  let stage = @identity.Guards
  let origin = guard_origin(name, None, [])
  let symbol = @logic.TypeSymbol::new_abstract(context, name, origin, [], None) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "cannot create an encoding sort")
  }
  let ty = @logic.Ty::app(symbol, [], None) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "cannot apply an encoding sort")
  }
  (symbol, ty)
}

///|
fn guard_type_item(
  context : @identity.CompilationContext,
  symbol : @logic.TypeSymbol,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Guards
  let declaration = @logic.Decl::type_declaration(
    context,
    symbol.origin(),
    [symbol],
    None,
  ) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "cannot declare an encoding sort")
  }
  TheoryDecl(declaration)
}

///|
fn guard_parameter_item(
  context : @identity.CompilationContext,
  symbol : @logic.LSymbol,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Guards
  let declaration = @logic.Decl::parameter(
    context,
    symbol.view().origin,
    symbol,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot declare an encoded symbol",
      )
  }
  TheoryDecl(declaration)
}

///|
fn guard_monomorphic_type(
  ty : @logic.Ty,
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
) -> @logic.Ty {
  if kept.contains(ty) {
    ty
  } else {
    universal_type
  }
}

///|
fn guard_has_origin_attribute(
  origin : @identity.Origin,
  attribute : BytesView,
) -> Bool {
  origin.attributes().any(value => value[:] == attribute)
}

///|
fn guard_ordered_type_variables(
  variables : ArrayView[@logic.TyVarSymbol],
) -> Array[@logic.TyVarSymbol] {
  let ordered = variables.to_owned()
  ordered.sort_by((left, right) => left.name().lexical_compare(right.name()))
  ordered
}

///|
fn guard_encoded_symbol(
  context : @identity.CompilationContext,
  symbol : @logic.LSymbol,
  type_type : @logic.Ty,
  universal_type : @logic.Ty,
  kept : Map[@logic.Ty, Unit],
) -> GuardSymbolEncoding? raise TransformError {
  let stage = @identity.Guards
  let view = symbol.view()
  if !(view.role is Ordinary) {
    return fail_transform(
      UnsupportedStructure,
      stage,
      "constructor survived algebraic elimination",
    )
  }
  if is_builtin_equality(symbol) {
    return None
  }
  let protects_arguments = !guard_has_origin_attribute(
    view.origin,
    b"encoding:unprotecting",
  )
  let protects_result = !guard_has_origin_attribute(
    view.origin,
    b"encoding:unprotected",
  )
  let arguments : Array[@logic.Ty] = []
  for _ in view.type_parameters {
    arguments.push(type_type)
  }
  for ty in view.argument_types {
    arguments.push(
      if protects_arguments {
        guard_monomorphic_type(ty, kept, universal_type)
      } else {
        universal_type
      },
    )
  }
  let result_type = match view.result_type {
    None => None
    Some(ty) =>
      Some(
        if protects_result {
          guard_monomorphic_type(ty, kept, universal_type)
        } else {
          universal_type
        },
      )
  }
  if view.type_parameters.is_empty() &&
    arguments[:] == view.argument_types &&
    result_type == view.result_type {
    return None
  }
  let origin = guard_origin(
    view.name,
    derived_generated_span(view.origin),
    view.origin.attributes(),
  )
  let encoded = match result_type {
    Some(result_type) =>
      @logic.LSymbol::new_function(
        context,
        view.name,
        origin,
        arguments,
        result_type,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot create an encoded function",
          )
      }
    None =>
      @logic.LSymbol::new_predicate(context, view.name, origin, arguments, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot create an encoded predicate",
          )
      }
  }
  Some({
    original: symbol,
    encoded,
    add_type_arguments: !view.type_parameters.is_empty(),
  })
}

///|
fn find_guard_symbol_encoding(
  encodings : ArrayView[GuardSymbolEncoding],
  symbol : @logic.LSymbol,
) -> GuardSymbolEncoding? {
  for encoding in encodings {
    if encoding.original == symbol {
      return Some(encoding)
    }
  }
  None
}

///|
fn guard_type_representation(
  context : @identity.CompilationContext,
  symbol : @logic.TypeSymbol,
  type_type : @logic.Ty,
) -> GuardTypeRepresentation raise TransformError {
  let stage = @identity.Guards
  let view = symbol.view()
  let origin = guard_origin(
    view.name,
    derived_generated_span(view.origin),
    view.origin.attributes(),
  )
  let arguments = [ for _ in view.parameters => type_type ]
  let encoded = @logic.LSymbol::new_function(
    context,
    view.name,
    origin,
    arguments,
    type_type,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot create a type representation",
      )
  }
  { type_symbol: symbol, encoded }
}

///|
fn find_guard_type_representation(
  representations : ArrayView[GuardTypeRepresentation],
  symbol : @logic.TypeSymbol,
) -> @logic.LSymbol? {
  for representation in representations {
    if representation.type_symbol == symbol {
      return Some(representation.encoded)
    }
  }
  None
}

///|
fn guard_type_term(
  ty : @logic.Ty,
  type_variables : Map[@logic.TyVarSymbol, @logic.Term],
  representations : ArrayView[GuardTypeRepresentation],
  type_type : @logic.Ty,
) -> @logic.Term raise TransformError {
  let stage = @identity.Guards
  match ty.view() {
    TyVar(variable) =>
      match type_variables.get(variable) {
        Some(term) => term
        None =>
          fail_transform(
            InvariantFailure,
            stage,
            "missing encoded type variable",
          )
      }
    TyApp(symbol, arguments) => {
      guard find_guard_type_representation(representations, symbol)
        is Some(representation) else {
        return fail_transform(
          UnsupportedStructure,
          stage,
          "missing type representation symbol",
        )
      }
      let terms = [
        for argument in arguments => {
          guard_type_term(argument, type_variables, representations, type_type)
        }
      ]
      @logic.Term::elaborated_apply(
        representation,
        terms,
        Some(type_type),
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot apply a type representation",
          )
      }
    }
  }
}

///|
fn guard_encoded_variable(
  context : @identity.CompilationContext,
  variable : @logic.VSymbol,
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
) -> @logic.VSymbol raise TransformError {
  let stage = @identity.Guards
  let view = variable.view()
  let ty = if guard_has_origin_attribute(view.origin, b"encoding:unprotected") {
    universal_type
  } else {
    guard_monomorphic_type(view.ty, kept, universal_type)
  }
  if ty == view.ty {
    return variable
  }
  let origin = guard_origin(
    view.name,
    derived_generated_span(view.origin),
    view.origin.attributes(),
  )
  @logic.VSymbol::new(context, view.name, origin, ty, None) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "cannot encode a value variable")
  }
}

///|
fn guard_instantiated_type(
  instantiation : ArrayView[(@logic.TyVarSymbol, @logic.Ty)],
  variable : @logic.TyVarSymbol,
) -> @logic.Ty? {
  for entry in instantiation {
    if entry.0 == variable {
      return Some(entry.1)
    }
  }
  None
}

///|
fn guard_binary_formula(
  operator : @logic.BinaryLogicOp,
  left : @logic.Term,
  right : @logic.Term,
) -> @logic.Term raise TransformError {
  @logic.Term::binary(operator, left, right, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.Guards,
        "cannot rebuild a polar formula",
      )
  }
}

///|
fn guard_not_formula(term : @logic.Term) -> @logic.Term raise TransformError {
  @logic.Term::not(term, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.Guards,
        "cannot rebuild a polar negation",
      )
  }
}

///|
fn guard_if_formula(
  condition : @logic.Term,
  then_branch : @logic.Term,
  else_branch : @logic.Term,
) -> @logic.Term raise TransformError {
  @logic.Term::if_then_else(condition, then_branch, else_branch, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.Guards,
        "cannot rebuild a polar conditional",
      )
  }
}

///|
fn guard_collect_equal_variables(
  term : @logic.Term,
  variables : Map[@logic.VSymbol, Unit],
) -> Unit raise TransformError {
  match term.view() {
    Tvar(variable) => variables[variable] = ()
    Tapp(_, _, _) | Tconst(_) => ()
    Tif(_, then_branch, else_branch) => {
      guard_collect_equal_variables(then_branch, variables)
      guard_collect_equal_variables(else_branch, variables)
    }
    Tlet(variable, value, body) => {
      let from_value : Map[@logic.VSymbol, Unit] = Map([])
      guard_collect_equal_variables(value, from_value)
      guard_collect_equal_variables(body, variables)
      if variables.contains(variable) {
        variables.remove(variable)
        for candidate in from_value.keys() {
          variables[candidate] = ()
        }
      }
    }
    Tcase(_, branches) =>
      for branch in branches {
        guard_collect_equal_variables(branch.view().body, variables)
      }
    Teps(_, _)
    | Tquant(_, _, _, _)
    | Tbinop(_, _, _)
    | Tnot(_)
    | Ttrue
    | Tfalse =>
      fail_transform(
        InvariantFailure,
        @identity.Guards,
        "proposition reached equality variable collection",
      )
  }
}

///|
fn guard_is_infinite_type(
  ty : @logic.Ty,
  infinite_types : Map[@logic.TypeSymbol, Unit],
) -> Bool {
  match ty.view() {
    TyVar(_) => false
    TyApp(symbol, arguments) => {
      let is_function_type = match symbol.origin().snapshot_key() {
        Some(key) => {
          let view = key.view()
          view.theory_key == b"why3.HighOrd.HighOrd" &&
          view.theory_item_ordinal == 0U &&
          view.declaration_inner_ordinal == 0U &&
          view.symbol_kind is Type
        }
        None => false
      }
      if is_function_type && arguments.length() == 2 {
        guard_is_infinite_type(arguments[1], infinite_types)
      } else {
        infinite_types.contains(symbol)
      }
    }
  }
}

///|
fn guard_sort_formula(
  original_type : @logic.Ty,
  encoded_variable : @logic.VSymbol,
  type_variables : Map[@logic.TyVarSymbol, @logic.Term],
  representations : ArrayView[GuardTypeRepresentation],
  sort_symbol : @logic.LSymbol,
  type_type : @logic.Ty,
) -> @logic.Term raise TransformError {
  let represented_type = guard_type_term(
    original_type, type_variables, representations, type_type,
  )
  @logic.Term::elaborated_apply(
    sort_symbol,
    [represented_type, @logic.Term::variable(encoded_variable)],
    None,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        @identity.Guards,
        "cannot construct a variable guard",
      )
  }
}

///|
fn guard_encode_term(
  context : @identity.CompilationContext,
  term : @logic.Term,
  values : Map[@logic.VSymbol, @logic.Term],
  type_variables : Map[@logic.TyVarSymbol, @logic.Term],
  symbol_encodings : ArrayView[GuardSymbolEncoding],
  representations : ArrayView[GuardTypeRepresentation],
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
  type_type : @logic.Ty,
  sort_symbol : @logic.LSymbol,
  infinite_types : Map[@logic.TypeSymbol, Unit],
  polar : Bool,
  sign : Bool,
  equal_variables : Map[@logic.VSymbol, Unit],
) -> @logic.Term raise TransformError {
  let stage = @identity.Guards
  let recurse = fn(child) -> @logic.Term raise TransformError {
    guard_encode_term(
      context, child, values, type_variables, symbol_encodings, representations,
      kept, universal_type, type_type, sort_symbol, infinite_types, polar, sign,
      equal_variables,
    )
  }
  let replacement = match term.view() {
    Tvar(variable) =>
      match values.get(variable) {
        Some(value) => value
        None =>
          @logic.Term::variable(
            guard_encoded_variable(context, variable, kept, universal_type),
          )
      }
    Tconst(constant) => {
      guard term.ty() is Some(ty) && kept.contains(ty) else {
        return fail_transform(
          UnsupportedStructure,
          stage,
          "unprotected literal requires the constant-symbol encoding",
        )
      }
      @logic.Term::constant(constant, ty, None) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot retain a protected literal",
          )
      }
    }
    Tapp(symbol, instantiation, arguments) => {
      if is_builtin_equality(symbol) &&
        arguments.length() == 2 &&
        (!polar || sign) {
        guard_collect_equal_variables(arguments[0], equal_variables)
        guard_collect_equal_variables(arguments[1], equal_variables)
      }
      let mapped_arguments = [ for argument in arguments => recurse(argument) ]
      let (encoded_symbol, type_arguments) = match
        find_guard_symbol_encoding(symbol_encodings, symbol) {
        Some(encoding) => {
          let type_arguments : Array[@logic.Term] = []
          if encoding.add_type_arguments {
            let parameters = guard_ordered_type_variables(
              symbol.view().type_parameters,
            )
            for parameter in parameters.rev() {
              guard guard_instantiated_type(instantiation, parameter)
                is Some(actual) else {
                return fail_transform(
                  InvariantFailure,
                  stage,
                  "missing logic type instantiation",
                )
              }
              type_arguments.push(
                guard_type_term(
                  actual, type_variables, representations, type_type,
                ),
              )
            }
          }
          (encoding.encoded, type_arguments)
        }
        None => (symbol, [])
      }
      let encoded_arguments = type_arguments
      for argument in mapped_arguments {
        encoded_arguments.push(argument)
      }
      let result_type = encoded_symbol.view().result_type
      @logic.Term::elaborated_apply(
        encoded_symbol,
        encoded_arguments,
        result_type,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "cannot apply an encoded logic symbol",
          )
      }
    }
    Tif(condition, then_branch, else_branch) =>
      if term.ty() is Some(_) {
        let encoded_condition = guard_encode_term(
          context, condition, values, type_variables, symbol_encodings, representations,
          kept, universal_type, type_type, sort_symbol, infinite_types, false, sign,
          equal_variables,
        )
        guard_if_formula(
          encoded_condition,
          recurse(then_branch),
          recurse(else_branch),
        )
      } else {
        let condition_at_sign = recurse(condition)
        let condition_at_opposite = guard_encode_term(
          context,
          condition,
          values,
          type_variables,
          symbol_encodings,
          representations,
          kept,
          universal_type,
          type_type,
          sort_symbol,
          infinite_types,
          polar,
          !sign,
          equal_variables,
        )
        let encoded_then = recurse(then_branch)
        let encoded_else = recurse(else_branch)
        if condition_at_sign == condition_at_opposite {
          guard_if_formula(condition_at_sign, encoded_then, encoded_else)
        } else if sign {
          guard_binary_formula(
            And,
            guard_binary_formula(Implies, condition_at_opposite, encoded_then),
            guard_binary_formula(
              Implies,
              guard_not_formula(condition_at_sign),
              encoded_else,
            ),
          )
        } else {
          guard_binary_formula(
            Or,
            guard_binary_formula(And, condition_at_sign, encoded_then),
            guard_binary_formula(
              And,
              guard_not_formula(condition_at_opposite),
              encoded_else,
            ),
          )
        }
      }
    Tlet(variable, value, body) => {
      let from_value : Map[@logic.VSymbol, Unit] = Map([])
      guard_collect_equal_variables(value, from_value)
      let encoded_variable = guard_encoded_variable(
        context, variable, kept, universal_type,
      )
      let nested = values.copy()
      nested[variable] = @logic.Term::variable(encoded_variable)
      let encoded_body = guard_encode_term(
        context, body, nested, type_variables, symbol_encodings, representations,
        kept, universal_type, type_type, sort_symbol, infinite_types, polar, sign,
        equal_variables,
      )
      if equal_variables.contains(variable) {
        equal_variables.remove(variable)
        for candidate in from_value.keys() {
          equal_variables[candidate] = ()
        }
      }
      @logic.Term::let_in(encoded_variable, recurse(value), encoded_body, None) catch {
        _ => fail_transform(InvariantFailure, stage, "cannot encode a let term")
      }
    }
    Tcase(_, _) =>
      return fail_transform(
        UnsupportedStructure,
        stage,
        "case survived algebraic elimination",
      )
    Teps(_, _) =>
      return fail_transform(
        UnsupportedStructure,
        stage,
        "epsilon survived elimination",
      )
    Tquant(quantifier, binders, triggers, body) => {
      let nested = values.copy()
      let encoded_binders : Array[@logic.VSymbol] = []
      for binder in binders {
        let encoded = guard_encoded_variable(
          context, binder, kept, universal_type,
        )
        encoded_binders.push(encoded)
        nested[binder] = @logic.Term::variable(encoded)
      }
      let encoded_triggers = [
        for group in triggers => {
          [
            for trigger in group => {
              guard_encode_term(
                context, trigger, nested, type_variables, symbol_encodings, representations,
                kept, universal_type, type_type, sort_symbol, infinite_types, polar,
                sign, equal_variables,
              )
            }
          ]
        }
      ]
      let encoded_body = guard_encode_term(
        context, body, nested, type_variables, symbol_encodings, representations,
        kept, universal_type, type_type, sort_symbol, infinite_types, polar, sign,
        equal_variables,
      )
      let mut guarded_body = encoded_body
      for index = binders.length() - 1; index >= 0; index = index - 1 {
        let original = binders[index]
        let encoded = encoded_binders[index]
        let view = original.view()
        let is_protected = kept.contains(view.ty) &&
          !guard_has_origin_attribute(view.origin, b"encoding:unprotected")
        let skip = is_protected ||
          (
            polar &&
            sign == (quantifier is ForallQuantifier) &&
            (
              !equal_variables.contains(original) ||
              guard_is_infinite_type(view.ty, infinite_types)
            )
          )
        equal_variables.remove(original)
        if !skip {
          let guard_formula = guard_sort_formula(
            view.ty,
            encoded,
            type_variables,
            representations,
            sort_symbol,
            type_type,
          )
          guarded_body = guard_binary_formula(
            if quantifier is ForallQuantifier {
              Implies
            } else {
              And
            },
            guard_formula,
            guarded_body,
          )
        }
      }
      @logic.Term::quantify(
        quantifier,
        encoded_binders,
        encoded_triggers,
        guarded_body,
        None,
      ) catch {
        _ =>
          fail_transform(InvariantFailure, stage, "cannot encode a quantifier")
      }
    }
    Tbinop(Implies, left, right) => {
      let encoded_left = guard_encode_term(
        context,
        left,
        values,
        type_variables,
        symbol_encodings,
        representations,
        kept,
        universal_type,
        type_type,
        sort_symbol,
        infinite_types,
        polar,
        !sign,
        equal_variables,
      )
      guard_binary_formula(Implies, encoded_left, recurse(right))
    }
    Tbinop(Iff, left, right) => {
      let left_at_sign = recurse(left)
      let left_at_opposite = guard_encode_term(
        context,
        left,
        values,
        type_variables,
        symbol_encodings,
        representations,
        kept,
        universal_type,
        type_type,
        sort_symbol,
        infinite_types,
        polar,
        !sign,
        equal_variables,
      )
      let right_at_sign = recurse(right)
      let right_at_opposite = guard_encode_term(
        context,
        right,
        values,
        type_variables,
        symbol_encodings,
        representations,
        kept,
        universal_type,
        type_type,
        sort_symbol,
        infinite_types,
        polar,
        !sign,
        equal_variables,
      )
      if left_at_sign == left_at_opposite && right_at_sign == right_at_opposite {
        guard_binary_formula(Iff, left_at_sign, right_at_sign)
      } else if sign {
        guard_binary_formula(
          And,
          guard_binary_formula(Implies, left_at_opposite, right_at_sign),
          guard_binary_formula(Implies, right_at_opposite, left_at_sign),
        )
      } else {
        guard_binary_formula(
          Implies,
          guard_binary_formula(Or, left_at_opposite, right_at_opposite),
          guard_binary_formula(And, left_at_sign, right_at_sign),
        )
      }
    }
    Tbinop(operator, left, right) =>
      guard_binary_formula(operator, recurse(left), recurse(right))
    Tnot(inner) => {
      let encoded = guard_encode_term(
        context,
        inner,
        values,
        type_variables,
        symbol_encodings,
        representations,
        kept,
        universal_type,
        type_type,
        sort_symbol,
        infinite_types,
        polar,
        !sign,
        equal_variables,
      )
      guard_not_formula(encoded)
    }
    Ttrue => @logic.Term::true_formula()
    Tfalse => @logic.Term::false_formula()
  }
  copy_term_decoration(term, replacement)
}

///|
fn guard_type_variable(
  context : @identity.CompilationContext,
  variable : @logic.TyVarSymbol,
  type_type : @logic.Ty,
) -> @logic.VSymbol raise TransformError {
  let stage = @identity.Guards
  let name = variable.name()
  let origin = guard_origin(name, None, variable.origin().attributes())
  @logic.VSymbol::new(context, name, origin, type_type, None) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "cannot quantify an encoded type")
  }
}

///|
fn guard_encode_formula(
  context : @identity.CompilationContext,
  formula : @logic.Term,
  symbol_encodings : ArrayView[GuardSymbolEncoding],
  representations : ArrayView[GuardTypeRepresentation],
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
  type_type : @logic.Ty,
  sort_symbol : @logic.LSymbol,
  infinite_types : Map[@logic.TypeSymbol, Unit],
  sign : Bool,
) -> @logic.Term raise TransformError {
  let stage = @identity.Guards
  let type_variables : Map[@logic.TyVarSymbol, @logic.Term] = Map([])
  let binders : Array[@logic.VSymbol] = []
  let free_type_variables = formula.free_type_variables()
  let free_type_variables = guard_ordered_type_variables(free_type_variables[:])
  for variable in free_type_variables {
    let binder = guard_type_variable(context, variable, type_type)
    binders.push(binder)
    type_variables[variable] = @logic.Term::variable(binder)
  }
  let encoded = guard_encode_term(
    context,
    formula,
    Map([]),
    type_variables,
    symbol_encodings,
    representations,
    kept,
    universal_type,
    type_type,
    sort_symbol,
    infinite_types,
    true,
    sign,
    Map([]),
  )
  if binders.is_empty() {
    return encoded
  }
  @logic.Term::quantify(ForallQuantifier, binders, [], encoded, None) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot close encoded type variables",
      )
  }
}

///|
fn guard_generated_proposition(
  context : @identity.CompilationContext,
  name : BytesView,
  formula : @logic.Term,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Guards
  let origin = guard_origin(name, None, [])
  let proposition = @logic.PrSymbol::new(context, name, origin)
  let declaration = @logic.Decl::proposition(
    context,
    origin,
    Paxiom,
    proposition,
    formula,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot declare an encoding axiom",
      )
  }
  TheoryDecl(declaration)
}

///|
fn guard_witness_axiom(
  context : @identity.CompilationContext,
  sort_symbol : @logic.LSymbol,
  witness_symbol : @logic.LSymbol,
  universal_type : @logic.Ty,
  type_type : @logic.Ty,
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Guards
  let variable = @logic.VSymbol::new(
    context,
    b"a",
    guard_origin(b"a", None, []),
    type_type,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot create witness type binder",
      )
  }
  let type_term = @logic.Term::variable(variable)
  let witness = @logic.Term::elaborated_apply(
    witness_symbol,
    [type_term],
    Some(universal_type),
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "cannot apply witness")
  }
  let formula = @logic.Term::elaborated_apply(
    sort_symbol,
    [type_term, witness],
    None,
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "cannot type witness")
  }
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    [variable],
    [],
    formula,
    None,
  ) catch {
    _ => fail_transform(InvariantFailure, stage, "cannot quantify witness type")
  }
  guard_generated_proposition(context, b"witness_sort", formula)
}

///|
fn guard_symbol_sort_axiom(
  context : @identity.CompilationContext,
  original : @logic.LSymbol,
  encoded : @logic.LSymbol,
  sort_symbol : @logic.LSymbol,
  representations : ArrayView[GuardTypeRepresentation],
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
  type_type : @logic.Ty,
) -> @theory.TheoryItem? raise TransformError {
  let stage = @identity.Guards
  let view = original.view()
  guard view.result_type is Some(result_type) &&
    (
      !kept.contains(result_type) ||
      guard_has_origin_attribute(view.origin, b"encoding:unprotected")
    ) else {
    return None
  }
  let type_variables : Map[@logic.TyVarSymbol, @logic.Term] = Map([])
  let type_binders : Array[@logic.VSymbol] = []
  let ordered_type_variables = guard_ordered_type_variables(
    view.type_parameters,
  )
  for variable in ordered_type_variables {
    let binder = guard_type_variable(context, variable, type_type)
    type_binders.push(binder)
    type_variables[variable] = @logic.Term::variable(binder)
  }
  let value_binders : Array[@logic.VSymbol] = []
  for formal in view.argument_types {
    let ty = guard_monomorphic_type(formal, kept, universal_type)
    let binder = @logic.VSymbol::new(
      context,
      b"x",
      guard_origin(b"x", None, []),
      ty,
      None,
    ) catch {
      _ =>
        fail_transform(
          InvariantFailure,
          stage,
          "cannot create sort-axiom binder",
        )
    }
    value_binders.push(binder)
  }
  let application_arguments : Array[@logic.Term] = []
  for binder in type_binders.rev() {
    application_arguments.push(@logic.Term::variable(binder))
  }
  for binder in value_binders {
    application_arguments.push(@logic.Term::variable(binder))
  }
  let application = @logic.Term::elaborated_apply(
    encoded,
    application_arguments,
    encoded.view().result_type,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot apply symbol in sort axiom",
      )
  }
  let result_sort = guard_type_term(
    result_type, type_variables, representations, type_type,
  )
  let formula = @logic.Term::elaborated_apply(
    sort_symbol,
    [result_sort, application],
    None,
    None,
  ) catch {
    _ =>
      fail_transform(InvariantFailure, stage, "cannot construct a sort axiom")
  }
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    value_binders,
    [],
    formula,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot quantify sort-axiom values",
      )
  }
  let formula = @logic.Term::quantify(
    ForallQuantifier,
    type_binders,
    [],
    formula,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot quantify sort-axiom types",
      )
  }
  let name = view.name + b"_sort"
  Some(guard_generated_proposition(context, name, formula))
}

///|
fn guard_rebuild_proposition(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
  kind : @logic.PropositionKind,
  proposition : @logic.PrSymbol,
  formula : @logic.Term,
  symbol_encodings : ArrayView[GuardSymbolEncoding],
  representations : ArrayView[GuardTypeRepresentation],
  kept : Map[@logic.Ty, Unit],
  universal_type : @logic.Ty,
  type_type : @logic.Ty,
  sort_symbol : @logic.LSymbol,
  infinite_types : Map[@logic.TypeSymbol, Unit],
) -> @theory.TheoryItem raise TransformError {
  let stage = @identity.Guards
  let formula = guard_encode_formula(
    context,
    formula,
    symbol_encodings,
    representations,
    kept,
    universal_type,
    type_type,
    sort_symbol,
    infinite_types,
    !(kind is Pgoal),
  )
  let declaration = @logic.Decl::proposition(
    context,
    declaration.origin(),
    kind,
    proposition,
    formula,
    None,
  ) catch {
    _ =>
      fail_transform(
        InvariantFailure,
        stage,
        "cannot rebuild an encoded proposition",
      )
  }
  TheoryDecl(declaration)
}

///|
pub fn encoding_guards(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.Guards
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return task
  }
  if task_has_meta(task, b"encoding:base") {
    return fail_transform(
      UnsupportedStructure,
      stage,
      "custom encoding base is outside the frozen profile",
    )
  }
  let (universal_symbol, universal_type) = guard_abstract_type(context, b"uni")
  let (type_symbol, type_type) = guard_abstract_type(context, b"ty")
  let kept = kept_type_set(task)
  kept[type_type] = ()
  let infinite_types : Map[@logic.TypeSymbol, Unit] = Map([])
  for item in task.view().items {
    if item is TheoryMeta(meta) &&
      meta.view()
      is { name: b"infinite_type", arguments: [MetaTypeSymbol(symbol)] } {
      infinite_types[symbol] = ()
    }
  }
  let mut equality_item : @theory.TheoryItem? = None
  let mut equality_symbol : @logic.LSymbol? = None
  for item in task.view().items {
    if item is TheoryDecl(declaration) &&
      declaration.view() is Dparam(symbol) &&
      is_builtin_equality(symbol) {
      equality_item = Some(item)
      equality_symbol = Some(symbol)
    }
  }
  guard equality_item is Some(equality_item) && equality_symbol is Some(_) else {
    return fail_transform(
      InvariantFailure,
      stage,
      "task has no equality declaration",
    )
  }
  let sort_origin = guard_origin(b"sort", None, [])
  let sort_symbol = @logic.LSymbol::new_predicate(
    context,
    b"sort",
    sort_origin,
    [type_type, universal_type],
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot create sort predicate",
      )
  }
  let witness_origin = guard_origin(b"witness", None, [])
  let witness_symbol = @logic.LSymbol::new_function(
    context,
    b"witness",
    witness_origin,
    [type_type],
    universal_type,
    None,
  ) catch {
    _ =>
      return fail_transform(
        InvariantFailure,
        stage,
        "cannot create witness function",
      )
  }
  let representations : Array[GuardTypeRepresentation] = []
  for item in task.view().items {
    if item is TheoryDecl(declaration) {
      match declaration.view() {
        Dtype(symbols) =>
          for symbol in symbols {
            representations.push(
              guard_type_representation(context, symbol, type_type),
            )
          }
        Ddata(declarations) =>
          for data in declarations {
            representations.push(
              guard_type_representation(
                context,
                data.view().type_symbol,
                type_type,
              ),
            )
          }
        Dparam(_) | Dlogic(_) | Dind(_) | Dprop(_, _, _) => ()
      }
    }
  }
  let symbol_encodings : Array[GuardSymbolEncoding] = []
  for item in task.view().items {
    if item is TheoryDecl(declaration) && declaration.view() is Dparam(symbol) {
      if guard_encoded_symbol(context, symbol, type_type, universal_type, kept)
        is Some(encoding) {
        symbol_encodings.push(encoding)
      }
    }
  }
  let result : Array[@theory.TheoryItem] = [
    guard_type_item(context, universal_symbol),
    guard_type_item(context, type_symbol),
    equality_item,
    guard_parameter_item(context, sort_symbol),
    guard_parameter_item(context, witness_symbol),
    guard_witness_axiom(
      context, sort_symbol, witness_symbol, universal_type, type_type,
    ),
  ]
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) =>
        match declaration.view() {
          Dtype(symbols) => {
            result.push(item)
            for symbol in symbols {
              guard find_guard_type_representation(representations, symbol)
                is Some(representation) else {
                return fail_transform(
                  InvariantFailure,
                  stage,
                  "missing declared type representation",
                )
              }
              result.push(guard_parameter_item(context, representation))
            }
          }
          Ddata(declarations) => {
            result.push(item)
            for data in declarations {
              let symbol = data.view().type_symbol
              guard find_guard_type_representation(representations, symbol)
                is Some(representation) else {
                return fail_transform(
                  InvariantFailure,
                  stage,
                  "missing data type representation",
                )
              }
              result.push(guard_parameter_item(context, representation))
            }
          }
          Dparam(symbol) => {
            if is_builtin_equality(symbol) {
              continue
            }
            match find_guard_symbol_encoding(symbol_encodings, symbol) {
              None => result.push(item)
              Some(encoding) => {
                result.push(guard_parameter_item(context, encoding.encoded))
                if guard_symbol_sort_axiom(
                    context,
                    symbol,
                    encoding.encoded,
                    sort_symbol,
                    representations,
                    kept,
                    universal_type,
                    type_type,
                  )
                  is Some(axiom) {
                  result.push(axiom)
                }
              }
            }
          }
          Dprop(kind, proposition, formula) =>
            result.push(
              guard_rebuild_proposition(
                context, declaration, kind, proposition, formula, symbol_encodings,
                representations, kept, universal_type, type_type, sort_symbol, infinite_types,
              ),
            )
          Dlogic(_) | Dind(_) =>
            return fail_transform(
              UnsupportedStructure,
              stage,
              "complex declaration survived the frozen guards prefix",
            )
        }
      TheoryUse(_) | TheoryMeta(_) => result.push(item)
      TheoryClone(_) => result.push(item)
    }
  }
  checked_task(task.context_anchor(), result, stage)
}

///|
pub fn encoding_smt_if_poly(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.EncodingSmtIfPoly
  require_task_context(context, task, stage)
  task
}
