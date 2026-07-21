// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn kept_algebraic_type(ty : @logic.Ty, kept : ArrayView[@logic.Ty]) -> Bool {
  kept.contains(ty)
}

///|
fn algebraic_passthrough_term(
  term : @logic.Term,
  kept : ArrayView[@logic.Ty],
) -> Bool {
  let children = fn(values : ArrayView[@logic.Term]) -> Bool {
    values.all(value => algebraic_passthrough_term(value, kept))
  }
  match term.view() {
    Tapp(symbol, _, arguments) => {
      let permitted = match symbol.view().role {
        Ordinary => true
        Constructor(_) => term.ty() is Some(ty) && kept_algebraic_type(ty, kept)
        Projection =>
          !arguments.is_empty() &&
          arguments[0].ty() is Some(ty) &&
          kept_algebraic_type(ty, kept)
      }
      permitted && children(arguments)
    }
    Tif(condition, then_branch, else_branch) =>
      algebraic_passthrough_term(condition, kept) &&
      algebraic_passthrough_term(then_branch, kept) &&
      algebraic_passthrough_term(else_branch, kept)
    Tlet(_, value, body) =>
      algebraic_passthrough_term(value, kept) &&
      algebraic_passthrough_term(body, kept)
    Tcase(_, _) => false
    Teps(_, body) => algebraic_passthrough_term(body, kept)
    Tquant(_, _, triggers, body) =>
      triggers.all(group => children(group)) &&
      algebraic_passthrough_term(body, kept)
    Tbinop(_, left, right) =>
      algebraic_passthrough_term(left, kept) &&
      algebraic_passthrough_term(right, kept)
    Tnot(inner) => algebraic_passthrough_term(inner, kept)
    Tvar(_) | Tconst(_) | Ttrue | Tfalse => true
  }
}

///|
fn kept_nullary_data_declaration(
  declaration : @logic.DataDeclaration,
  kept : ArrayView[@logic.Ty],
) -> Bool {
  let view = declaration.view()
  if view.type_symbol.arity() != 0 {
    return false
  }
  let instance = @logic.Ty::app(view.type_symbol, [], None) catch {
    _ => return false
  }
  kept_algebraic_type(instance, kept) &&
  view.constructors.all(data_constructor => {
    let data_constructor = data_constructor.view()
    data_constructor.symbol.view().argument_types.is_empty() &&
    data_constructor.projections.is_empty()
  })
}

///|
fn algebraic_passthrough_declaration(
  declaration : @logic.Decl,
  kept : ArrayView[@logic.Ty],
) -> Bool {
  match declaration.view() {
    Dtype(_) => true
    Ddata(declarations) =>
      declarations.all(data => kept_nullary_data_declaration(data, kept))
    Dind(_) => false
    Dparam(symbol) => {
      let view = symbol.view()
      match view.role {
        Ordinary => true
        Constructor(_) =>
          view.result_type is Some(ty) && kept_algebraic_type(ty, kept)
        Projection =>
          !view.argument_types.is_empty() &&
          kept_algebraic_type(view.argument_types[0], kept)
      }
    }
    Dlogic(definitions) =>
      definitions.all(definition => {
        algebraic_passthrough_term(definition.view().body, kept)
      })
    Dprop(_, _, formula) => algebraic_passthrough_term(formula, kept)
  }
}

///|
fn tagged_algebraic_types(task : @theory.Task) -> Array[@logic.Ty] {
  let kept : Array[@logic.Ty] = []
  for item in task.view().items {
    guard item is TheoryMeta(meta) else { continue }
    let view = meta.view()
    if view.name == b"algebraic:kept" &&
      view.arguments.length() == 1 &&
      view.arguments[0] is MetaType(ty) &&
      !kept.contains(ty) {
      kept.push(ty)
    }
  }
  kept
}

///|
fn tuple_zero_key(key : @theory.TheoryKey) -> Bool {
  let view = key.view()
  view.path == [b"why3", b"Tuple0"] && view.name == b"Tuple0"
}

///|
fn required_builtin_type(
  candidate : @logic.TypeSymbol?,
  expected : @logic.BuiltinTypeKind,
  stage : @identity.GeneratedStage,
) -> @logic.TypeSymbol raise TransformError {
  guard candidate is Some(symbol) && symbol.builtin_kind() == Some(expected) else {
    return fail_transform(
      InvariantFailure,
      stage,
      "static profile is missing an encoding base type",
    )
  }
  symbol
}

///|
/// Narrow exact branch of `Eliminate_algebraic.eliminate_algebraic`.  The
/// supported polymorphic closure has no algebraic declaration or match at this
/// point, so the upstream fold contributes only its fixed infinite-type/equal
/// prefix, removes the Tuple0 use, and replays the remaining task.
pub fn eliminate_algebraic_if_poly(
  context : @identity.CompilationContext,
  task : @theory.Task,
  integer_type : @logic.TypeSymbol?,
  real_type : @logic.TypeSymbol?,
  string_type : @logic.TypeSymbol?,
) -> @theory.Task raise TransformError {
  let stage = @identity.EliminateAlgebraicIfPoly
  require_task_context(context, task, stage)
  if task_has_meta(task, b"encoding:monomorphic_only") {
    return eliminate_projections_sums(context, task)
  }
  let integer_type = required_builtin_type(integer_type, BuiltinInteger, stage)
  let real_type = required_builtin_type(real_type, BuiltinReal, stage)
  let string_type = required_builtin_type(string_type, BuiltinString, stage)
  let kept_algebraic = tagged_algebraic_types(task)
  let mut equality : @theory.TheoryItem? = None
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) if declaration.view() is Dparam(symbol) &&
        is_builtin_equality(symbol) => equality = Some(item)
      _ => ()
    }
  }
  guard equality is Some(equality) else {
    return fail_transform(
      InvariantFailure,
      stage,
      "task has no builtin equality parameter",
    )
  }
  let result : Array[@theory.TheoryItem] = [
    TheoryMeta(
      @theory.Meta::new(b"infinite_type", [MetaTypeSymbol(integer_type)]),
    ),
    TheoryMeta(@theory.Meta::new(b"infinite_type", [MetaTypeSymbol(real_type)])),
    TheoryMeta(
      @theory.Meta::new(b"infinite_type", [MetaTypeSymbol(string_type)]),
    ),
    equality,
  ]
  let mut goal : @theory.TheoryItem? = None
  let input = task.view().items
  for index, item in input {
    if index + 1 == input.length() &&
      item is TheoryDecl(declaration) &&
      declaration.view() is Dprop(Pgoal, _, _) {
      goal = Some(item)
      continue
    }
    match item {
      TheoryDecl(declaration) => {
        if declaration.view() is Dparam(symbol) && is_builtin_equality(symbol) {
          continue
        }
        if !algebraic_passthrough_declaration(declaration, kept_algebraic) {
          return fail_transform(
            UnsupportedStructure,
            stage,
            "algebraic declaration or match requires the full elimination branch",
          )
        }
        result.push(item)
      }
      TheoryUse(key) => if !tuple_zero_key(key) { result.push(item) }
      TheoryMeta(meta) => {
        if meta.view().name == b"infinite_type" {
          return fail_transform(
            UnsupportedStructure,
            stage,
            "explicit infinite_type is outside the frozen profile",
          )
        }
        result.push(item)
      }
      TheoryClone(_) => result.push(item)
    }
  }
  for ty in kept_algebraic {
    result.push(TheoryMeta(@theory.Meta::new(b"encoding:kept", [MetaType(ty)])))
  }
  guard goal is Some(goal) else {
    return fail_transform(InvalidTask, stage, "task has no final goal")
  }
  guard goal is TheoryDecl(goal_declaration) &&
    algebraic_passthrough_declaration(goal_declaration, kept_algebraic) else {
    return fail_transform(
      UnsupportedStructure,
      stage,
      "algebraic match in the goal requires the full elimination branch",
    )
  }
  result.push(goal)
  checked_task(task.context_anchor(), result, stage)
}
