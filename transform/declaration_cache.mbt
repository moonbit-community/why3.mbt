// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-28.

///|
/// Why3 memoizes declaration transforms with weak keys. Declarations rooted
/// in raw split tasks remain live across goals; intermediate declarations are
/// cacheable only during the goal that produced them unless an upstream cache
/// retains them.
let declaration_cache_generation : Ref[Int64] = Ref(0L)

///|
let persistent_declarations : Ref[Map[@identity.DeclarationId, Unit]] = Ref(
  Map([]),
)

///|
/// `encoding:kept` declarations created from goal-local discrimination or
/// selection are weak hash-cons keys in Why3. Record them for the current
/// goal so dependent encoding transforms do not retain declaration caches
/// beyond the lifetime of that meta set.
let dynamic_encoding_kept : Ref[Map[@logic.Ty, Int64]] = Ref(Map([]))

///|
pub fn begin_declaration_cache_goal(task : @theory.Task) -> Unit {
  declaration_cache_generation.val = declaration_cache_generation.val + 1L
  let persistent = persistent_declarations.val
  for item in task.view().items {
    if item is TheoryDecl(declaration) {
      persistent[declaration.declaration_id()] = ()
    }
  }
  persistent_declarations.val = persistent
}

///|
fn current_declaration_cache_generation() -> Int64 {
  declaration_cache_generation.val
}

///|
fn mark_dynamic_encoding_kept(ty : @logic.Ty) -> Unit {
  let entries = dynamic_encoding_kept.val
  entries[ty] = current_declaration_cache_generation()
  dynamic_encoding_kept.val = entries
}

///|
fn task_has_dynamic_encoding_kept(task : @theory.Task) -> Bool {
  let generation = current_declaration_cache_generation()
  for item in task.view().items {
    if item is TheoryMeta(meta) &&
      meta.view() is { name: b"encoding:kept", arguments: [MetaType(ty)], .. } &&
      dynamic_encoding_kept.val.get(ty) == Some(generation) {
      return true
    }
  }
  false
}

///|
fn declaration_cache_is_persistent(declaration : @logic.Decl) -> Bool {
  persistent_declarations.val.contains(declaration.declaration_id())
}

///|
fn declaration_cache_retain(declaration : @logic.Decl) -> Unit {
  let persistent = persistent_declarations.val
  persistent[declaration.declaration_id()] = ()
  persistent_declarations.val = persistent
}

///|
fn declaration_cache_definition_equal(
  left : @logic.LogicDefinition,
  right : @logic.LogicDefinition,
) -> Bool {
  let left = left.view()
  let right = right.view()
  left.symbol == right.symbol &&
  left.parameters == right.parameters &&
  left.decreasing_parameters == right.decreasing_parameters &&
  left.body == right.body
}

///|
fn declaration_cache_data_equal(
  left : @logic.DataDeclaration,
  right : @logic.DataDeclaration,
) -> Bool {
  let left = left.view()
  let right = right.view()
  if left.type_symbol != right.type_symbol ||
    left.constructors.length() != right.constructors.length() {
    return false
  }
  for index, constructor in left.constructors {
    let left = constructor.view()
    let right = right.constructors[index].view()
    if left.symbol != right.symbol || left.projections != right.projections {
      return false
    }
  }
  true
}

///|
fn declaration_cache_inductive_equal(
  left : @logic.InductiveDeclaration,
  right : @logic.InductiveDeclaration,
) -> Bool {
  let left = left.view()
  let right = right.view()
  if left.predicate != right.predicate ||
    left.cases.length() != right.cases.length() {
    return false
  }
  for index, case_ in left.cases {
    let left = case_.view()
    let right = right.cases[index].view()
    if left.proposition != right.proposition || left.formula != right.formula {
      return false
    }
  }
  true
}

///|
fn declaration_cache_equivalent(
  left : @logic.Decl,
  right : @logic.Decl,
) -> Bool {
  if left.origin() != right.origin() {
    return false
  }
  match (left.view(), right.view()) {
    (Dtype(left), Dtype(right)) => left == right
    (Ddata(left), Ddata(right)) => {
      if left.length() != right.length() {
        return false
      }
      for index, declaration in left {
        if !declaration_cache_data_equal(declaration, right[index]) {
          return false
        }
      }
      true
    }
    (Dparam(left), Dparam(right)) => left == right
    (Dlogic(left), Dlogic(right)) => {
      if left.length() != right.length() {
        return false
      }
      for index, definition in left {
        if !declaration_cache_definition_equal(definition, right[index]) {
          return false
        }
      }
      true
    }
    (Dind(left_sign, left), Dind(right_sign, right)) => {
      if left_sign != right_sign || left.length() != right.length() {
        return false
      }
      for index, declaration in left {
        if !declaration_cache_inductive_equal(declaration, right[index]) {
          return false
        }
      }
      true
    }
    (
      Dprop(left_kind, left_proposition, left_formula),
      Dprop(right_kind, right_proposition, right_formula),
    ) =>
      left_kind == right_kind &&
      left_proposition == right_proposition &&
      left_formula == right_formula
    _ => false
  }
}

///|
fn propagate_persistent_declarations(
  original : @theory.Task,
  items : ArrayView[@theory.TheoryItem],
) -> Unit {
  let roots : Map[@identity.SemanticId, Array[@logic.Decl]] = Map([])
  for item in original.view().items {
    guard item is TheoryDecl(declaration) &&
      declaration_cache_is_persistent(declaration) else {
      continue
    }
    for introduced in declaration.introduced_symbols() {
      let id = introduced.semantic_id()
      let declarations = match roots.get(id) {
        Some(declarations) => declarations
        None => {
          let declarations : Array[@logic.Decl] = []
          roots[id] = declarations
          declarations
        }
      }
      declarations.push(declaration)
    }
  }
  for item in items {
    guard item is TheoryDecl(declaration) &&
      !declaration_cache_is_persistent(declaration) else {
      continue
    }
    let mut retained = false
    for introduced in declaration.introduced_symbols() {
      match roots.get(introduced.semantic_id()) {
        Some(candidates) =>
          if candidates.any(candidate => {
              declaration_cache_equivalent(candidate, declaration)
            }) {
            declaration_cache_retain(declaration)
            retained = true
          }
        None => ()
      }
      if retained {
        break
      }
    }
  }
}
