// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
priv struct CoercionPath {
  source_symbol : @logic.TypeSymbol
  source_arguments : Array[@logic.Ty]
  target_symbol : @logic.TypeSymbol
  target_arguments : Array[@logic.Ty]
  functions : Array[@logic.LSymbol]
  direct : Bool
}

///|
/// A transitively closed set of implicit logic coercions.
struct CoercionMap {
  paths : Map[@logic.TypeSymbol, Map[@logic.TypeSymbol, CoercionPath]]
}

///|
pub fn CoercionMap::empty() -> CoercionMap {
  { paths: Map([]) }
}

///|
fn CoercionMap::copy(self : CoercionMap) -> CoercionMap {
  let paths : Map[@logic.TypeSymbol, Map[@logic.TypeSymbol, CoercionPath]] = Map([],
  )
  for source, targets in self.paths {
    paths[source] = targets.copy()
  }
  { paths, }
}

///|
fn make_coercion_path(
  function_ : @logic.LSymbol,
  span : @identity.SourceSpan?,
) -> CoercionPath raise TheoryError {
  let view = function_.view()
  guard view.argument_types is [source] &&
    view.result_type is Some(target) &&
    source.view() is TyApp(source_symbol, source_arguments) &&
    target.view() is TyApp(target_symbol, target_arguments) &&
    source_symbol != target_symbol else {
    fail_theory(NotACoercion, span, "logic symbol cannot be used as a coercion")
  }
  {
    source_symbol,
    source_arguments: source_arguments.to_owned(),
    target_symbol,
    target_arguments: target_arguments.to_owned(),
    functions: [function_],
    direct: true,
  }
}

///|
fn CoercionMap::path(
  self : CoercionMap,
  source : @logic.TypeSymbol,
  target : @logic.TypeSymbol,
) -> CoercionPath? {
  match self.paths.get(source) {
    Some(targets) => targets.get(target)
    None => None
  }
}

///|
fn insert_coercion_path(
  paths : Map[@logic.TypeSymbol, Map[@logic.TypeSymbol, CoercionPath]],
  path : CoercionPath,
  span : @identity.SourceSpan?,
) -> Unit raise TheoryError {
  match paths.get(path.target_symbol) {
    Some(reverse) =>
      if reverse.contains(path.source_symbol) {
        fail_theory(CoercionCycle, span, "coercion introduces a cycle")
      }
    None => ()
  }
  match paths.get(path.source_symbol) {
    Some(targets) =>
      match targets.get(path.target_symbol) {
        Some(existing) =>
          if existing.functions != path.functions {
            fail_theory(
              CoercionAlreadyDefined,
              span,
              "a different coercion path is already defined",
            )
          }
        None => targets[path.target_symbol] = path
      }
    None => {
      let targets : Map[@logic.TypeSymbol, CoercionPath] = Map([])
      targets[path.target_symbol] = path
      paths[path.source_symbol] = targets
    }
  }
}

///|
fn compose_coercion_paths(
  left : CoercionPath,
  right : CoercionPath,
) -> CoercionPath {
  let functions = left.functions.copy()
  for function_ in right.functions {
    functions.push(function_)
  }
  {
    source_symbol: left.source_symbol,
    source_arguments: left.source_arguments.copy(),
    target_symbol: right.target_symbol,
    target_arguments: right.target_arguments.copy(),
    functions,
    direct: false,
  }
}

///|
fn outgoing_coercion_paths(
  paths : Map[@logic.TypeSymbol, Map[@logic.TypeSymbol, CoercionPath]],
  source : @logic.TypeSymbol,
) -> Array[CoercionPath] {
  match paths.get(source) {
    Some(targets) => {
      let result : Array[CoercionPath] = []
      for _, path in targets {
        result.push(path)
      }
      result
    }
    None => []
  }
}

///|
fn incoming_coercion_paths(
  paths : Map[@logic.TypeSymbol, Map[@logic.TypeSymbol, CoercionPath]],
  target : @logic.TypeSymbol,
) -> Array[CoercionPath] {
  let result : Array[CoercionPath] = []
  for _, targets in paths {
    match targets.get(target) {
      Some(path) => result.push(path)
      None => ()
    }
  }
  result
}

///|
fn add_coercion_path(
  map : CoercionMap,
  path : CoercionPath,
  span : @identity.SourceSpan?,
) -> CoercionMap raise TheoryError {
  let result = map.copy()
  insert_coercion_path(result.paths, path, span)
  let outgoing = outgoing_coercion_paths(result.paths, path.target_symbol)
  for right in outgoing {
    insert_coercion_path(
      result.paths,
      compose_coercion_paths(path, right),
      span,
    )
  }
  let incoming = incoming_coercion_paths(result.paths, path.source_symbol)
  for left in incoming {
    let through_new = compose_coercion_paths(left, path)
    insert_coercion_path(result.paths, through_new, span)
    for right in outgoing {
      insert_coercion_path(
        result.paths,
        compose_coercion_paths(through_new, right),
        span,
      )
    }
  }
  result
}

///|
pub fn CoercionMap::add(
  self : CoercionMap,
  function_ : @logic.LSymbol,
  span : @identity.SourceSpan?,
) -> CoercionMap raise TheoryError {
  add_coercion_path(self, make_coercion_path(function_, span), span)
}

///|
fn coercion_types_may_match(left : @logic.Ty, right : @logic.Ty) -> Bool {
  match (left.view(), right.view()) {
    (TyApp(left_symbol, left_arguments), TyApp(right_symbol, right_arguments)) => {
      if left_symbol != right_symbol ||
        left_arguments.length() != right_arguments.length() {
        return false
      }
      for index, argument in left_arguments {
        if !coercion_types_may_match(argument, right_arguments[index]) {
          return false
        }
      }
      true
    }
    _ => true
  }
}

///|
fn coercion_argument_lists_may_match(
  left : ArrayView[@logic.Ty],
  right : ArrayView[@logic.Ty],
) -> Bool {
  if left.length() != right.length() {
    return false
  }
  for index, argument in left {
    if !coercion_types_may_match(argument, right[index]) {
      return false
    }
  }
  true
}

///|
pub fn CoercionMap::find(
  self : CoercionMap,
  source : @logic.Ty,
  target : @logic.Ty,
  span : @identity.SourceSpan?,
) -> Array[@logic.LSymbol] raise TheoryError {
  guard source.view() is TyApp(source_symbol, source_arguments) &&
    target.view() is TyApp(target_symbol, target_arguments) &&
    self.path(source_symbol, target_symbol) is Some(path) &&
    coercion_argument_lists_may_match(source_arguments, path.source_arguments) &&
    coercion_argument_lists_may_match(target_arguments, path.target_arguments) else {
    fail_theory(CoercionNotFound, span, "no matching coercion path")
  }
  path.functions.copy()
}

///|
pub fn CoercionMap::find_by_symbols(
  self : CoercionMap,
  source : @logic.TypeSymbol,
  target : @logic.TypeSymbol,
) -> Array[@logic.LSymbol]? {
  match self.path(source, target) {
    Some(path) => Some(path.functions.copy())
    None => None
  }
}

///|
pub fn CoercionMap::has_target_symbol(
  self : CoercionMap,
  target : @logic.TypeSymbol,
) -> Bool {
  for _, targets in self.paths {
    if targets.contains(target) {
      return true
    }
  }
  false
}

///|
pub fn CoercionMap::union(
  self : CoercionMap,
  imported : CoercionMap,
  span : @identity.SourceSpan?,
) -> CoercionMap raise TheoryError {
  let mut result = self
  for _, targets in imported.paths {
    for _, path in targets {
      if path.direct {
        result = add_coercion_path(result, path, span)
      }
    }
  }
  result
}
