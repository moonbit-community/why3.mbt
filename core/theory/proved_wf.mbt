// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
fn lambda_relation(lambda : @logic.Term) -> @logic.LSymbol? {
  guard lambda.view() is Teps(function_variable, quantified) &&
    quantified.view()
    is Tquant(ForallQuantifier, [left_variable, right_variable], _, body) &&
    body.view() is Tbinop(Iff, function_side, relation_side) &&
    relation_side.view() is Tapp(relation, _, [left_argument, right_argument]) &&
    left_argument.view() is Tvar(found_left) &&
    right_argument.view() is Tvar(found_right) &&
    found_left == left_variable &&
    found_right == right_variable else {
    return None
  }
  guard function_side.view() is Tapp(_, _, [function_application, _]) &&
    function_application.view()
    is Tapp(_, _, [partial_application, right_function_argument]) &&
    partial_application.view()
    is Tapp(_, _, [function_head, left_function_argument]) &&
    function_head.view() is Tvar(found_function) &&
    left_function_argument.view() is Tvar(found_left) &&
    right_function_argument.view() is Tvar(found_right) &&
    found_function == function_variable &&
    found_left == left_variable &&
    found_right == right_variable else {
    return None
  }
  Some(relation)
}

///|
fn proved_wf_entry(
  known : @logic.KnownMap,
  relation : @logic.LSymbol,
  proof : @logic.PrSymbol,
  span : @identity.SourceSpan?,
) -> (@logic.PrSymbol, @logic.LSymbol) raise TheoryError {
  let (_, formula) = known.find_proposition(proof, span) catch {
    TypeError(_) =>
      fail_theory(
        IllFormedProvedWf,
        span,
        "vc:proved_wf references an invalid proposition",
      )
  }
  guard formula.view() is Tapp(well_founded, _, [lambda]) &&
    lambda_relation(lambda) is Some(found_relation) &&
    found_relation == relation else {
    fail_theory(
      IllFormedProvedWf,
      span,
      "vc:proved_wf proposition does not prove the supplied relation",
    )
  }
  (proof, well_founded)
}

///|
fn add_proved_wf_meta(
  current : Map[@logic.LSymbol, (@logic.PrSymbol, @logic.LSymbol)],
  known : @logic.KnownMap,
  meta : Meta,
  span : @identity.SourceSpan?,
) -> Map[@logic.LSymbol, (@logic.PrSymbol, @logic.LSymbol)] raise TheoryError {
  let view = meta.view()
  guard (view.name, view.arguments)
    is (
      b"vc:proved_wf",
      [MetaLogicSymbol(relation), MetaPropositionSymbol(proof)],
    ) else {
    return current
  }
  let entry = proved_wf_entry(known, relation, proof, span)
  match current.get(relation) {
    Some(existing) =>
      if existing != entry {
        fail_theory(
          ProvedWfConflict,
          span,
          "relation has conflicting well-foundedness proofs",
        )
      }
    None => ()
  }
  let result = current.copy()
  result[relation] = entry
  result
}

///|
fn merge_proved_wf(
  current : Map[@logic.LSymbol, (@logic.PrSymbol, @logic.LSymbol)],
  imported : Map[@logic.LSymbol, (@logic.PrSymbol, @logic.LSymbol)],
  span : @identity.SourceSpan?,
) -> Map[@logic.LSymbol, (@logic.PrSymbol, @logic.LSymbol)] raise TheoryError {
  let result = current.copy()
  for relation, entry in imported {
    match result.get(relation) {
      Some(existing) =>
        if existing != entry {
          fail_theory(
            ProvedWfConflict,
            span,
            "relation has conflicting well-foundedness proofs",
          )
        }
      None => result[relation] = entry
    }
  }
  result
}
