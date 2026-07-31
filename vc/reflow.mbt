// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).

///|
priv struct ReflowContinuation {
  index : Int
  kode : Kode
  closed : Bool
}

///|
fn reflow_outcome_position(
  outcomes : ArrayView[(Int, Bool)],
  index : Int,
) -> Int? {
  for position, outcome in outcomes {
    if outcome.0 == index {
      return Some(position)
    }
  }
  None
}

///|
fn reflow_outcome_contains(
  outcomes : ArrayView[(Int, Bool)],
  index : Int,
) -> Bool {
  reflow_outcome_position(outcomes, index) is Some(_)
}

///|
fn reflow_outcome_remove(
  outcomes : ArrayView[(Int, Bool)],
  index : Int,
) -> Array[(Int, Bool)] {
  [
    for outcome in outcomes if outcome.0 != index => outcome
  ]
}

///|
fn reflow_outcome_union(
  left : ArrayView[(Int, Bool)],
  right : ArrayView[(Int, Bool)],
) -> Array[(Int, Bool)] {
  let result = left.to_owned()
  for outcome in right {
    match reflow_outcome_position(result, outcome.0) {
      Some(position) => result[position] = (outcome.0, false)
      None => result.push(outcome)
    }
  }
  result
}

///|
fn reflow_direct_sequence_head(kode : Kode) -> Bool {
  match kode.view() {
    Khavoc(_, _, _) | Klet(_, _, _) | Kval(_, _) | Kcut(_) => true
    _ => false
  }
}

///|
fn reflow_mark(
  kode : Kode,
  mode : VcMode,
) -> (Kode, Array[(Int, Bool)]) raise VcError {
  match kode.view() {
    Kseq(first, 0, second) if reflow_direct_sequence_head(first) => {
      let (second, outcomes) = reflow_mark(second, mode)
      (kseq(first, 0, second), outcomes)
    }
    Kseq(first, index, second) => {
      let (first, first_outcomes) = reflow_mark(first, mode)
      guard reflow_outcome_position(first_outcomes, index) is Some(position) else {
        return (first, first_outcomes)
      }
      let push = first_outcomes[position].1
      let (second, second_outcomes) = reflow_mark(second, mode)
      let second = if push {
        kpush(!reflow_outcome_contains(second_outcomes, 0), second)
      } else {
        second
      }
      (
        kseq(first, index, second),
        reflow_outcome_union(
          reflow_outcome_remove(first_outcomes, index),
          second_outcomes,
        ),
      )
    }
    Kpar(left, right) => {
      let (left, left_outcomes) = reflow_mark(left, mode)
      let (right, right_outcomes) = reflow_mark(right, mode)
      (kpar(left, right), reflow_outcome_union(left_outcomes, right_outcomes))
    }
    Kif(condition, yes, no) => {
      let (yes, yes_outcomes) = reflow_mark(yes, mode)
      let (no, no_outcomes) = reflow_mark(no, mode)
      (kif(condition, yes, no), reflow_outcome_union(yes_outcomes, no_outcomes))
    }
    Kcase(scrutinee, branches) => {
      let rewritten : Array[(@logic.Pattern, Kode)] = []
      let outcomes : Array[(Int, Bool)] = []
      for branch in branches {
        let (body, body_outcomes) = reflow_mark(branch.1, mode)
        rewritten.push((branch.0, body))
        let combined = reflow_outcome_union(outcomes, body_outcomes)
        outcomes.clear()
        outcomes.append(combined)
      }
      (kcase(scrutinee, rewritten), outcomes)
    }
    Khavoc(_, _, _) | Klet(_, _, _) | Kval(_, _) | Kcut(_) =>
      (kode, [(0, true)])
    Kstop(_) => (kode, [])
    Kcont(index) => (kode, [(index, true)])
    Koff(explanation, inner) => {
      let (inner, outcomes) = reflow_mark(inner, mode)
      (koff(explanation, inner), outcomes)
    }
    Kmode(inner_mode, inner) if inner_mode == mode => reflow_mark(inner, mode)
    Kmode(inner_mode, inner) => {
      let (inner, outcomes) = reflow_mark(inner, inner_mode)
      if inner_mode is ClassicalWp && !outcomes.is_empty() {
        fail_vc(
          UnsupportedComputation,
          None,
          "Cannot switch to the classical WP procedure",
        )
      }
      (
        kout(outcomes.map(outcome => outcome.0), kmode(inner_mode, inner)),
        outcomes.map(outcome => (outcome.0, false)),
      )
    }
    Kout(_, _) | Kpush(_, _) =>
      fail_vc(InvariantFailure, None, "Kode was reflowed twice")
  }
}

///|
fn reflow_continuation_position(
  continuations : ArrayView[ReflowContinuation],
  index : Int,
) -> Int? {
  for position, continuation in continuations {
    if continuation.index == index {
      return Some(position)
    }
  }
  None
}

///|
fn reflow_continuation_remove(
  continuations : ArrayView[ReflowContinuation],
  index : Int,
) -> Array[ReflowContinuation] {
  let result : Array[ReflowContinuation] = []
  for continuation in continuations {
    if continuation.index != index {
      result.push(continuation)
    }
  }
  result
}

///|
fn reflow_continuation_set(
  continuations : ArrayView[ReflowContinuation],
  replacement : ReflowContinuation,
) -> Array[ReflowContinuation] {
  let result = continuations.to_owned()
  match reflow_continuation_position(result, replacement.index) {
    Some(position) => result[position] = replacement
    None => result.push(replacement)
  }
  result
}

///|
fn reflow_push(
  kode : Kode,
  continuations : ArrayView[ReflowContinuation],
) -> Kode raise VcError {
  match kode.view() {
    Kseq(first, index, second) if second.view() is Kpush(closed, pushed) => {
      let closed = closed ||
        (match reflow_continuation_position(continuations, 0) {
          Some(position) => continuations[position].closed
          None => false
        })
      let replacement = {
        index,
        kode: reflow_push(pushed, continuations),
        closed,
      }
      let nested = reflow_continuation_set(continuations, replacement)
      if index == 0 || closed {
        reflow_push(first, nested)
      } else {
        kseq(reflow_push(first, nested), index, kcont(0))
      }
    }
    Kseq(first, index, second) =>
      kseq(
        reflow_push(first, reflow_continuation_remove(continuations, index)),
        index,
        reflow_push(second, continuations),
      )
    Kpar(left, right) =>
      kpar(reflow_push(left, continuations), reflow_push(right, continuations))
    Kif(condition, yes, no) =>
      kif(
        condition,
        reflow_push(yes, continuations),
        reflow_push(no, continuations),
      )
    Kcase(scrutinee, branches) =>
      kcase(
        scrutinee,
        branches.map(branch => (branch.0, reflow_push(branch.1, continuations))),
      )
    Khavoc(_, _, _) | Klet(_, _, _) | Kval(_, _) | Kcut(_) =>
      match reflow_continuation_position(continuations, 0) {
        Some(position) => kseq(kode, 0, continuations[position].kode)
        None => kode
      }
    Kstop(_) => kode
    Kcont(index) =>
      match reflow_continuation_position(continuations, index) {
        Some(position) => {
          let continuation = continuations[position]
          if index == 0 || continuation.closed {
            continuation.kode
          } else {
            kseq(continuation.kode, 0, kode)
          }
        }
        None => kode
      }
    Koff(explanation, inner) =>
      koff(explanation, reflow_push(inner, continuations))
    Kmode(mode, inner) => kmode(mode, reflow_push(inner, []))
    Kout(outcomes, inner) => kout(outcomes, reflow_push(inner, []))
    Kpush(_, _) =>
      fail_vc(InvariantFailure, None, "unconsumed Kode continuation marker")
  }
}

///|
fn reflow_kode(mode : VcMode, kode : Kode) -> Kode raise VcError {
  let kode = if mode is EfficientSp { kmode(EfficientSp, kode) } else { kode }
  let (marked, _) = reflow_mark(kode, ClassicalWp)
  reflow_push(marked, [])
}
