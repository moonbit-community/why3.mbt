// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
priv struct SpWrite {
  variable : @mlw.PVariable
  destination : @logic.VSymbol
}

///|
priv struct PureSpOutcome {
  index : Int
  formula : @logic.Term
  writes : Array[SpWrite]
}

///|
priv struct PureSpResult {
  safety : @logic.Term
  outcomes : Array[PureSpOutcome]
  reads : Array[@logic.VSymbol]
}

///|
fn pvariable_contains(
  variables : ArrayView[@mlw.PVariable],
  wanted : @mlw.PVariable,
) -> Bool {
  variables.any(variable => variable == wanted)
}

///|
fn pvariable_add_unique(
  variables : Array[@mlw.PVariable],
  variable : @mlw.PVariable,
) -> Unit {
  if !pvariable_contains(variables, variable) {
    variables.push(variable)
  }
}

///|
fn pvariable_for_symbol(
  variables : ArrayView[@mlw.PVariable],
  symbol : @logic.VSymbol,
) -> @mlw.PVariable? {
  for variable in variables {
    if variable.view().pure_symbol == symbol {
      return Some(variable)
    }
  }
  None
}

///|
fn collect_kode_variables(
  kode : Kode,
  variables : Array[@mlw.PVariable],
) -> Unit {
  match kode.view() {
    Kseq(first, _, second) | Kpar(first, second) => {
      collect_kode_variables(first, variables)
      collect_kode_variables(second, variables)
    }
    Kif(condition, yes, no) => {
      pvariable_add_unique(variables, condition)
      collect_kode_variables(yes, variables)
      collect_kode_variables(no, variables)
    }
    Kcase(scrutinee, branches) => {
      pvariable_add_unique(variables, scrutinee)
      for branch in branches {
        collect_kode_variables(branch.1, variables)
      }
    }
    Khavoc(affected, writes, _) => {
      for variable in affected {
        pvariable_add_unique(variables, variable)
      }
      for write in writes {
        for field in write.fields {
          pvariable_add_unique(variables, field)
        }
      }
    }
    Klet(variable, _, _) => pvariable_add_unique(variables, variable)
    Kval(binders, _) =>
      for binder in binders {
        pvariable_add_unique(variables, binder)
      }
    Koff(_, inner) | Kmode(_, inner) | Kout(_, inner) | Kpush(_, inner) =>
      collect_kode_variables(inner, variables)
    Kcut(_) | Kstop(_) | Kcont(_) => ()
  }
}

///|
fn sp_write_position(
  writes : ArrayView[SpWrite],
  variable : @mlw.PVariable,
) -> Int? {
  for index, write in writes {
    if write.variable == variable {
      return Some(index)
    }
  }
  None
}

///|
fn sp_write_contains(
  writes : ArrayView[SpWrite],
  variable : @mlw.PVariable,
) -> Bool {
  sp_write_position(writes, variable) is Some(_)
}

///|
fn sp_write_union(
  preferred : ArrayView[SpWrite],
  fallback : ArrayView[SpWrite],
) -> Array[SpWrite] {
  let result = preferred.to_owned()
  for write in fallback {
    if !sp_write_contains(result, write.variable) {
      result.push(write)
    }
  }
  result
}

///|
fn sp_write_difference(
  left : ArrayView[SpWrite],
  right : ArrayView[SpWrite],
) -> Array[SpWrite] {
  [
    for write in left if !sp_write_contains(right, write.variable) => write
  ]
}

///|
fn sp_write_intersection(
  left : ArrayView[SpWrite],
  right : ArrayView[SpWrite],
) -> Array[SpWrite] {
  [
    for write in left if sp_write_contains(right, write.variable) => write
  ]
}

///|
fn sp_write_intersection_reads(
  writes : ArrayView[SpWrite],
  reads : ArrayView[@logic.VSymbol],
) -> Array[SpWrite] {
  [
    for write in writes if symbol_contains(
      reads,
      write.variable.view().pure_symbol,
    ) => write
  ]
}

///|
fn sp_write_values(writes : ArrayView[SpWrite]) -> Array[@logic.VSymbol] {
  [
    for write in writes => write.destination
  ]
}

///|
fn sp_write_adjustment(
  writes : ArrayView[SpWrite],
) -> @logic.TermSubstitution raise {
  let mut substitution = @logic.TermSubstitution::new()
  for write in writes {
    substitution = substitution.bind(
      write.variable.view().pure_symbol,
      @logic.Term::variable(write.destination),
      None,
    )
  }
  substitution
}

///|
fn sp_write_advancement(
  before : ArrayView[SpWrite],
  after : ArrayView[SpWrite],
) -> @logic.TermSubstitution raise {
  let mut substitution = @logic.TermSubstitution::new()
  for write in before {
    match sp_write_position(after, write.variable) {
      Some(position) => {
        let destination = after[position].destination
        if write.destination != destination {
          substitution = substitution.bind(
            write.destination,
            @logic.Term::variable(destination),
            None,
          )
        }
      }
      None => ()
    }
  }
  substitution
}

///|
fn apply_sp_substitution(
  environment : VcEnvironment,
  substitution : @logic.TermSubstitution,
  formula : @logic.Term,
) -> @logic.Term raise {
  if substitution.bindings().is_empty() {
    formula
  } else {
    substitution.apply(environment.context, formula, None)
  }
}

///|
fn symbol_contains(
  symbols : ArrayView[@logic.VSymbol],
  wanted : @logic.VSymbol,
) -> Bool {
  symbols.any(symbol => symbol == wanted)
}

///|
fn symbol_union(
  left : ArrayView[@logic.VSymbol],
  right : ArrayView[@logic.VSymbol],
) -> Array[@logic.VSymbol] {
  let result = left.to_owned()
  for symbol in right {
    if !symbol_contains(result, symbol) {
      result.push(symbol)
    }
  }
  result
}

///|
fn symbol_remove(
  symbols : ArrayView[@logic.VSymbol],
  unwanted : @logic.VSymbol,
) -> Array[@logic.VSymbol] {
  [
    for symbol in symbols if symbol != unwanted => symbol
  ]
}

///|
fn symbol_remove_all(
  symbols : ArrayView[@logic.VSymbol],
  unwanted : ArrayView[@logic.VSymbol],
) -> Array[@logic.VSymbol] {
  [
    for symbol in symbols if !symbol_contains(unwanted, symbol) => symbol
  ]
}

///|
fn symbol_difference(
  left : ArrayView[@logic.VSymbol],
  right : ArrayView[@logic.VSymbol],
) -> Array[@logic.VSymbol] {
  [
    for symbol in left if !symbol_contains(right, symbol) => symbol
  ]
}

///|
fn reads_with_term(
  reads : ArrayView[@logic.VSymbol],
  term : @logic.Term,
) -> Array[@logic.VSymbol] {
  symbol_union(reads, term.free_variables())
}

///|
fn integer_contains(values : ArrayView[Int], wanted : Int) -> Bool {
  values.any(value => value == wanted)
}

///|
fn integer_add_unique(values : Array[Int], value : Int) -> Unit {
  if !integer_contains(values, value) {
    values.push(value)
  }
}

///|
fn outcome_position(outcomes : ArrayView[PureSpOutcome], index : Int) -> Int? {
  for position, outcome in outcomes {
    if outcome.index == index {
      return Some(position)
    }
  }
  None
}

///|
fn outcome_entry(
  outcomes : ArrayView[PureSpOutcome],
  index : Int,
) -> PureSpOutcome? {
  match outcome_position(outcomes, index) {
    Some(position) => Some(outcomes[position])
    None => None
  }
}

///|
fn outcome_indices(outcomes : ArrayView[PureSpOutcome]) -> Array[Int] {
  [
    for outcome in outcomes => outcome.index
  ]
}

///|
fn post_reads_for(
  post_reads : ArrayView[(Int, Array[@logic.VSymbol])],
  index : Int,
) -> Array[@logic.VSymbol] {
  for entry in post_reads {
    if entry.0 == index {
      return entry.1.copy()
    }
  }
  []
}

///|
fn bind_post_reads(
  post_reads : ArrayView[(Int, Array[@logic.VSymbol])],
  index : Int,
  reads : ArrayView[@logic.VSymbol],
) -> Array[(Int, Array[@logic.VSymbol])] {
  let result = []
  let mut replaced = false
  for entry in post_reads {
    if entry.0 == index {
      result.push((index, reads.to_owned()))
      replaced = true
    } else {
      result.push((entry.0, entry.1.copy()))
    }
  }
  if !replaced {
    result.push((index, reads.to_owned()))
  }
  result
}

///|
fn pure_sp_and(left : @logic.Term, right : @logic.Term) -> @logic.Term raise {
  if is_true(left) || is_false(right) {
    right
  } else if is_true(right) || is_false(left) {
    left
  } else {
    plain_and(left, right)
  }
}

///|
fn pure_sp_or(left : @logic.Term, right : @logic.Term) -> @logic.Term raise {
  if is_true(left) || is_false(right) {
    left
  } else if is_true(right) || is_false(left) {
    right
  } else {
    @logic.Term::binary(Or, left, right, None).add_attributes([
      case_split_attribute,
    ])
  }
}

///|
fn pure_sp_if(
  condition : @logic.Term,
  yes : @logic.Term,
  no : @logic.Term,
) -> @logic.Term raise {
  if is_true(condition) || (is_true(yes) && is_true(no)) {
    yes
  } else if is_false(condition) || (is_false(yes) && is_false(no)) {
    no
  } else if is_false(no) {
    pure_sp_and(condition, yes)
  } else if is_false(yes) {
    pure_sp_and(not_simplified(condition), no)
  } else {
    @logic.Term::if_then_else(condition, yes, no, None).add_attributes([
      case_split_attribute,
    ])
  }
}

///|
fn pure_sp_case(
  scrutinee : @logic.Term,
  branches : ArrayView[(@logic.Pattern, @logic.Term)],
) -> @logic.Term raise {
  if branches.all(entry => is_false(entry.1)) {
    @logic.Term::false_formula()
  } else {
    @logic.Term::case(scrutinee, branches, None).add_attributes([
      case_split_attribute,
    ])
  }
}

///|
fn exists_simplified(
  binders : ArrayView[@logic.VSymbol],
  body : @logic.Term,
) -> @logic.Term raise {
  let free = body.free_variables()
  @logic.Term::quantify(
    ExistsQuantifier,
    [
      for binder in binders if symbol_contains(free, binder) => binder
    ],
    [],
    body,
    None,
  )
}

///|
priv struct PreparedHavoc {
  binders : Array[@logic.VSymbol]
  relation : @logic.Term
  substitution : @logic.TermSubstitution
}

///|
fn prepare_havoc(
  environment : VcEnvironment,
  affected : ArrayView[@mlw.PVariable],
  writes : ArrayView[VcHavocWrite],
  formula : @logic.Term,
  span : @identity.SourceSpan?,
) -> PreparedHavoc raise {
  let free = formula.free_variables()
  let binders : Array[@logic.VSymbol] = []
  let relations : Array[@logic.Term] = []
  let mut substitution = @logic.TermSubstitution::new()
  let ordered_affected = affected.to_owned()
  ordered_affected.sort_by((left, right) => {
    right.semantic_id().local_id().compare(left.semantic_id().local_id())
  })
  for variable in ordered_affected {
    let old = variable.view().pure_symbol
    if !free.any(candidate => candidate == old) {
      continue
    }
    let old_view = old.view()
    let fresh = @logic.VSymbol::new(
      environment.context,
      old_view.name,
      @identity.Origin::user(old_view.name, span, old_view.origin.attributes()),
      old_view.ty,
      span,
    )
    binders.push(fresh)
    substitution = substitution.bind(old, @logic.Term::variable(fresh), span)
    let relation = havoc_value_relation(
      environment,
      writes,
      @logic.Term::variable(old),
      @logic.Term::variable(fresh),
      variable.view().ity,
      span,
    )
    if !is_true(relation) {
      relations.push(relation)
    }
  }
  { binders, relation: conjunction(relations), substitution }
}

///|
fn wp_havoc(
  environment : VcEnvironment,
  affected : ArrayView[@mlw.PVariable],
  writes : ArrayView[VcHavocWrite],
  formula : @logic.Term,
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let prepared = prepare_havoc(environment, affected, writes, formula, span)
  let rewritten = prepared.substitution.apply(
    environment.context,
    formula,
    None,
  )
  forall_simplified(prepared.binders, sp_implies(prepared.relation, rewritten))
}

///|
fn fresh_written_symbol(
  environment : VcEnvironment,
  variable : @mlw.PVariable,
) -> @logic.VSymbol raise {
  let symbol = variable.view().pure_symbol
  symbol.clone_with_type(environment.context, symbol.ty(), None)
}

///|
fn sp_havoc_relation(
  environment : VcEnvironment,
  destinations : ArrayView[SpWrite],
  writes : ArrayView[VcHavocWrite],
  span : @identity.SourceSpan?,
) -> @logic.Term raise {
  let relations = []
  for destination in destinations {
    let variable = destination.variable
    let relation = havoc_value_relation(
      environment,
      writes,
      pvariable_term(variable),
      @logic.Term::variable(destination.destination),
      variable.view().ity,
      span,
    )
    if !is_true(relation) {
      relations.push(relation)
    }
  }
  conjunction(relations)
}

///|
fn pure_sp_let(
  environment : VcEnvironment,
  variable : @mlw.PVariable,
  value : @logic.Term,
  formula : @logic.Term,
  post_reads : ArrayView[@logic.VSymbol],
) -> @logic.Term raise {
  let symbol = variable.view().pure_symbol
  guard environment.unit_value.ty() is Some(unit_type) else {
    abort("validated unit value is untyped")
  }
  if variable.view().ity.to_ty(None) == unit_type {
    substitute_variable(
      environment.context,
      symbol,
      environment.unit_value,
      formula,
    )
  } else if symbol_contains(post_reads, symbol) {
    pure_sp_and(
      @logic.Term::elaborated_apply(
        environment.equality,
        [@logic.Term::variable(symbol), value],
        None,
        None,
      ),
      formula,
    )
  } else {
    let_simplified_symbol(
      environment.context,
      symbol,
      value,
      formula,
      relevant_for_counterexample(symbol),
    )
  }
}

///|
fn sp_complete(
  environment : VcEnvironment,
  formula : @logic.Term,
  present : ArrayView[SpWrite],
  required : ArrayView[SpWrite],
) -> @logic.Term raise {
  let mut result = formula
  for write in required {
    if !sp_write_contains(present, write.variable) {
      result = pure_sp_and(
        result,
        @logic.Term::elaborated_apply(
          environment.equality,
          [
            @logic.Term::variable(write.destination),
            pvariable_term(write.variable),
          ],
          None,
          None,
        ),
      )
    }
  }
  result
}

///|
fn sp_combine(
  environment : VcEnvironment,
  left : PureSpOutcome,
  right : PureSpOutcome,
) -> PureSpOutcome raise {
  {
    index: left.index,
    formula: pure_sp_or(
      sp_complete(environment, left.formula, left.writes, right.writes),
      sp_complete(environment, right.formula, right.writes, left.writes),
    ),
    writes: sp_write_union(left.writes, right.writes),
  }
}

///|
fn add_outcome(
  environment : VcEnvironment,
  outcomes : Array[PureSpOutcome],
  outcome : PureSpOutcome,
) -> Unit raise {
  match outcome_position(outcomes, outcome.index) {
    Some(position) =>
      outcomes[position] = sp_combine(environment, outcomes[position], outcome)
    None => outcomes.push(outcome)
  }
}

///|
fn kode_outcome_indices(kode : Kode) -> Array[Int] {
  match kode.view() {
    Kseq(first, index, second) => {
      let result = kode_outcome_indices(first)
      if integer_contains(result, index) {
        let retained = [ for outcome in result if outcome != index => outcome ]
        for outcome in kode_outcome_indices(second) {
          integer_add_unique(retained, outcome)
        }
        retained
      } else {
        result
      }
    }
    Kpar(left, right) => {
      let result = kode_outcome_indices(left)
      for outcome in kode_outcome_indices(right) {
        integer_add_unique(result, outcome)
      }
      result
    }
    Kif(_, yes, no) => {
      let result = kode_outcome_indices(yes)
      for outcome in kode_outcome_indices(no) {
        integer_add_unique(result, outcome)
      }
      result
    }
    Kcase(_, branches) => {
      let result = []
      for branch in branches {
        for outcome in kode_outcome_indices(branch.1) {
          integer_add_unique(result, outcome)
        }
      }
      result
    }
    Khavoc(_, _, _) | Klet(_, _, _) | Kval(_, _) | Kcut(_) => [0]
    Kstop(_) => []
    Kcont(index) => [index]
    Koff(_, inner) => kode_outcome_indices(inner)
    Kmode(_, inner) => kode_outcome_indices(inner)
    Kout(outcomes, inner) => {
      let result : Array[Int] = []
      for outcome in kode_outcome_indices(inner) {
        if outcomes.contains(outcome) {
          result.push(outcome)
        }
      }
      result
    }
    Kpush(_, _) => []
  }
}

///|
fn sp_quantifier_binders(
  reads : ArrayView[@logic.VSymbol],
  writes : ArrayView[SpWrite],
) -> Array[@logic.VSymbol] {
  let ordered_reads = reads.to_owned()
  ordered_reads.sort_by((left, right) => {
    left.semantic_id().local_id().compare(right.semantic_id().local_id())
  })
  let ordered_writes = writes.to_owned()
  ordered_writes.sort_by((left, right) => {
    left.variable
    .semantic_id()
    .local_id()
    .compare(right.variable.semantic_id().local_id())
  })
  symbol_union(ordered_reads, sp_write_values(ordered_writes))
}

///|
fn advance_sp_outcome(
  environment : VcEnvironment,
  outcome : PureSpOutcome,
  destinations : ArrayView[SpWrite],
) -> PureSpOutcome raise {
  let visible = sp_write_intersection(destinations, outcome.writes)
  {
    index: outcome.index,
    formula: apply_sp_substitution(
      environment,
      sp_write_advancement(outcome.writes, visible),
      outcome.formula,
    ),
    writes: visible,
  }
}

///|
fn sequence_head_destinations(
  environment : VcEnvironment,
  tail : PureSpResult,
  destinations : ArrayView[SpWrite],
  variables : ArrayView[@mlw.PVariable],
) -> Array[SpWrite] raise {
  let tail_writes : Array[SpWrite] = []
  for outcome in tail.outcomes {
    let combined = sp_write_union(outcome.writes, tail_writes)
    tail_writes.clear()
    tail_writes.push_iter(combined.iter())
  }
  let written_destinations = tail_writes.map(write => {
    variable: write.variable,
    destination: fresh_written_symbol(environment, write.variable),
  })
  let read_destinations : Array[SpWrite] = []
  for symbol in tail.reads {
    match pvariable_for_symbol(variables, symbol) {
      Some(variable) =>
        if !variable.view().ity.is_pure() &&
          !sp_write_contains(destinations, variable) &&
          !sp_write_contains(written_destinations, variable) &&
          !sp_write_contains(read_destinations, variable) {
          read_destinations.push({
            variable,
            destination: fresh_written_symbol(environment, variable),
          })
        }
      _ => ()
    }
  }
  sp_write_union(
    written_destinations,
    sp_write_union(read_destinations, destinations),
  )
}

///|
fn pure_sp_sequence_with_destinations(
  environment : VcEnvironment,
  first : Kode,
  index : Int,
  second : Kode,
  post_reads : ArrayView[(Int, Array[@logic.VSymbol])],
  destinations : ArrayView[SpWrite],
  variables : ArrayView[@mlw.PVariable],
) -> PureSpResult raise {
  match (index, first.view()) {
    (0, Klet(variable, value, constraint)) => {
      let tail = pure_sp_with_destinations(
        environment, second, post_reads, destinations, variables,
      )
      let safety = wp_let(
        environment,
        variable,
        value,
        sp_implies(constraint, tail.safety),
      )
      let outcomes = []
      for outcome in tail.outcomes {
        outcomes.push({
          index: outcome.index,
          formula: pure_sp_let(
            environment,
            variable,
            value,
            pure_sp_and(constraint, outcome.formula),
            post_reads_for(post_reads, outcome.index),
          ),
          writes: outcome.writes,
        })
      }
      let reads = symbol_remove(
        reads_with_term(reads_with_term(tail.reads, value), constraint),
        variable.view().pure_symbol,
      )
      { safety, outcomes, reads }
    }
    _ => {
      let tail = pure_sp_with_destinations(
        environment, second, post_reads, destinations, variables,
      )
      let head_destinations = sequence_head_destinations(
        environment, tail, destinations, variables,
      )
      let head = pure_sp_with_destinations(
        environment,
        first,
        bind_post_reads(post_reads, index, tail.reads),
        head_destinations,
        variables,
      )
      match outcome_entry(head.outcomes, index) {
        None =>
          {
            safety: head.safety,
            outcomes: [
              for outcome in head.outcomes if outcome.index != index => {
                advance_sp_outcome(environment, outcome, destinations)
              }
            ],
            reads: head.reads,
          }
        Some(head_outcome) => {
          let bound = symbol_difference(tail.reads, head.reads)
          let adjusted_tail_safety = apply_sp_substitution(
            environment,
            sp_write_adjustment(head_outcome.writes),
            tail.safety,
          )
          let tail_safety = forall_simplified(
            sp_quantifier_binders(bound, head_outcome.writes),
            sp_implies(head_outcome.formula, adjusted_tail_safety),
          )
          let safety = wp_and(head.safety, tail_safety)
          let outcomes = [
            for outcome in head.outcomes if outcome.index != index => {
              advance_sp_outcome(environment, outcome, destinations)
            }
          ]
          for tail_outcome in tail.outcomes {
            let reads = post_reads_for(post_reads, tail_outcome.index)
            let visible_head_writes = sp_write_intersection(
              destinations,
              sp_write_difference(
                sp_write_intersection_reads(head_outcome.writes, reads),
                tail_outcome.writes,
              ),
            )
            let writes = sp_write_union(
              visible_head_writes,
              tail_outcome.writes,
            )
            let hidden_head_writes = sp_write_difference(
              head_outcome.writes,
              visible_head_writes,
            )
            let quantified = sp_quantifier_binders(
              symbol_difference(bound, reads),
              hidden_head_writes,
            )
            let head_formula = apply_sp_substitution(
              environment,
              sp_write_advancement(head_outcome.writes, visible_head_writes),
              head_outcome.formula,
            )
            let tail_formula = apply_sp_substitution(
              environment,
              sp_write_adjustment(
                sp_write_union(visible_head_writes, head_outcome.writes),
              ),
              tail_outcome.formula,
            )
            add_outcome(environment, outcomes, {
              index: tail_outcome.index,
              formula: exists_simplified(
                quantified,
                pure_sp_and(head_formula, tail_formula),
              ),
              writes,
            })
          }
          { safety, outcomes, reads: head.reads }
        }
      }
    }
  }
}

///|
fn pure_sp_with_destinations(
  environment : VcEnvironment,
  kode : Kode,
  post_reads : ArrayView[(Int, Array[@logic.VSymbol])],
  destinations : ArrayView[SpWrite],
  variables : ArrayView[@mlw.PVariable],
) -> PureSpResult raise {
  match kode.view() {
    Kseq(first, index, second) =>
      pure_sp_sequence_with_destinations(
        environment, first, index, second, post_reads, destinations, variables,
      )
    Kpar(left, right) => {
      let left = pure_sp_with_destinations(
        environment, left, post_reads, destinations, variables,
      )
      let right = pure_sp_with_destinations(
        environment, right, post_reads, destinations, variables,
      )
      let outcomes = left.outcomes.copy()
      for outcome in right.outcomes {
        add_outcome(environment, outcomes, outcome)
      }
      {
        safety: wp_and(left.safety, right.safety),
        outcomes,
        reads: symbol_union(left.reads, right.reads),
      }
    }
    Kif(condition, yes, no) => {
      let yes = pure_sp_with_destinations(
        environment, yes, post_reads, destinations, variables,
      )
      let no = pure_sp_with_destinations(
        environment, no, post_reads, destinations, variables,
      )
      let condition_formula = environment.boolean_test(condition)
      let indices = outcome_indices(yes.outcomes)
      for index in outcome_indices(no.outcomes) {
        integer_add_unique(indices, index)
      }
      let outcomes = []
      for index in indices {
        let outcome = match
          (
            outcome_entry(yes.outcomes, index),
            outcome_entry(no.outcomes, index),
          ) {
          (Some(yes_outcome), Some(no_outcome)) => {
            let writes = sp_write_union(yes_outcome.writes, no_outcome.writes)
            {
              index,
              formula: pure_sp_if(
                condition_formula,
                sp_complete(
                  environment,
                  yes_outcome.formula,
                  yes_outcome.writes,
                  no_outcome.writes,
                ),
                sp_complete(
                  environment,
                  no_outcome.formula,
                  no_outcome.writes,
                  yes_outcome.writes,
                ),
              ),
              writes,
            }
          }
          (Some(yes_outcome), None) =>
            {
              index,
              formula: pure_sp_and(condition_formula, yes_outcome.formula),
              writes: yes_outcome.writes,
            }
          (None, Some(no_outcome)) =>
            {
              index,
              formula: pure_sp_and(
                not_simplified(condition_formula),
                no_outcome.formula,
              ),
              writes: no_outcome.writes,
            }
          (None, None) =>
            { index, formula: @logic.Term::false_formula(), writes: [] }
        }
        outcomes.push(outcome)
      }
      {
        safety: wp_if(condition_formula, yes.safety, no.safety),
        outcomes,
        reads: symbol_union(
          [condition.view().pure_symbol],
          symbol_union(yes.reads, no.reads),
        ),
      }
    }
    Kcase(scrutinee, branches) => {
      let branch_results = branches.map(entry => {
        (
          entry.0,
          pure_sp_with_destinations(
            environment,
            entry.1,
            post_reads,
            destinations,
            variables,
          ),
        )
      })
      let safety_branches = branch_results.map(entry => {
        (entry.0, entry.1.safety)
      })
      let safety = if safety_branches.all(entry => can_simplify_true(entry.1)) {
        @logic.Term::true_formula()
      } else {
        @logic.Term::case(pvariable_term(scrutinee), safety_branches, None)
      }
      let indices = []
      for entry in branch_results {
        for index in outcome_indices(entry.1.outcomes) {
          integer_add_unique(indices, index)
        }
      }
      let outcomes = []
      for index in indices {
        let required_writes : Array[SpWrite] = []
        for entry in branch_results {
          match outcome_entry(entry.1.outcomes, index) {
            Some(outcome) => {
              let combined = sp_write_union(outcome.writes, required_writes)
              required_writes.clear()
              required_writes.push_iter(combined.iter())
            }
            None => ()
          }
        }
        let mut present = false
        let outcome_branches = branch_results.map(entry => {
          let formula = match outcome_entry(entry.1.outcomes, index) {
            Some(outcome) => {
              present = true
              sp_complete(
                environment,
                outcome.formula,
                outcome.writes,
                required_writes,
              )
            }
            None => @logic.Term::false_formula()
          }
          (entry.0, formula)
        })
        if present {
          outcomes.push({
            index,
            formula: pure_sp_case(pvariable_term(scrutinee), outcome_branches),
            writes: required_writes,
          })
        }
      }
      let mut reads = [scrutinee.view().pure_symbol]
      for entry in branch_results {
        reads = symbol_union(
          reads,
          symbol_remove_all(entry.1.reads, entry.0.bound_variables()),
        )
      }
      { safety, outcomes, reads }
    }
    Khavoc(affected, writes, span) => {
      let reads = post_reads_for(post_reads, 0)
      let selected : Array[SpWrite] = []
      for destination in destinations {
        if pvariable_contains(affected, destination.variable) &&
          symbol_contains(reads, destination.variable.view().pure_symbol) {
          selected.push(destination)
        }
      }
      if selected.is_empty() {
        {
          safety: @logic.Term::true_formula(),
          outcomes: [
            { index: 0, formula: @logic.Term::true_formula(), writes: [] },
          ],
          reads,
        }
      } else {
        let relation = sp_havoc_relation(environment, selected, writes, span)
        let destination_symbols = sp_write_values(selected)
        let mut result_reads = reads
        for symbol in relation.free_variables() {
          if !symbol_contains(destination_symbols, symbol) {
            result_reads = symbol_union(result_reads, [symbol])
          }
        }
        {
          safety: @logic.Term::true_formula(),
          outcomes: [{ index: 0, formula: relation, writes: selected }],
          reads: result_reads,
        }
      }
    }
    Klet(variable, value, constraint) => {
      let reads_after = post_reads_for(post_reads, 0)
      let outcome = pure_sp_let(
        environment, variable, value, constraint, reads_after,
      )
      {
        safety: @logic.Term::true_formula(),
        outcomes: [{ index: 0, formula: outcome, writes: [] }],
        reads: symbol_remove(
          reads_with_term(reads_after, outcome),
          variable.view().pure_symbol,
        ),
      }
    }
    Kval(variables, constraint) => {
      let binders = [ for variable in variables => variable.view().pure_symbol ]
      let reads_after = post_reads_for(post_reads, 0)
      let lost = [
        for binder in binders if !symbol_contains(reads_after, binder) => binder
      ]
      let outcome = exists_simplified(lost, constraint)
      {
        safety: @logic.Term::true_formula(),
        outcomes: [{ index: 0, formula: outcome, writes: [] }],
        reads: symbol_remove_all(reads_with_term(reads_after, outcome), binders),
      }
    }
    Kcut(formula) => {
      let reads_after = post_reads_for(post_reads, 0)
      {
        safety: formula,
        outcomes: [{ index: 0, formula, writes: [] }],
        reads: reads_with_term(reads_after, formula),
      }
    }
    Kstop(formula) =>
      { safety: formula, outcomes: [], reads: formula.free_variables() }
    Kcont(index) =>
      {
        safety: @logic.Term::true_formula(),
        outcomes: [{ index, formula: @logic.Term::true_formula(), writes: [] }],
        reads: post_reads_for(post_reads, index),
      }
    Koff(explanation, inner) => {
      let result = pure_sp_with_destinations(
        environment, inner, post_reads, destinations, variables,
      )
      { ..result, safety: solder_explanation(result.safety, explanation) }
    }
    Kmode(ClassicalWp, inner) => {
      if !kode_outcome_indices(inner).is_empty() {
        fail_vc(
          UnsupportedComputation,
          None,
          "Cannot switch to the classical WP procedure",
        )
      }
      let safety = wp_kode(environment, inner, [])
      { safety, outcomes: [], reads: safety.free_variables() }
    }
    Kmode(EfficientSp, inner) =>
      pure_sp_with_destinations(
        environment, inner, post_reads, destinations, variables,
      )
    Kout(outcomes, inner) =>
      pure_sp_with_destinations(
        environment,
        inner,
        [
          for entry in post_reads if outcomes.contains(entry.0) => entry
        ],
        destinations,
        variables,
      )
    Kpush(_, _) =>
      fail_vc(InvariantFailure, None, "unconsumed Kode continuation marker")
  }
}

///|
fn pure_sp(
  environment : VcEnvironment,
  kode : Kode,
  post_reads : ArrayView[(Int, Array[@logic.VSymbol])],
) -> PureSpResult raise {
  let variables = []
  collect_kode_variables(kode, variables)
  pure_sp_with_destinations(environment, kode, post_reads, [], variables)
}
