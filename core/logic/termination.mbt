// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
priv enum StructuralDescent {
  StrictDescent(Int)
  SameArgument(Int)
  UnknownDescent
}

///|
priv struct LogicCall {
  caller : LSymbol
  arguments : Array[StructuralDescent]
}

///|
priv struct LogicCallGraph {
  calls : Map[LSymbol, Array[LogicCall]]
}

///|
fn initial_variable_graph(
  parameters : ArrayView[VSymbol],
) -> Array[Map[VSymbol, StructuralDescent]] {
  let variables : Map[VSymbol, StructuralDescent] = Map([])
  for index, parameter in parameters {
    variables[parameter] = SameArgument(index)
  }
  [variables]
}

///|
fn remove_graph_variable(
  graphs : Array[Map[VSymbol, StructuralDescent]],
  variable : VSymbol,
) -> Array[Map[VSymbol, StructuralDescent]] {
  let result : Array[Map[VSymbol, StructuralDescent]] = []
  for graph in graphs {
    let copied = graph.copy()
    copied.remove(variable)
    result.push(copied)
  }
  result
}

///|
fn bind_graph_variable(
  graphs : Array[Map[VSymbol, StructuralDescent]],
  variable : VSymbol,
  descent : StructuralDescent,
) -> Array[Map[VSymbol, StructuralDescent]] {
  let result : Array[Map[VSymbol, StructuralDescent]] = []
  for graph in graphs {
    let copied = graph.copy()
    copied[variable] = descent
    result.push(copied)
  }
  result
}

///|
fn graph_after_let(
  graphs : Array[Map[VSymbol, StructuralDescent]],
  value : Term,
  binder : VSymbol,
) -> Array[Map[VSymbol, StructuralDescent]] {
  match value.node {
    VariableTerm(variable) => {
      let result : Array[Map[VSymbol, StructuralDescent]] = []
      for graph in graphs {
        let copied = graph.copy()
        match graph.get(variable) {
          Some(descent) => copied[binder] = descent
          None => copied.remove(binder)
        }
        result.push(copied)
      }
      result
    }
    _ => remove_graph_variable(graphs, binder)
  }
}

///|
fn descend_under_constructor(descent : StructuralDescent) -> StructuralDescent {
  match descent {
    UnknownDescent => UnknownDescent
    SameArgument(index) | StrictDescent(index) => StrictDescent(index)
  }
}

///|
fn bind_pattern_variables(
  descent : StructuralDescent,
  graphs : Array[Map[VSymbol, StructuralDescent]],
  pattern : Pattern,
) -> Array[Map[VSymbol, StructuralDescent]] {
  match pattern.node {
    WildPattern => graphs
    VariablePattern(variable) => bind_graph_variable(graphs, variable, descent)
    AsPattern(inner, variable) =>
      bind_graph_variable(
        bind_pattern_variables(descent, graphs, inner),
        variable,
        descent,
      )
    OrPattern(left, right) => {
      let result = bind_pattern_variables(descent, graphs, left)
      for graph in bind_pattern_variables(descent, graphs, right) {
        result.push(graph)
      }
      result
    }
    ApplicationPattern(_, _) => {
      let nested = descend_under_constructor(descent)
      let result : Array[Map[VSymbol, StructuralDescent]] = []
      for graph in graphs {
        let copied = graph.copy()
        for variable in pattern.bound_variables {
          copied[variable] = nested
        }
        result.push(copied)
      }
      result
    }
  }
}

///|
fn remove_pattern_variables(
  graphs : Array[Map[VSymbol, StructuralDescent]],
  pattern : Pattern,
) -> Array[Map[VSymbol, StructuralDescent]] {
  let result : Array[Map[VSymbol, StructuralDescent]] = []
  for graph in graphs {
    let copied = graph.copy()
    for variable in pattern.bound_variables {
      copied.remove(variable)
    }
    result.push(copied)
  }
  result
}

///|
fn match_term_pattern(
  variables : Map[VSymbol, StructuralDescent],
  term : Term,
  graphs : Array[Map[VSymbol, StructuralDescent]],
  pattern : Pattern,
) -> Array[Map[VSymbol, StructuralDescent]] {
  if pattern.node is WildPattern {
    return graphs
  }
  match term.node {
    VariableTerm(variable) =>
      match variables.get(variable) {
        Some(descent) => bind_pattern_variables(descent, graphs, pattern)
        None => remove_pattern_variables(graphs, pattern)
      }
    ApplicationTerm(term_symbol, _, term_arguments) =>
      match pattern.node {
        VariablePattern(variable) => remove_graph_variable(graphs, variable)
        AsPattern(inner, variable) =>
          match_term_pattern(
            variables,
            term,
            remove_graph_variable(graphs, variable),
            inner,
          )
        OrPattern(left, right) => {
          let result = match_term_pattern(variables, term, graphs, left)
          for graph in match_term_pattern(variables, term, graphs, right) {
            result.push(graph)
          }
          result
        }
        ApplicationPattern(pattern_symbol, pattern_arguments) if term_symbol ==
          pattern_symbol => {
          let mut result = graphs
          for index, argument in term_arguments {
            result = match_term_pattern(
              variables,
              argument,
              result,
              pattern_arguments[index],
            )
          }
          result
        }
        WildPattern => graphs
        _ => remove_pattern_variables(graphs, pattern)
      }
    _ => remove_pattern_variables(graphs, pattern)
  }
}

///|
fn graph_after_pattern(
  graphs : Array[Map[VSymbol, StructuralDescent]],
  term : Term,
  pattern : Pattern,
) -> Array[Map[VSymbol, StructuralDescent]] {
  let result : Array[Map[VSymbol, StructuralDescent]] = []
  for variables in graphs {
    for graph in match_term_pattern(variables, term, [variables], pattern) {
      result.push(graph)
    }
  }
  result
}

///|
fn register_logic_call(
  graph : LogicCallGraph,
  caller : LSymbol,
  variables : Array[Map[VSymbol, StructuralDescent]],
  callee : LSymbol,
  arguments : ArrayView[Term],
) -> Unit {
  for variable_graph in variables {
    let description : Array[StructuralDescent] = []
    for argument in arguments {
      match argument.node {
        VariableTerm(variable) =>
          match variable_graph.get(variable) {
            Some(descent) => description.push(descent)
            None => description.push(UnknownDescent)
          }
        _ => description.push(UnknownDescent)
      }
    }
    let call = { caller, arguments: description }
    match graph.calls.get(callee) {
      Some(calls) => calls.push(call)
      None => graph.calls[callee] = [call]
    }
  }
}

///|
fn collect_logic_calls(
  graph : LogicCallGraph,
  defined : Map[LSymbol, Unit],
  caller : LSymbol,
  variables : Array[Map[VSymbol, StructuralDescent]],
  term : Term,
) -> Unit {
  let visit = fn(child : Term) {
    collect_logic_calls(graph, defined, caller, variables, child)
  }
  match term.node {
    VariableTerm(_) | ConstantTerm(_) | TrueTerm | FalseTerm => ()
    ApplicationTerm(symbol, _, arguments) => {
      for argument in arguments {
        visit(argument)
      }
      if defined.contains(symbol) {
        register_logic_call(graph, caller, variables, symbol, arguments)
      }
    }
    IfTerm(condition, then_branch, else_branch) => {
      visit(condition)
      visit(then_branch)
      visit(else_branch)
    }
    LetTerm(binder, value, body) => {
      visit(value)
      collect_logic_calls(
        graph,
        defined,
        caller,
        graph_after_let(variables, value, binder),
        body,
      )
    }
    CaseTerm(scrutinee, branches) => {
      visit(scrutinee)
      for branch in branches {
        collect_logic_calls(
          graph,
          defined,
          caller,
          graph_after_pattern(variables, scrutinee, branch.pattern),
          branch.body,
        )
      }
    }
    EpsilonTerm(_, body) => visit(body)
    QuantifiedTerm(_, _, _, body) => visit(body)
    BinaryTerm(_, left, right) => {
      visit(left)
      visit(right)
    }
    NotTerm(inner) => visit(inner)
  }
}

///|
fn build_logic_call_graph(
  definitions : ArrayView[LogicDefinition],
) -> LogicCallGraph {
  let defined : Map[LSymbol, Unit] = Map([])
  for definition in definitions {
    defined[definition.symbol] = ()
  }
  let graph : LogicCallGraph = { calls: Map([]) }
  for definition in definitions {
    collect_logic_calls(
      graph,
      defined,
      definition.symbol,
      initial_variable_graph(definition.parameters),
      definition.body,
    )
  }
  graph
}

///|
fn local_call(
  arguments : ArrayView[StructuralDescent],
) -> Array[StructuralDescent] {
  let result : Array[StructuralDescent] = []
  for index, descent in arguments {
    result.push(
      match descent {
        StrictDescent(source) if index == source => descent
        SameArgument(source) if index == source => descent
        _ => UnknownDescent
      },
    )
  }
  result
}

///|
fn descent_vector_subsumes(
  candidate : ArrayView[StructuralDescent],
  existing : ArrayView[StructuralDescent],
) -> Bool {
  for index, candidate_descent in candidate {
    let compatible = match (candidate_descent, existing[index]) {
      (_, UnknownDescent) => true
      (SameArgument(left), SameArgument(right)) => left == right
      (StrictDescent(left), SameArgument(right)) => left == right
      (StrictDescent(left), StrictDescent(right)) => left == right
      _ => false
    }
    if !compatible {
      return false
    }
  }
  true
}

///|
fn call_is_subsumed(
  resolved : Map[LSymbol, Array[Array[StructuralDescent]]],
  caller : LSymbol,
  arguments : ArrayView[StructuralDescent],
) -> Bool {
  match resolved.get(caller) {
    None => false
    Some(vectors) =>
      vectors.any(vector => descent_vector_subsumes(arguments, vector))
  }
}

///|
fn remember_resolved_call(
  resolved : Map[LSymbol, Array[Array[StructuralDescent]]],
  caller : LSymbol,
  arguments : Array[StructuralDescent],
) -> Unit {
  match resolved.get(caller) {
    Some(vectors) => vectors.push(arguments)
    None => resolved[caller] = [arguments]
  }
}

///|
fn strict_after_composition(descent : StructuralDescent) -> StructuralDescent {
  match descent {
    UnknownDescent => UnknownDescent
    SameArgument(index) | StrictDescent(index) => StrictDescent(index)
  }
}

///|
fn compose_call_vectors(
  outer : ArrayView[StructuralDescent],
  inner : ArrayView[StructuralDescent],
) -> Array[StructuralDescent] {
  let result : Array[StructuralDescent] = []
  for descent in outer {
    result.push(
      match descent {
        UnknownDescent => UnknownDescent
        SameArgument(index) => inner[index]
        StrictDescent(index) => strict_after_composition(inner[index])
      },
    )
  }
  result
}

///|
fn recursive_call_vectors(
  graph : LogicCallGraph,
  symbol : LSymbol,
) -> Array[Array[StructuralDescent]] {
  let worklist : Array[LogicCall] = match graph.calls.get(symbol) {
    Some(calls) => calls.copy()
    None => []
  }
  let resolved : Map[LSymbol, Array[Array[StructuralDescent]]] = Map([])
  let recursive : Array[Array[StructuralDescent]] = []
  let mut cursor = 0
  while cursor < worklist.length() {
    let call = worklist[cursor]
    cursor = cursor + 1
    if call.caller == symbol {
      recursive.push(local_call(call.arguments))
    } else if !call_is_subsumed(resolved, call.caller, call.arguments) {
      remember_resolved_call(resolved, call.caller, call.arguments)
      match graph.calls.get(call.caller) {
        Some(incoming) =>
          for next in incoming {
            worklist.push({
              caller: next.caller,
              arguments: compose_call_vectors(call.arguments, next.arguments),
            })
          }
        None => ()
      }
    }
  }
  recursive
}

///|
fn combine_descent(
  left : StructuralDescent,
  right : StructuralDescent,
) -> StructuralDescent {
  match (left, right) {
    (UnknownDescent, _) => left
    (_, UnknownDescent) => right
    (StrictDescent(_), _) => left
    (_, StrictDescent(_)) => right
    _ => left
  }
}

///|
fn find_decreasing_parameters(
  graph : LogicCallGraph,
  symbol : LSymbol,
) -> Array[Int]? {
  let mut remaining = recursive_call_vectors(graph, symbol)
  let decreasing : Array[Int] = []
  while !remaining.is_empty() {
    let minimum = remaining[0].copy()
    for call_index = 1
        call_index < remaining.length()
        call_index = call_index + 1 {
      let call = remaining[call_index]
      for index = 0; index < minimum.length(); index = index + 1 {
        minimum[index] = combine_descent(minimum[index], call[index])
      }
    }
    let selected : Array[Int] = []
    let mut index = minimum.length() - 1
    while index >= 0 {
      if minimum[index] is StrictDescent(source) && source == index {
        selected.push(index)
      }
      index = index - 1
    }
    if selected.is_empty() {
      return None
    }
    for parameter in selected {
      decreasing.push(parameter)
    }
    let retained : Array[Array[StructuralDescent]] = []
    for call in remaining {
      let mut decreases = false
      for parameter in selected {
        if call[parameter] is StrictDescent(source) && source == parameter {
          decreases = true
        }
      }
      if !decreases {
        retained.push(call)
      }
    }
    remaining = retained
  }
  Some(decreasing)
}

///|
fn check_logic_termination(
  definitions : ArrayView[LogicDefinition],
  span : @identity.SourceSpan?,
) -> Array[LogicDefinition] raise TypeError {
  let graph = build_logic_call_graph(definitions)
  let result : Array[LogicDefinition] = []
  for definition in definitions {
    let decreasing = match
      find_decreasing_parameters(graph, definition.symbol) {
      Some(parameters) => parameters
      None =>
        fail_type(
          NoTerminationProof,
          span,
          "no structural termination proof for logic definition",
        )
    }
    result.push({ ..definition, decreasing_parameters: decreasing })
  }
  result
}
