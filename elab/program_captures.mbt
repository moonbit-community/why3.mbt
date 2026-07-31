// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-27.

///|
fn append_program_capture_name(names : Array[Bytes], name : Bytes) -> Unit {
  if !names.any(existing => existing == name) {
    names.push(name)
  }
}

///|
fn program_pattern_bound_names(
  pattern : @parser.Pattern,
  names : Array[Bytes],
) -> Unit {
  match pattern.desc {
    Pwild => ()
    Pvar(ident) => append_program_capture_name(names, ident.name)
    Papp(_, arguments) | Ptuple(arguments) =>
      for argument in arguments {
        program_pattern_bound_names(argument, names)
      }
    Prec(fields) =>
      for field in fields {
        program_pattern_bound_names(field.1, names)
      }
    Pas(inner, ident, _) => {
      program_pattern_bound_names(inner, names)
      append_program_capture_name(names, ident.name)
    }
    Por(left, right) => {
      program_pattern_bound_names(left, names)
      program_pattern_bound_names(right, names)
    }
    Pcast(inner, _) | Pscope(_, inner) | Pparen(inner) | Pghost(inner) =>
      program_pattern_bound_names(inner, names)
  }
}

///|
fn program_binder_bound_names(
  binders : ArrayView[@parser.Binder],
  names : Array[Bytes],
) -> Unit {
  for binder in binders {
    if binder.ident is Some(ident) {
      append_program_capture_name(names, ident.name)
    }
  }
}

///|
fn program_param_bound_names(
  parameters : ArrayView[@parser.Param],
  names : Array[Bytes],
) -> Unit {
  for parameter in parameters {
    if parameter.ident is Some(ident) {
      append_program_capture_name(names, ident.name)
    }
  }
}

///|
fn record_program_target_qualid(
  targets : ArrayView[Bytes],
  bound : ArrayView[Bytes],
  captured : Array[Bytes],
  path : @parser.QualId,
) -> Unit {
  guard path is Qident(ident) else { return }
  if !bound.any(name => name == ident.name) &&
    targets.any(name => name == ident.name) {
    append_program_capture_name(captured, ident.name)
  }
}

///|
fn collect_program_target_term(
  targets : ArrayView[Bytes],
  bound : ArrayView[Bytes],
  captured : Array[Bytes],
  term : @parser.Term,
) -> Unit {
  let recurse = fn(child) {
    collect_program_target_term(targets, bound, captured, child)
  }
  match term.desc {
    Ttrue | Tfalse | Tconst(_) => ()
    Tident(path) | Tasref(path) =>
      record_program_target_qualid(targets, bound, captured, path)
    Tidapp(path, arguments) => {
      record_program_target_qualid(targets, bound, captured, path)
      for argument in arguments {
        recurse(argument)
      }
    }
    Tapply(function_, argument)
    | Tinfix(function_, _, argument)
    | Tinnfix(function_, _, argument)
    | Tbinop(function_, _, argument)
    | Tbinnop(function_, _, argument) => {
      recurse(function_)
      recurse(argument)
    }
    Tnot(inner)
    | Tattr(_, inner)
    | Tscope(_, inner)
    | Tcast(inner, _)
    | Tat(inner, _) => recurse(inner)
    Tif(condition, consequent, alternative) => {
      recurse(condition)
      recurse(consequent)
      recurse(alternative)
    }
    Tquant(_, binders, triggers, body) => {
      let nested_bound = bound.to_owned()
      program_binder_bound_names(binders, nested_bound)
      for group in triggers {
        for trigger in group {
          collect_program_target_term(targets, nested_bound, captured, trigger)
        }
      }
      collect_program_target_term(targets, nested_bound, captured, body)
    }
    Teps(ident, _, body) => {
      let nested_bound = bound.to_owned()
      append_program_capture_name(nested_bound, ident.name)
      collect_program_target_term(targets, nested_bound, captured, body)
    }
    Tlet(ident, value, body) => {
      recurse(value)
      let nested_bound = bound.to_owned()
      append_program_capture_name(nested_bound, ident.name)
      collect_program_target_term(targets, nested_bound, captured, body)
    }
    Tcase(scrutinee, branches) => {
      recurse(scrutinee)
      for branch in branches {
        let nested_bound = bound.to_owned()
        program_pattern_bound_names(branch.0, nested_bound)
        collect_program_target_term(targets, nested_bound, captured, branch.1)
      }
    }
    Ttuple(arguments) =>
      for argument in arguments {
        recurse(argument)
      }
    Trecord(fields) =>
      for field in fields {
        recurse(field.1)
      }
    Tupdate(source, fields) => {
      recurse(source)
      for field in fields {
        recurse(field.1)
      }
    }
  }
}

///|
fn collect_program_target_invariant(
  targets : ArrayView[Bytes],
  bound : ArrayView[Bytes],
  captured : Array[Bytes],
  invariant : @parser.Invariant,
) -> Unit {
  for term in invariant.terms {
    collect_program_target_term(targets, bound, captured, term)
  }
}

///|
fn collect_program_target_variant(
  targets : ArrayView[Bytes],
  bound : ArrayView[Bytes],
  captured : Array[Bytes],
  variant : @parser.Variant,
) -> Unit {
  for item in variant.items {
    collect_program_target_term(targets, bound, captured, item.0)
  }
}

///|
fn collect_program_target_spec(
  targets : ArrayView[Bytes],
  bound : ArrayView[Bytes],
  captured : Array[Bytes],
  spec : @parser.Spec,
) -> Unit {
  for precondition in spec.preconditions {
    collect_program_target_term(targets, bound, captured, precondition)
  }
  for postcondition in spec.postconditions {
    for branch in postcondition.branches {
      let branch_bound = bound.to_owned()
      program_pattern_bound_names(branch.0, branch_bound)
      collect_program_target_term(targets, branch_bound, captured, branch.1)
    }
  }
  for postcondition in spec.exceptional_postconditions {
    for branch in postcondition.branches {
      if branch.1 is Some((pattern, formula)) {
        let branch_bound = bound.to_owned()
        program_pattern_bound_names(pattern, branch_bound)
        collect_program_target_term(targets, branch_bound, captured, formula)
      }
    }
  }
  for read in spec.reads {
    record_program_target_qualid(targets, bound, captured, read)
  }
  for write in spec.writes {
    collect_program_target_term(targets, bound, captured, write)
  }
  for alias_entry in spec.aliases {
    collect_program_target_term(targets, bound, captured, alias_entry.0)
    collect_program_target_term(targets, bound, captured, alias_entry.1)
  }
  collect_program_target_variant(targets, bound, captured, spec.variant)
}

///|
fn collect_program_target_expression(
  targets : ArrayView[Bytes],
  bound : ArrayView[Bytes],
  captured : Array[Bytes],
  expression : @parser.Expr,
) -> Unit {
  let recurse = fn(child) {
    collect_program_target_expression(targets, bound, captured, child)
  }
  match expression.desc {
    Eref | Etrue | Efalse | Econst(_) | Eabsurd => ()
    Eident(path) | Easref(path) | Eidpur(path) =>
      record_program_target_qualid(targets, bound, captured, path)
    Eidapp(path, arguments) => {
      record_program_target_qualid(targets, bound, captured, path)
      for argument in arguments {
        recurse(argument)
      }
    }
    Eapply(function_, argument)
    | Einfix(function_, _, argument)
    | Einnfix(function_, _, argument)
    | Esequence(function_, argument)
    | Eand(function_, argument)
    | Eor(function_, argument) => {
      recurse(function_)
      recurse(argument)
    }
    Elet(ident, _, _, value, body) => {
      recurse(value)
      let nested_bound = bound.to_owned()
      append_program_capture_name(nested_bound, ident.name)
      collect_program_target_expression(targets, nested_bound, captured, body)
    }
    Erec(definitions, body) => {
      let recursive_bound = bound.to_owned()
      for definition in definitions {
        append_program_capture_name(recursive_bound, definition.name.name)
      }
      for definition in definitions {
        let function_bound = recursive_bound.copy()
        program_binder_bound_names(definition.binders, function_bound)
        collect_program_target_spec(
          targets,
          function_bound,
          captured,
          definition.spec,
        )
        collect_program_target_expression(
          targets,
          function_bound,
          captured,
          definition.body,
        )
      }
      collect_program_target_expression(
        targets, recursive_bound, captured, body,
      )
    }
    Efun(binders, _, _, _, spec, body) => {
      let function_bound = bound.to_owned()
      program_binder_bound_names(binders, function_bound)
      collect_program_target_spec(targets, function_bound, captured, spec)
      collect_program_target_expression(targets, function_bound, captured, body)
    }
    Eany(parameters, _, _, _, _, spec) => {
      let function_bound = bound.to_owned()
      program_param_bound_names(parameters, function_bound)
      collect_program_target_spec(targets, function_bound, captured, spec)
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
    Ewhile(condition, invariant, variant, body) => {
      recurse(condition)
      collect_program_target_invariant(targets, bound, captured, invariant)
      collect_program_target_variant(targets, bound, captured, variant)
      recurse(body)
    }
    Enot(inner)
    | Escope(_, inner)
    | Elabel(_, inner)
    | Ecast(inner, _)
    | Eghost(inner)
    | Eattr(_, inner) => recurse(inner)
    Ematch(scrutinee, regular, exceptional) => {
      recurse(scrutinee)
      for branch in regular {
        let branch_bound = bound.to_owned()
        program_pattern_bound_names(branch.pattern, branch_bound)
        collect_program_target_expression(
          targets,
          branch_bound,
          captured,
          branch.body,
        )
      }
      for branch in exceptional {
        let branch_bound = bound.to_owned()
        if branch.pattern is Some(pattern) {
          program_pattern_bound_names(pattern, branch_bound)
        }
        collect_program_target_expression(
          targets,
          branch_bound,
          captured,
          branch.body,
        )
      }
    }
    Epure(term) | Eassert(_, term) =>
      collect_program_target_term(targets, bound, captured, term)
    Eraise(_, payload) => if payload is Some(payload) { recurse(payload) }
    Eexn(ident, _, _, body) | Eoptexn(ident, _, body) => {
      let nested_bound = bound.to_owned()
      append_program_capture_name(nested_bound, ident.name)
      collect_program_target_expression(targets, nested_bound, captured, body)
    }
    Efor(ident, first, _, last, invariant, body) => {
      recurse(first)
      recurse(last)
      let nested_bound = bound.to_owned()
      append_program_capture_name(nested_bound, ident.name)
      collect_program_target_invariant(
        targets, nested_bound, captured, invariant,
      )
      collect_program_target_expression(targets, nested_bound, captured, body)
    }
  }
}

///|
fn program_expression_mentions_name(
  expression : @parser.Expr,
  name : BytesView,
) -> Bool {
  let captured : Array[Bytes] = []
  collect_program_target_expression([name.to_owned()], [], captured, expression)
  !captured.is_empty()
}

///|
fn program_recursive_preliminary_reads(
  outer_scope : ArrayView[(Bytes, ProgramLocal)],
  sources : ArrayView[@parser.FunctionDef],
) -> Array[Array[@mlw.PVariable]] {
  let outer_names : Array[Bytes] = []
  for entry in outer_scope {
    append_program_capture_name(outer_names, entry.0)
  }
  let recursive_names : Array[Bytes] = []
  for source in sources {
    append_program_capture_name(recursive_names, source.name.name)
  }
  let captures : Array[Array[@mlw.PVariable]] = []
  let dependencies : Array[Array[Int]] = []
  for source in sources {
    let parameter_names = recursive_names.copy()
    program_binder_bound_names(source.binders, parameter_names)
    let capture_names : Array[Bytes] = []
    collect_program_target_spec(
      outer_names,
      parameter_names,
      capture_names,
      source.spec,
    )
    collect_program_target_expression(
      outer_names,
      parameter_names,
      capture_names,
      source.body,
    )
    let direct : Array[@mlw.PVariable] = []
    for name in capture_names {
      if find_program_local(outer_scope, name) is Some(binding) &&
        !direct.any(existing => existing == binding.variable) {
        direct.push(binding.variable)
      }
    }
    captures.push(direct)
    let locally_bound : Array[Bytes] = []
    program_binder_bound_names(source.binders, locally_bound)
    let dependency_names : Array[Bytes] = []
    collect_program_target_expression(
      recursive_names,
      locally_bound,
      dependency_names,
      source.body,
    )
    let source_dependencies : Array[Int] = []
    for name in dependency_names {
      for index, recursive_name in recursive_names {
        if name == recursive_name &&
          !source_dependencies.any(existing => existing == index) {
          source_dependencies.push(index)
        }
      }
    }
    dependencies.push(source_dependencies)
  }
  let mut changed = true
  while changed {
    changed = false
    for index = 0; index < captures.length(); index = index + 1 {
      for dependency in dependencies[index] {
        for captured in captures[dependency] {
          if !captures[index].any(existing => existing == captured) {
            captures[index].push(captured)
            changed = true
          }
        }
      }
    }
  }
  captures
}
