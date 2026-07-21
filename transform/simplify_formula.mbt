// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn simplify_formula_term(
  context : @identity.CompilationContext,
  formula : @logic.Term,
) -> @logic.Term raise TransformError {
  let stage = @identity.SimplifyFormula
  let formula = without_asym_split(formula)
  let recurse = fn(child : @logic.Term) -> @logic.Term raise TransformError {
    if child.is_formula() {
      simplify_formula_term(context, child)
    } else {
      simplify_value_term(context, child)
    }
  }
  map_simplified(context, formula, recurse, false, stage)
}

///|
fn simplify_value_term(
  context : @identity.CompilationContext,
  term : @logic.Term,
) -> @logic.Term raise TransformError {
  let recurse = fn(child : @logic.Term) -> @logic.Term raise TransformError {
    if child.is_formula() {
      simplify_formula_term(context, child)
    } else {
      simplify_value_term(context, child)
    }
  }
  map_plain(term, recurse, @identity.SimplifyFormula)
}

///|
fn simplify_formula_definition(
  context : @identity.CompilationContext,
  definition : @logic.LogicDefinition,
) -> @logic.LogicDefinition raise TransformError {
  let stage = @identity.SimplifyFormula
  let view = definition.view()
  let body = if view.body.is_formula() {
    simplify_formula_term(context, view.body)
  } else {
    simplify_value_term(context, view.body)
  }
  match view.symbol.view().origin.kind().view() {
    SnapshotKind =>
      @logic.LogicDefinition::trusted_recursive(
        context,
        view.symbol,
        view.parameters,
        body,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "invalid trusted simplified definition",
          )
      }
    UserKind | GeneratedKind(_) =>
      @logic.LogicDefinition::new(
        context,
        view.symbol,
        view.parameters,
        body,
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "invalid simplified definition",
          )
      }
  }
}

///|
fn simplify_formula_declaration(
  context : @identity.CompilationContext,
  declaration : @logic.Decl,
) -> @logic.Decl raise TransformError {
  let stage = @identity.SimplifyFormula
  match declaration.view() {
    Dtype(_) | Ddata(_) | Dparam(_) => declaration
    Dind(_) =>
      fail_transform(
        UnsupportedStructure,
        stage,
        "inductive declaration survived its slot",
      )
    Dlogic(definitions) => {
      let mapped = [
        for definition in definitions => {
          simplify_formula_definition(context, definition)
        }
      ]
      match declaration.origin().kind().view() {
        SnapshotKind =>
          @logic.Decl::trusted_logic(
            context,
            declaration.origin(),
            mapped,
            None,
          ) catch {
            _ =>
              fail_transform(
                InvariantFailure,
                stage,
                "invalid trusted simplified group",
              )
          }
        UserKind | GeneratedKind(_) =>
          @logic.Decl::logic(context, declaration.origin(), mapped, None) catch {
            _ =>
              fail_transform(
                InvariantFailure,
                stage,
                "invalid simplified group",
              )
          }
      }
    }
    Dprop(kind, proposition, formula) =>
      @logic.Decl::proposition(
        context,
        declaration.origin(),
        kind,
        proposition,
        simplify_formula_term(context, formula),
        None,
      ) catch {
        _ =>
          fail_transform(
            InvariantFailure,
            stage,
            "invalid simplified proposition",
          )
      }
  }
}

///|
pub fn simplify_formula(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.SimplifyFormula
  require_task_context(context, task, stage)
  let items : Array[@theory.TheoryItem] = []
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) =>
        items.push(
          TheoryDecl(simplify_formula_declaration(context, declaration)),
        )
      TheoryUse(_) | TheoryClone(_) | TheoryMeta(_) => items.push(item)
    }
  }
  checked_task(task.context_anchor(), items, stage)
}
