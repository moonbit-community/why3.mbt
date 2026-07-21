// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn literal_term_is_passthrough(term : @logic.Term) -> Bool {
  let children_supported = fn(values : ArrayView[@logic.Term]) -> Bool {
    values.all(literal_term_is_passthrough)
  }
  match term.view() {
    Tconst(constant) => {
      guard term.ty() is Some(ty) &&
        ty.view() is TyApp(symbol, arguments) &&
        arguments.is_empty() else {
        return false
      }
      match constant.view() {
        IntegerConstant(_, _) => symbol.builtin_kind() == Some(BuiltinInteger)
        RealConstant(_, _) => symbol.builtin_kind() == Some(BuiltinReal)
        StringConstant(_) => false
      }
    }
    Tvar(_) | Ttrue | Tfalse => true
    Tapp(_, _, arguments) => children_supported(arguments)
    Tif(condition, then_branch, else_branch) =>
      literal_term_is_passthrough(condition) &&
      literal_term_is_passthrough(then_branch) &&
      literal_term_is_passthrough(else_branch)
    Tlet(_, value, body) =>
      literal_term_is_passthrough(value) && literal_term_is_passthrough(body)
    Tcase(scrutinee, branches) =>
      literal_term_is_passthrough(scrutinee) &&
      branches.all(branch => literal_term_is_passthrough(branch.view().body))
    Teps(_, _) => false
    Tquant(_, _, triggers, body) =>
      triggers.all(group => children_supported(group)) &&
      literal_term_is_passthrough(body)
    Tbinop(_, left, right) =>
      literal_term_is_passthrough(left) && literal_term_is_passthrough(right)
    Tnot(inner) => literal_term_is_passthrough(inner)
  }
}

///|
fn literal_declaration_is_passthrough(declaration : @logic.Decl) -> Bool {
  match declaration.view() {
    Dtype(symbols) =>
      symbols.all(symbol => {
        symbol.view().definition is NoDef ||
        symbol.view().definition is Alias(_)
      })
    Ddata(_) | Dparam(_) => true
    Dlogic(definitions) =>
      definitions.all(definition => {
        literal_term_is_passthrough(definition.view().body)
      })
    Dind(_) => false
    Dprop(_, _, formula) => literal_term_is_passthrough(formula)
  }
}

///|
pub fn eliminate_literal(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.EliminateLiteral
  require_task_context(context, task, stage)
  for item in task.view().items {
    match item {
      TheoryMeta(meta) => {
        let name = meta.view().name
        if name == b"literal:keep" || name == b"range" || name == b"float" {
          fail_transform(
            UnsupportedStructure,
            stage,
            "literal profile input requires the full abstraction branch",
          )
        }
      }
      TheoryDecl(declaration) =>
        if !literal_declaration_is_passthrough(declaration) {
          fail_transform(
            UnsupportedStructure,
            stage,
            "non-builtin or residual literal structure reached eliminate_literal",
          )
        }
      TheoryUse(_) | TheoryClone(_) => ()
    }
  }
  task
}
