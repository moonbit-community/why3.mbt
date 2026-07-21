// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
/// `eliminate_projections_sums` only rewrites projections belonging to an
/// algebraic datatype with more than one constructor.  The frozen MVP closure
/// contains Bool/Unit datatypes but no such projection.  Keep this slot as an
/// asserted identity transform so an expanded snapshot cannot silently skip
/// the upstream rewrite implemented by `eliminate_algebraic.ml`.
pub fn eliminate_projections_sums(
  context : @identity.CompilationContext,
  task : @theory.Task,
) -> @theory.Task raise TransformError {
  let stage = @identity.EliminateProjectionsSums
  require_task_context(context, task, stage)
  for item in task.view().items {
    guard item is TheoryDecl(declaration) &&
      declaration.view() is Ddata(data_declarations) else {
      continue
    }
    for data_declaration in data_declarations {
      let constructors = data_declaration.view().constructors
      if constructors.length() <= 1 {
        continue
      }
      for data_constructor in constructors {
        if data_constructor.view().projections.any(projection => {
            projection is Some(_)
          }) {
          fail_transform(
            UnsupportedStructure,
            stage,
            "sum projection requires the full eliminate_projections_sums rewrite",
          )
        }
      }
    }
  }
  task
}
