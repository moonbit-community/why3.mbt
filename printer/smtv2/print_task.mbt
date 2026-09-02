// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-21.

///|
fn task_has_meta(task : @theory.Task, name : BytesView) -> Bool {
  task.view().items.any(item => {
    item is TheoryMeta(meta) && meta.view().name[:] == name
  })
}

///|
pub fn print_task(
  query : SmtV26Query,
  task : @theory.Task,
) -> SmtQuery raise PrinterError {
  let syntax = syntax_maps(task)
  scan_prepared_task(query, syntax, task)
  let request_model = task_has_meta(task, b"get_counterexmp")
  let state = PrinterState::new(
    syntax,
    request_model,
    task_has_meta(task, b"counterexample_need_smtlib_push"),
  )
  for prelude in query.preludes {
    state.writer.write(prelude)
    state.writer.write(b"\n")
  }
  if request_model {
    state.writer.write(b"(set-option :produce-models true)\n")
  }
  for item in task.view().items {
    match item {
      TheoryDecl(declaration) => print_declaration(state, declaration)
      TheoryUse(_) | TheoryClone(_) | TheoryMeta(_) => ()
    }
  }
  state.writer.finish()
}
