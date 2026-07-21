// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "static Z3 profile decodes the complete frozen inventory" {
  let spec = z3_static_spec()
  let view = spec.view()
  assert_eq(view.printer, SmtV26)
  assert_eq(view.transforms.length(), 15)
  assert_eq(view.driver_meta_group_count, 48)
  assert_eq(view.driver_meta_count, 992)
  assert_eq(view.snapshot_meta_group_count, 14)
  assert_eq(view.snapshot_meta_count, 491)
  assert_eq(view.syntax_count, 284)
  assert_eq(view.remove_count, 680)
  assert_eq(view.preludes.length(), 3)
  assert_eq(view.theory_prelude_count, 5)
  assert_eq(view.result_regexp_count, 11)
  assert_eq(view.result_exit_code_count, 0)
  assert_eq(view.monomorphic_checkpoints.length(), 16)
  assert_eq(view.polymorphic_checkpoints.length(), 22)
  assert_eq(
    view.polymorphic_checkpoints[13],
    b"discriminate_if_poly:monomorphise_goal",
  )
  assert_eq(view.polymorphic_checkpoints[20], b"encoding_smt_if_poly:guards")
  assert_eq(view.command.view().executable, b"z3")
  assert_eq(view.command.view().common_arguments.length(), 5)
  assert_eq(spec.required_keys().length(), 1465)
}
