// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "upstream standard-library Wasm1 slice 3/3 loads through the typed cache" {
  @stdlib_slices.check_upstream_stdlib_slice(29, 53)
}
