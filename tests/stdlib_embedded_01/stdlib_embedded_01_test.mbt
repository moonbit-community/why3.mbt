// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
test "embedded standard-library Wasm1 slice 2/3 loads through the typed cache" {
  @stdlib_slices.check_embedded_stdlib_slice(18, 29)
}
