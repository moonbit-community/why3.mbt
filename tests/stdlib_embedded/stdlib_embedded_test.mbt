// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
#cfg(target="wasm")
test "embedded standard-library Wasm1 slice 1/3 loads through the typed cache" {
  @stdlib_slices.check_embedded_stdlib_slice(0, 18)
}

///|
#cfg(not(target="wasm"))
test "all 53 embedded standard-library sources load through the typed cache" {
  @stdlib_slices.check_embedded_stdlib_slice(0, 53)
}
