// Learn more about moon.mod configuration:
// https://docs.moonbitlang.com/en/latest/toolchain/moon/module.html
//
// To add a dependency, run this command in your terminal:
//   moon add moonbitlang/async
//
// Or manually declare it in `import`, for example:
// import {
//   "moonbitlang/async@0.20.2",
// }

name = "moonbit-community/why3"

version = "0.1.0"

readme = "README.mbt.md"

repository = ""

license = "Apache-2.0"

keywords = [ ]

preferred_target = "wasm-gc"

description = ""

import {
  "moonbitlang/async@0.20.2",
  "moonbit-community/prettyprinter@0.4.10",
}
