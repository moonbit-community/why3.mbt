// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception
// Derived from Why3 1.7.2 (Copyright 2010-2023 Inria, CNRS, Paris-Saclay University).
// MoonBit translation and semantic modifications recorded on 2026-07-24.

///|
/// Parser/elaborator adapter for `Environment::read_library`. Keeping it in
/// this package preserves the dependency direction:
/// core/env <- environment <- parser/elab.
pub fn load_mlw_library(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  candidate : @env.SourceCandidate,
) -> @environment.TypedLibrary raise {
  let view = candidate.view()
  let parsed = @parser.parse_mlw_file(view.contents, filename=view.location)
  let elaborated = elaborate_file_at_path(
    context,
    environment,
    parsed,
    view.path.view().segments,
  )
  elaborated.typed_library
}
