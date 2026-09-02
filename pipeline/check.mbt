// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub fn check_with_environment(
  source : BytesView,
  environment : @environment.Environment,
  filename? : BytesView = b"",
) -> CheckedFile raise {
  let parsed = @parser.parse_mlw_file(source, filename~)
  let context = environment.compilation_context()
  let elaborated = @elab.elaborate_file(context, environment, parsed)
  let units : Array[TypedUnitView] = []
  for unit in elaborated.units() {
    match unit {
      ElaboratedTheory(theory) => units.push(Theory(theory))
      ElaboratedModule(pmodule) => units.push(Module(pmodule))
    }
  }
  CheckedFile::new(context, environment, units)
}

///|
/// Checks one WhyML source using the complete embedded Why3 1.7.2 standard
/// library and a fresh compilation context.
pub fn check(
  source : BytesView,
  filename? : BytesView = b"",
) -> CheckedFile raise {
  check_with_environment(
    source,
    @environment.Environment::with_source(@stdlib.embedded_source_provider()),
    filename~,
  )
}
