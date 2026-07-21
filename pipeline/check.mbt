// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
pub fn check(
  source : BytesView,
  filename? : BytesView = b"",
) -> CheckedFile raise {
  let parsed = @parser.parse_mlw_file(source, filename~)
  let context = @identity.CompilationContext::new()
  let frozen = @stdlib.minimal_env(context)
  let elaborated = @elab.elaborate_file(
    context,
    frozen.semantic_environment(),
    parsed,
  )
  let units : Array[TypedUnitView] = []
  for unit in elaborated.units() {
    match unit {
      ElaboratedTheory(theory) => units.push(Theory(theory))
      ElaboratedModule(pmodule) => units.push(Module(pmodule))
    }
  }
  CheckedFile::new(context, frozen, units)
}
