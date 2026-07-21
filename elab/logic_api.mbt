// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

///|
struct PureFile {
  theories : Array[@theory.Theory]
}

///|
pub(all) struct PureFileView {
  theories : ArrayView[@theory.Theory]
}

///|
pub fn PureFile::view(self : PureFile) -> PureFileView {
  { theories: self.theories[:] }
}

///|
/// Elaborates and registers source theories in file order. The direct-file
/// Why3 path is empty, matching `Env.read_file` in Why3 1.7.2.
fn elaborate_pure_file_raw(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  file : @parser.MlwFile,
) -> PureFile raise {
  guard file is Modules(units) else {
    fail_unsupported(
      ProgramRoutineShape,
      FeatureClassification,
      None,
      "anonymous declaration files are outside the MVP",
    )
  }
  let theories : Array[@theory.Theory] = []
  for unit in units {
    let theory = elaborate_theory_unit(context, environment, unit)
    environment.register_theory(theory, true, Some(source_span(unit.name.span)))
    theories.push(theory)
  }
  { theories, }
}

///|
/// Elaborates and registers source theories in file order while exposing one
/// stable elaboration error family at the package boundary.
pub fn elaborate_pure_file(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  file : @parser.MlwFile,
) -> PureFile raise ElabError {
  normalize_elaboration_errors(
    () => elaborate_pure_file_raw(context, environment, file),
    FileRegistration,
  )
}

///|
/// Single-unit entry point used by selectors and differential tests.
pub fn elaborate_pure_unit(
  context : @identity.CompilationContext,
  environment : @environment.Environment,
  unit : @parser.MlwModule,
) -> @theory.Theory raise ElabError {
  normalize_elaboration_errors(
    () => elaborate_theory_unit(context, environment, unit),
    DeclarationElaboration,
  )
}
