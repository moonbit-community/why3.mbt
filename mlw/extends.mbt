///|
pub extend Ity with Eq::{not_equal, equal}

///|
pub extend Ity with Hash::{hash, hash_combine}

///|
pub extend MlwDiagnostic with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend MlwDiagnostic with Eq::{not_equal, equal}

///|
pub extend MlwError with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend MlwError with Eq::{not_equal, equal}

///|
pub extend MlwErrorKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend MlwErrorKind with Eq::{not_equal, equal}

///|
pub extend PVariable with Eq::{not_equal, equal}

///|
pub extend PVariable with Hash::{hash, hash_combine}

///|
pub extend ProgramMask with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ProgramMask with Eq::{not_equal, equal}

///|
pub extend ProgramTermination with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ProgramTermination with Eq::{not_equal, equal}

///|
pub extend ProgramTypeArgumentFlag with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ProgramTypeArgumentFlag with Eq::{not_equal, equal}

///|
pub extend ProgramTypeFlags with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ProgramTypeFlags with Eq::{not_equal, equal}

///|
pub extend ProgramTypeSymbol with Eq::{not_equal, equal}

///|
pub extend ProgramTypeSymbol with Hash::{hash, hash_combine}

///|
pub extend RoutineSymbol with Eq::{not_equal, equal}

///|
pub extend RoutineSymbol with Hash::{hash, hash_combine}
