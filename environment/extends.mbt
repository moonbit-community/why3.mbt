///|
pub extend EnvironmentDiagnostic with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend EnvironmentDiagnostic with Eq::{not_equal, equal}

///|
pub extend EnvironmentError with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend EnvironmentError with Eq::{not_equal, equal}

///|
pub extend EnvironmentErrorKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend EnvironmentErrorKind with Eq::{not_equal, equal}
