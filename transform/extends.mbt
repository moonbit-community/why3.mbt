///|
pub extend TransformDiagnostic with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend TransformDiagnostic with Eq::{not_equal, equal}

///|
pub extend TransformError with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend TransformError with Eq::{not_equal, equal}

///|
pub extend TransformErrorKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend TransformErrorKind with Eq::{not_equal, equal}
