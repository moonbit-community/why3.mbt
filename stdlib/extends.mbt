///|
pub extend BindDiagnostic with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend BindDiagnostic with Eq::{not_equal, equal}

///|
pub extend BindError with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend BindError with Eq::{not_equal, equal}

///|
pub extend BindErrorKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend BindErrorKind with Eq::{not_equal, equal}

///|
pub extend SnapshotDiagnostic with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend SnapshotDiagnostic with Eq::{not_equal, equal}

///|
pub extend SnapshotError with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend SnapshotError with Eq::{not_equal, equal}

///|
pub extend SnapshotErrorKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend SnapshotErrorKind with Eq::{not_equal, equal}
