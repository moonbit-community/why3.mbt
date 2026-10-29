///|
pub extend TheoryDiagnostic with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend TheoryDiagnostic with Eq::{not_equal, equal}

///|
pub extend TheoryError with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend TheoryError with Eq::{not_equal, equal}

///|
pub extend TheoryErrorKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend TheoryErrorKind with Eq::{not_equal, equal}

///|
pub extend TheoryKey with Eq::{not_equal, equal}

///|
pub extend TheoryKey with Hash::{hash, hash_combine}
