///|
pub extend VcDiagnostic with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend VcDiagnostic with Eq::{not_equal, equal}

///|
pub extend VcError with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend VcError with Eq::{not_equal, equal}

///|
pub extend VcErrorKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend VcErrorKind with Eq::{not_equal, equal}
