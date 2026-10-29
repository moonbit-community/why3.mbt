///|
pub extend PrinterDiagnostic with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend PrinterDiagnostic with Eq::{not_equal, equal}

///|
pub extend PrinterError with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend PrinterError with Eq::{not_equal, equal}

///|
pub extend PrinterErrorKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend PrinterErrorKind with Eq::{not_equal, equal}

///|
pub extend SmtToken with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend SmtToken with Eq::{not_equal, equal}

///|
pub extend SmtTokenKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend SmtTokenKind with Eq::{not_equal, equal}
