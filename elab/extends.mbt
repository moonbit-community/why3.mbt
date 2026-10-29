///|
pub extend ElabDiagnostic with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ElabDiagnostic with Eq::{not_equal, equal}

///|
pub extend ElabError with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ElabError with Eq::{not_equal, equal}

///|
pub extend ElabErrorKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ElabErrorKind with Eq::{not_equal, equal}

///|
pub extend ElabStage with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ElabStage with Eq::{not_equal, equal}

///|
pub extend UnsupportedFeature with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend UnsupportedFeature with Eq::{not_equal, equal}
