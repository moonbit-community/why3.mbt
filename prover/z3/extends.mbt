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
pub extend GoalUnitKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend GoalUnitKind with Eq::{not_equal, equal}

///|
pub extend ProverAnswerRule with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ProverAnswerRule with Eq::{not_equal, equal}

///|
pub extend SyntaxKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend SyntaxKind with Eq::{not_equal, equal}

///|
pub extend TransformId with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend TransformId with Eq::{not_equal, equal}

///|
pub extend Z3Printer with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Z3Printer with Eq::{not_equal, equal}
