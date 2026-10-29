///|
pub extend ConfigDiagnostic with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ConfigDiagnostic with Eq::{not_equal, equal}

///|
pub extend ConfigError with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ConfigError with Eq::{not_equal, equal}

///|
pub extend ConfigErrorKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ConfigErrorKind with Eq::{not_equal, equal}

///|
pub extend MalformedProverOutput with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend MalformedProverOutput with Eq::{not_equal, equal}

///|
pub extend MalformedProverOutputDiagnostic with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend MalformedProverOutputDiagnostic with Eq::{not_equal, equal}

///|
pub extend MalformedProverOutputKind with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend MalformedProverOutputKind with Eq::{not_equal, equal}

///|
pub extend OutputLimitDiagnostic with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend OutputLimitDiagnostic with Eq::{not_equal, equal}

///|
pub extend OutputLimitExceeded with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend OutputLimitExceeded with Eq::{not_equal, equal}

///|
pub extend ParentDeadlinePolicy with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ParentDeadlinePolicy with Eq::{not_equal, equal}

///|
pub extend ProcessDiagnostic with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ProcessDiagnostic with Eq::{not_equal, equal}

///|
pub extend ProcessError with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ProcessError with Eq::{not_equal, equal}

///|
pub extend ProcessErrorKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ProcessErrorKind with Eq::{not_equal, equal}

///|
pub extend ProcessExitStatus with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ProcessExitStatus with Eq::{not_equal, equal}

///|
pub extend ProverResult with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ProverResult with Eq::{not_equal, equal}

///|
pub extend ProverStream with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ProverStream with Eq::{not_equal, equal}

///|
pub extend ProverTransport with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ProverTransport with Eq::{not_equal, equal}
