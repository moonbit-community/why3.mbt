///|
pub extend BinaryLogicOp with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend BinaryLogicOp with Eq::{not_equal, equal}

///|
pub extend BuiltinTypeKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend BuiltinTypeKind with Eq::{not_equal, equal}

///|
pub extend Constant with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Constant with Eq::{not_equal, equal}

///|
pub extend DeclDependency with Eq::{not_equal, equal}

///|
pub extend DeclDependency with Hash::{hash, hash_combine}

///|
pub extend IntegerLiteralKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend IntegerLiteralKind with Eq::{not_equal, equal}

///|
pub extend LSymbol with Eq::{not_equal, equal}

///|
pub extend LSymbol with Hash::{hash, hash_combine}

///|
pub extend LogicSymbolRoleView with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend LogicSymbolRoleView with Eq::{not_equal, equal}

///|
pub extend PrSymbol with Eq::{not_equal, equal}

///|
pub extend PrSymbol with Hash::{hash, hash_combine}

///|
pub extend PropositionKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend PropositionKind with Eq::{not_equal, equal}

///|
pub extend Quantifier with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Quantifier with Eq::{not_equal, equal}

///|
pub extend RealLiteralKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend RealLiteralKind with Eq::{not_equal, equal}

///|
pub extend Term with Eq::{not_equal, equal}

///|
pub extend Ty with Eq::{not_equal, equal}

///|
pub extend Ty with Hash::{hash, hash_combine}

///|
pub extend TyVarSymbol with Eq::{not_equal, equal}

///|
pub extend TyVarSymbol with Hash::{hash, hash_combine}

///|
pub extend TypeDiagnostic with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend TypeDiagnostic with Eq::{not_equal, equal}

///|
pub extend TypeError with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend TypeError with Eq::{not_equal, equal}

///|
pub extend TypeErrorKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend TypeErrorKind with Eq::{not_equal, equal}

///|
pub extend TypeSymbol with Eq::{not_equal, equal}

///|
pub extend TypeSymbol with Hash::{hash, hash_combine}

///|
pub extend VSymbol with Eq::{not_equal, equal}

///|
pub extend VSymbol with Hash::{hash, hash_combine}
