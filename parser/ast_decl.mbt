///|
pub(all) struct Field {
  span : Span
  ident : Ident
  field_type : Pty
  mutable : Bool
  ghost : Bool
} derive(Debug, Eq)

///|
pub(all) struct AlgebraicCase {
  span : Span
  ident : Ident
  params : Array[Param]
} derive(Debug, Eq)

///|
pub(all) enum TypeDef {
  TDalias(Pty)
  TDalgebraic(Array[AlgebraicCase])
  TDrecord(Array[Field])
  TDrange(BigInt, BigInt)
  TDfloat(Int64, Int64)
} derive(Debug, Eq)

///|
pub(all) struct TypeDecl {
  span : Span
  ident : Ident
  params : Array[Ident]
  visibility : Visibility
  mutable : Bool
  invariant : Invariant
  witness : Expr?
  definition : TypeDef
} derive(Debug, Eq)

///|
pub(all) struct LogicDecl {
  span : Span
  ident : Ident
  params : Array[Param]
  return_type : Pty?
  definition : Term?
} derive(Debug, Eq)

///|
pub(all) struct InductiveCase {
  span : Span
  ident : Ident
  body : Term
} derive(Debug, Eq)

///|
pub(all) struct InductiveDecl {
  span : Span
  ident : Ident
  params : Array[Param]
  cases : Array[InductiveCase]
} derive(Debug, Eq)

///|
pub(all) enum MetaArg {
  Mty(Pty)
  Mfs(QualId)
  Mps(QualId)
  Max(QualId)
  Mlm(QualId)
  Mgl(QualId)
  Mval(QualId)
  Mstr(Bytes)
  Mint(Int64)
} derive(Debug, Eq)

///|
pub(all) enum CloneSubstitution {
  CStsym(QualId, Array[Ident], Pty)
  CSfsym(QualId, QualId)
  CSpsym(QualId, QualId)
  CSvsym(QualId, QualId)
  CSxsym(QualId, QualId)
  CSprop(PropositionKind)
  CSaxiom(QualId)
  CSlemma(QualId)
  CSgoal(QualId)
} derive(Debug, Eq)

///|
pub(all) enum Decl {
  Dtype(Array[TypeDecl])
  Dlogic(Array[LogicDecl])
  Dind(InductiveSign, Array[InductiveDecl])
  Dprop(PropositionKind, Ident, Term)
  Dlet(Ident, Bool, RoutineKind, Expr)
  Drec(Array[FunctionDef])
  Dexn(Ident, Pty, Mask)
  Dmeta(Ident, Array[MetaArg])
  Dcloneexport(Span, QualId, Array[CloneSubstitution])
  Duseexport(QualId)
  Dcloneimport(Span, Bool, QualId, Ident?, Array[CloneSubstitution])
  Duseimport(Span, Bool, Array[(QualId, Ident?)])
  Dimport(QualId)
  Dscope(Span, Bool, Ident, Array[Decl])
} derive(Debug, Eq)

///|
pub(all) struct MlwModule {
  kind : ModuleKind
  name : Ident
  interface : QualId?
  declarations : Array[Decl]
  span : Span
} derive(Debug, Eq)

///|
pub(all) enum MlwFile {
  Modules(Array[MlwModule])
  Decls(Array[Decl])
} derive(Debug, Eq)

///|
pub fn MlwFile::empty() -> MlwFile {
  Modules([])
}
