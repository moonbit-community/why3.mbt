// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..');
const AST_FILES = [
  'parser/ast_common.mbt',
  'parser/ast_ident_type.mbt',
  'parser/ast_term.mbt',
  'parser/ast_decl.mbt',
  'parser/ast_expr.mbt',
  'parser/literal.mbt',
];

function fail(message) {
  throw new Error(message);
}

function compareUtf8(left, right) {
  return Buffer.compare(Buffer.from(left, 'utf8'), Buffer.from(right, 'utf8'));
}

function discoverVariants() {
  const discovered = new Map();
  for (const path of AST_FILES) {
    const source = readFileSync(join(PROJECT_ROOT, path), 'utf8');
    const enumPattern = /pub(?:\(all\))?\s+enum\s+([A-Za-z][A-Za-z0-9_]*)\s*\{([\s\S]*?)\n\}/gu;
    for (const match of source.matchAll(enumPattern)) {
      const enumName = match[1];
      if (discovered.has(enumName)) fail(`duplicate public enum ${enumName}`);
      const variants = [];
      for (const line of match[2].split('\n')) {
        const variant = line.trim().match(/^([A-Z][A-Za-z0-9_]*)\b/u)?.[1];
        if (variant) variants.push(variant);
      }
      if (variants.length === 0) fail(`public enum ${enumName} has no variants`);
      discovered.set(enumName, { path, variants });
    }
  }
  return discovered;
}

const classifications = new Map();

function classify(enumName, variantNames, specification) {
  for (const variant of variantNames.trim().split(/\s+/u)) {
    const key = `${enumName}.${variant}`;
    if (classifications.has(key)) fail(`duplicate classification ${key}`);
    classifications.set(key, {
      enum: enumName,
      variant,
      disposition: specification.disposition ?? 'supported',
      allowedShapes: specification.allowedShapes,
      rejectedShapes: specification.rejectedShapes ?? [],
      classificationStage: specification.classificationStage,
      errorKind: specification.errorKind ?? null,
      fixtureId: specification.fixtureId,
      rejectionFixtureId: specification.rejectionFixtureId ?? null,
      lane: specification.lane ??
        (specification.disposition === 'unsupported' ? 'unsupported' : 'exact'),
    });
  }
}

const syntax = {
  disposition: 'supported',
  allowedShapes: ['All parser-produced shapes; semantic restrictions are carried by the enclosing node.'],
  classificationStage: 'parser',
  fixtureId: 'parser.ptree-exact',
};

classify('Attribute', 'Text', {
  ...syntax,
  disposition: 'partial',
  allowedShapes: ['Ordinary attributes are preserved as exact Bytes.', 'Generated/snapshot attributes allowed by the control-attribute policy.'],
  rejectedShapes: ['User attributes matching a known control pattern but absent from the allowlist.'],
  classificationStage: 'feature-classification',
  errorKind: 'UnsupportedFeature(ControlAttribute)',
  fixtureId: 'mvp.logic-core',
  rejectionFixtureId: 'unsupported.control-attribute',
});
classify('Attribute', 'Position', syntax);
classify('QualId', 'Qident Qdot', syntax);

classify('Pty', 'PTtyvar', {
  disposition: 'partial',
  allowedShapes: ['Pure-logic type variables generalized at declaration boundaries.'],
  rejectedShapes: ['Any residual type variable in a user program routine.'],
  classificationStage: 'program-finalize',
  errorKind: 'TypeError(PolymorphicProgramRoutine)',
  fixtureId: 'mvp.logic-polymorphism',
  rejectionFixtureId: 'unsupported.polymorphic-program',
});
classify('Pty', 'PTtyapp', {
  disposition: 'partial',
  allowedShapes: ['Bool, Int, Real, Unit, or user abstract/alias types in pure logic.', 'Monomorphic Bool, Int, Real, or Unit in user programs.'],
  rejectedShapes: ['User-visible driver-only range, float, bitvector, map, or string types.'],
  classificationStage: 'name-resolution',
  errorKind: 'UnsupportedFeature(DriverOnlyTheory)',
  fixtureId: 'mvp.logic-core',
  rejectionFixtureId: 'unsupported.driver-only-theory',
});
classify('Pty', 'PTtuple', {
  disposition: 'partial',
  allowedShapes: ['The empty tuple used as Unit.'],
  rejectedShapes: ['Non-empty user tuple types.'],
  classificationStage: 'type-elaboration',
  errorKind: 'UnsupportedFeature(TupleType)',
  fixtureId: 'mvp.unit',
  rejectionFixtureId: 'unsupported.tuple',
});
classify('Pty', 'PTref', {
  disposition: 'unsupported',
  allowedShapes: [],
  rejectedShapes: ['Every reference type.'],
  classificationStage: 'feature-classification',
  errorKind: 'UnsupportedFeature(Reference)',
  fixtureId: 'unsupported.references',
});
classify('Pty', 'PTarrow', {
  disposition: 'unsupported',
  allowedShapes: [],
  rejectedShapes: ['Every higher-order function type.'],
  classificationStage: 'feature-classification',
  errorKind: 'UnsupportedFeature(HigherOrder)',
  fixtureId: 'unsupported.higher-order',
});
classify('Pty', 'PTscope PTparen', {
  disposition: 'supported',
  allowedShapes: ['Qualified scope lookup and transparent parentheses around an otherwise supported type.'],
  classificationStage: 'type-elaboration',
  fixtureId: 'mvp.logic-core',
});
classify('Pty', 'PTpure', {
  disposition: 'unsupported',
  allowedShapes: [],
  rejectedShapes: ['Explicit program-type purification.'],
  classificationStage: 'feature-classification',
  errorKind: 'UnsupportedFeature(TypePurification)',
  fixtureId: 'unsupported.effects',
});

classify('PatternDesc', 'Pwild Pvar Pparen', {
  disposition: 'partial',
  allowedShapes: ['Simple wildcard or variable binders/result patterns, with transparent parentheses.'],
  rejectedShapes: ['Any nested occurrence that forms a destructuring pattern.'],
  classificationStage: 'pattern-elaboration',
  errorKind: 'UnsupportedFeature(DestructuringPattern)',
  fixtureId: 'mvp.abs',
  rejectionFixtureId: 'unsupported.patterns',
});
classify('PatternDesc', 'Papp Prec Ptuple Pas Por Pcast Pscope Pghost', {
  disposition: 'unsupported',
  allowedShapes: [],
  rejectedShapes: ['Every constructor, record, tuple, alias, or-pattern, cast, scoped, or ghost pattern.'],
  classificationStage: 'feature-classification',
  errorKind: 'UnsupportedFeature(DestructuringPattern)',
  fixtureId: 'unsupported.patterns',
});

classify('TermDesc', 'Ttrue Tfalse Tconst Tident Tidapp Tinfix Tinnfix Tbinop Tbinnop Tnot Tif Tattr Tlet Tcast Tscope', {
  disposition: 'partial',
  allowedShapes: ['First-order Bool/Int/Real/Unit values and formulas using supported symbols.', 'Ordinary byte-preserved attributes and explicit casts between supported expected kinds.'],
  rejectedShapes: ['A nested unsupported type, symbol, constant, or control attribute.'],
  classificationStage: 'term-elaboration',
  errorKind: 'UnsupportedFeature(NestedUnsupportedTerm)',
  fixtureId: 'mvp.logic-core',
  rejectionFixtureId: 'unsupported.logic-term',
});
classify('TermDesc', 'Tquant', {
  disposition: 'partial',
  allowedShapes: ['Forall and exists with first-order binders and validated triggers.'],
  rejectedShapes: ['Lambda quantifier or unsupported binder/type/trigger shapes.'],
  classificationStage: 'term-elaboration',
  errorKind: 'UnsupportedFeature(Lambda)',
  fixtureId: 'mvp.logic-quantifiers',
  rejectionFixtureId: 'unsupported.lambda',
});
classify('TermDesc', 'Ttuple', {
  disposition: 'partial',
  allowedShapes: ['The empty tuple used as Unit.'],
  rejectedShapes: ['Every non-empty tuple term.'],
  classificationStage: 'term-elaboration',
  errorKind: 'UnsupportedFeature(TupleTerm)',
  fixtureId: 'mvp.unit',
  rejectionFixtureId: 'unsupported.tuple',
});
classify('TermDesc', 'Tasref', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every auto-reference term.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(Reference)', fixtureId: 'unsupported.references',
});
classify('TermDesc', 'Tapply', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every higher-order term application.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(HigherOrderApplication)', fixtureId: 'unsupported.higher-order',
});
classify('TermDesc', 'Teps', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every user epsilon term.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(Epsilon)', fixtureId: 'unsupported.epsilon',
});
classify('TermDesc', 'Tcase Trecord Tupdate', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every user case, record, or record-update term.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(AlgebraicData)', fixtureId: 'unsupported.datatypes',
});
classify('TermDesc', 'Tat', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every old/at label term.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(OldAt)', fixtureId: 'unsupported.old-at',
});

classify('TypeDef', 'TDalias', {
  disposition: 'supported', allowedShapes: ['Parameterized or monomorphic non-recursive aliases.'],
  classificationStage: 'declaration-elaboration', fixtureId: 'mvp.logic-polymorphism',
});
classify('TypeDef', 'TDrecord', {
  disposition: 'partial',
  allowedShapes: ['Empty immutable record with Abstract visibility, no invariant, and no witness, representing an abstract type.'],
  rejectedShapes: ['Every concrete record, mutable type, invariant, or witness.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(RecordOrInvariant)',
  fixtureId: 'mvp.logic-polymorphism', rejectionFixtureId: 'unsupported.datatypes',
});
classify('TypeDef', 'TDalgebraic', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every user algebraic datatype.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(Datatype)', fixtureId: 'unsupported.datatypes',
});
classify('TypeDef', 'TDrange TDfloat', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every user range or floating-point type.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(DriverOnlyType)', fixtureId: 'unsupported.driver-only-theory',
});

classify('MetaArg', 'Mty Mfs Mps Max Mlm Mgl Mval Mstr Mint', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['All arguments are rejected because user Dmeta is rejected as a whole.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(UserMeta)', fixtureId: 'unsupported.meta',
});
classify('CloneSubstitution', 'CStsym CSfsym CSpsym CSvsym CSxsym CSprop CSaxiom CSlemma CSgoal', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['All substitutions are rejected because user clone is rejected as a whole.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(Clone)', fixtureId: 'unsupported.clone',
});

classify('Decl', 'Dtype', {
  disposition: 'partial', allowedShapes: ['Parameterized abstract and alias types described by the TypeDef policy.'],
  rejectedShapes: ['Datatype, record, range, float, mutable, invariant, or witness declarations.'],
  classificationStage: 'declaration-elaboration', errorKind: 'UnsupportedFeature(TypeDeclarationShape)',
  fixtureId: 'mvp.logic-polymorphism', rejectionFixtureId: 'unsupported.datatypes',
});
classify('Decl', 'Dlogic', {
  disposition: 'partial', allowedShapes: ['Non-recursive polymorphic constant, function, and predicate declarations.'],
  rejectedShapes: ['Recursive or higher-order logic definitions.'], classificationStage: 'declaration-elaboration',
  errorKind: 'UnsupportedFeature(RecursiveOrHigherOrderLogic)', fixtureId: 'mvp.logic-core', rejectionFixtureId: 'unsupported.recursion',
});
classify('Decl', 'Dprop', {
  disposition: 'supported', allowedShapes: ['Polymorphic axiom, lemma, and goal formulas.'],
  classificationStage: 'declaration-elaboration', fixtureId: 'mvp.logic-core',
});
classify('Decl', 'Dlet', {
  disposition: 'partial', allowedShapes: ['Non-recursive top-level RLnone let routine or abstract val with a pure MVP contract.'],
  rejectedShapes: ['let function, val function, lemma routine, ghost/effectful routine, or unsupported body/spec.'],
  classificationStage: 'program-elaboration', errorKind: 'UnsupportedFeature(ProgramRoutineShape)',
  fixtureId: 'mvp.abs', rejectionFixtureId: 'unsupported.function-kinds',
});
classify('Decl', 'Dscope Duseexport Duseimport Dimport', {
  disposition: 'partial', allowedShapes: ['Scopes and same-file/builtin use or use import.'],
  rejectedShapes: ['External loadpath or driver-only theory import.'], classificationStage: 'name-resolution',
  errorKind: 'UnsupportedFeature(ExternalOrDriverOnlyImport)', fixtureId: 'mvp.namespace', rejectionFixtureId: 'unsupported.driver-only-theory',
});
classify('Decl', 'Dind', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every user inductive/coinductive declaration.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(Inductive)', fixtureId: 'unsupported.inductive',
});
classify('Decl', 'Drec', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every recursive program declaration.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(Recursion)', fixtureId: 'unsupported.recursion',
});
classify('Decl', 'Dexn', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every exception declaration.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(Exception)', fixtureId: 'unsupported.exceptions',
});
classify('Decl', 'Dmeta', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every user meta declaration.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(UserMeta)', fixtureId: 'unsupported.meta',
});
classify('Decl', 'Dcloneexport Dcloneimport', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every user clone declaration.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(Clone)', fixtureId: 'unsupported.clone',
});

classify('MlwFile', 'Modules Decls', {
  disposition: 'supported', allowedShapes: ['A single file containing ordered theory/module units or top-level declarations.'],
  classificationStage: 'file-elaboration', fixtureId: 'mvp.multiple-units',
});

classify('ExprDesc', 'Etrue Efalse Econst Eident Eidapp Einfix Einnfix Eif Eand Eor Enot Esequence Epure Eidpur Escope Ecast Eattr', {
  disposition: 'partial',
  allowedShapes: ['Monomorphic Bool/Int/Real/Unit expressions, pure logic/routine operators, and supported sequencing/casts/attributes.'],
  rejectedShapes: ['Any nested unsupported symbol, type, constant, effect, or control attribute.'],
  classificationStage: 'program-elaboration', errorKind: 'UnsupportedFeature(NestedUnsupportedExpression)',
  fixtureId: 'mvp.abs', rejectionFixtureId: 'unsupported.program-expression',
});
classify('ExprDesc', 'Elet', {
  disposition: 'partial', allowedShapes: ['Simple non-recursive RLnone local value binding.'],
  rejectedShapes: ['Local function/predicate/lemma, ghost binding, or unsupported pattern/effect.'],
  classificationStage: 'program-elaboration', errorKind: 'UnsupportedFeature(LocalRoutine)', fixtureId: 'mvp.abs', rejectionFixtureId: 'unsupported.function-kinds',
});
classify('ExprDesc', 'Eany', {
  disposition: 'partial', allowedShapes: ['Top-level ordinary RLnone abstract val with pure pre/post contract.'],
  rejectedShapes: ['First-class any expression, val function/predicate/lemma, ghost/effectful contract, or polymorphic user routine.'],
  classificationStage: 'program-elaboration', errorKind: 'UnsupportedFeature(AbstractRoutineShape)', fixtureId: 'mvp.routine-call', rejectionFixtureId: 'unsupported.function-kinds',
});
classify('ExprDesc', 'Etuple', {
  disposition: 'partial', allowedShapes: ['The empty tuple Unit expression.'], rejectedShapes: ['Every non-empty tuple expression.'],
  classificationStage: 'program-elaboration', errorKind: 'UnsupportedFeature(TupleExpression)', fixtureId: 'mvp.unit', rejectionFixtureId: 'unsupported.tuple',
});
classify('ExprDesc', 'Eassert', {
  disposition: 'partial', allowedShapes: ['Assert and Assume formulas.'], rejectedShapes: ['Check assertion kind.'],
  classificationStage: 'program-elaboration', errorKind: 'UnsupportedFeature(CheckAssertion)', fixtureId: 'mvp.assert-assume', rejectionFixtureId: 'unsupported.check',
});
classify('ExprDesc', 'Eref Easref Eapply Erec Efun Erecord Eupdate Eassign Ewhile Ematch Eabsurd Eraise Eexn Eoptexn Efor Elabel Eghost', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every occurrence; feature kind is refined from the concrete ExprDesc before typing.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(ProgramExpression)', fixtureId: 'unsupported.program-expression',
});

classify('BinaryLogicOp', 'DTand DTandAsym DTor DTorAsym DTimplies DTiff', {
  disposition: 'supported', allowedShapes: ['First-order formula operands with Why3 ordering/coercion semantics.'],
  classificationStage: 'term-elaboration', fixtureId: 'mvp.logic-core',
});
classify('BinaryLogicOp', 'DTby DTso', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Proof-control by/so connectives.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(ProofControlConnective)', fixtureId: 'unsupported.logic-term',
});
classify('Quantifier', 'DTforall DTexists', {
  disposition: 'supported', allowedShapes: ['First-order quantified formula with validated binders/triggers.'],
  classificationStage: 'term-elaboration', fixtureId: 'mvp.logic-quantifiers',
});
classify('Quantifier', 'DTlambda', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every lambda.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(Lambda)', fixtureId: 'unsupported.lambda',
});
classify('RoutineKind', 'RKnone', {
  disposition: 'supported', allowedShapes: ['Ordinary user let/val routine.'], classificationStage: 'program-elaboration', fixtureId: 'mvp.abs',
});
classify('RoutineKind', 'RKlocal RKfunc RKpred RKlemma', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every user local/function/predicate/lemma routine kind.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(RoutineKind)', fixtureId: 'unsupported.function-kinds',
});
classify('AssertionKind', 'Assert Assume', {
  disposition: 'supported', allowedShapes: ['Program assert or assume.'], classificationStage: 'program-elaboration', fixtureId: 'mvp.assert-assume',
});
classify('AssertionKind', 'Check', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every check assertion.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(CheckAssertion)', fixtureId: 'unsupported.check',
});
classify('ForDirection', 'To DownTo', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every for-loop direction because all loops are rejected.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(Loop)', fixtureId: 'unsupported.loops',
});
classify('Mask', 'MaskVisible', {
  disposition: 'supported', allowedShapes: ['Visible non-ghost result.'], classificationStage: 'program-elaboration', fixtureId: 'mvp.abs',
});
classify('Mask', 'MaskTuple MaskGhost', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every tuple/ghost result mask.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(Ghost)', fixtureId: 'unsupported.ghost',
});
classify('InductiveSign', 'Ind Coind', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every user inductive/coinductive sign.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(Inductive)', fixtureId: 'unsupported.inductive',
});
classify('PropositionKind', 'Plemma Paxiom Pgoal', {
  disposition: 'supported', allowedShapes: ['Well-typed pure formula.'], classificationStage: 'declaration-elaboration', fixtureId: 'mvp.logic-core',
});
classify('Visibility', 'Public Abstract', {
  disposition: 'partial', allowedShapes: ['Public alias/abstract type and Abstract empty-record type.'],
  rejectedShapes: ['Visibility used with an unsupported type shape.'], classificationStage: 'declaration-elaboration',
  errorKind: 'UnsupportedFeature(TypeVisibilityShape)', fixtureId: 'mvp.logic-polymorphism', rejectionFixtureId: 'unsupported.datatypes',
});
classify('Visibility', 'Private', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every private user type.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(PrivateType)', fixtureId: 'unsupported.datatypes',
});
classify('ModuleKind', 'Theory Module', {
  disposition: 'supported', allowedShapes: ['Ordered theory or module unit in the single input file.'], classificationStage: 'file-elaboration', fixtureId: 'mvp.multiple-units',
});

classify('IntLiteralKind', 'ILitUnk ILitDec ILitHex ILitOct ILitBin', {
  disposition: 'supported', allowedShapes: ['Exact arbitrary-precision integer representation; no host floating conversion.'], classificationStage: 'literal-elaboration', fixtureId: 'parser.literal-kinds',
});
classify('RealLiteralKind', 'RLitUnk RLitDec RLitHex', {
  disposition: 'supported', allowedShapes: ['Exact significand/pow2/pow5 representation; no Double conversion.'], classificationStage: 'literal-elaboration', fixtureId: 'parser.literal-kinds',
});
classify('Constant', 'ConstInt ConstReal', {
  disposition: 'supported', allowedShapes: ['Exact Int or Real constant in a supported expected type.'], classificationStage: 'literal-elaboration', fixtureId: 'parser.literal-kinds',
});
classify('Constant', 'ConstStr', {
  disposition: 'unsupported', allowedShapes: [], rejectedShapes: ['Every user string constant; trusted snapshot strings use the decoder schema.'],
  classificationStage: 'feature-classification', errorKind: 'UnsupportedFeature(StringLiteral)', fixtureId: 'unsupported.strings',
});

function buildManifest() {
  const discovered = discoverVariants();
  const expected = new Set();
  for (const [enumName, { variants }] of discovered) {
    for (const variant of variants) expected.add(`${enumName}.${variant}`);
  }
  const missing = [...expected].filter(key => !classifications.has(key)).sort(compareUtf8);
  const extra = [...classifications.keys()].filter(key => !expected.has(key)).sort(compareUtf8);
  if (missing.length > 0 || extra.length > 0) {
    fail(`classification mismatch; missing=${JSON.stringify(missing)} extra=${JSON.stringify(extra)}`);
  }
  const variants = [...classifications.values()]
    .map(entry => ({ ...entry, source: discovered.get(entry.enum).path }))
    .sort((left, right) =>
      compareUtf8(`${left.enum}.${left.variant}`, `${right.enum}.${right.variant}`));
  return {
    schemaVersion: 1,
    why3Version: '1.7.2',
    why3Commit: '1343338d3bb1941c0d4f134283bb0790816113c4',
    policy: {
      ordinaryTermAttributes: 'preserve exact Bytes and source attachment',
      knownControlDefault: 'reject',
      userDmeta: 'reject at feature-classification as UnsupportedFeature(UserMeta)',
      allowedLanes: ['exact', 'reject', 'intentional-divergence', 'unsupported'],
    },
    controlAttributes: {
      knownControlPatterns: [
        { kind: 'prefix', bytesUtf8: 'vc:' },
        { kind: 'prefix', bytesUtf8: 'encoding:' },
        { kind: 'prefix', bytesUtf8: 'algebraic:' },
        { kind: 'prefix', bytesUtf8: 'remove_unused:' },
        { kind: 'exact', bytesUtf8: 'select_alginst_default' },
        { kind: 'exact', bytesUtf8: 'eliminate_algebraic' },
        { kind: 'exact', bytesUtf8: 'get_counterexmp' },
      ],
      allowlist: [
        { bytesUtf8: 'stop_split', origins: ['Snapshot', 'Generated(wp)'] },
      ],
      explicitUserRejects: ['vc:sp', 'vc:wp'],
    },
    parserLanes: [
      { fixtureId: 'parser.ptree-exact', lane: 'exact' },
      { fixtureId: 'parser.why3-rejects', lane: 'reject' },
      { fixtureId: 'parser.module-interface-extension', lane: 'intentional-divergence' },
    ],
    variants,
  };
}

function renderManifest() {
  return `${JSON.stringify(buildManifest(), null, 2)}\n`;
}

function run() {
  const [mode, path, ...rest] = process.argv.slice(2);
  if (rest.length > 0 || (mode !== undefined && mode !== '--output' && mode !== '--check') ||
      (mode !== undefined && path === undefined)) {
    fail('usage: generate_feature_manifest.mjs [--output PATH | --check PATH]');
  }
  const rendered = renderManifest();
  if (mode === '--output') {
    writeFileSync(resolve(path), rendered);
  } else if (mode === '--check') {
    if (readFileSync(resolve(path), 'utf8') !== rendered) {
      fail(`${path} does not match the generated feature manifest`);
    }
  } else {
    process.stdout.write(rendered);
  }
}

try {
  run();
} catch (error) {
  process.stderr.write(`generate_feature_manifest: ${error.message}\n`);
  process.exitCode = 1;
}
