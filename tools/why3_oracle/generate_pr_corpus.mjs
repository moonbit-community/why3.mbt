// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import {
  lstatSync,
  mkdtempSync,
  readFileSync,
  readlinkSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  enumerateFixtures,
  validateManifest as validateParserManifest,
} from '../check_why3_fixtures.mjs';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const PARSER_ROOT = join(PROJECT_ROOT, 'fixtures', 'why3-1.7.2');
const STDLIB_ROOT = join(PARSER_ROOT, 'stdlib');
const FIXTURE_ROOT = join(SCRIPT_DIRECTORY, 'fixtures');
const WHY3_COMMIT = '1343338d3bb1941c0d4f134283bb0790816113c4';
const STDLIB_TREE_SHA256 = '355ec847dee8c9083ed6392ad5fa121285ce36f682950accc7982e3ba343dcc6';

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function canonicalSha(value) {
  return sha256(`${JSON.stringify(value)}\n`);
}

function compareUtf8(left, right) {
  return Buffer.compare(Buffer.from(left, 'utf8'), Buffer.from(right, 'utf8'));
}

function toPosix(path) {
  return path.split(sep).join('/');
}

function projectPath(path) {
  const projectRelative = toPosix(relative(PROJECT_ROOT, path));
  if (projectRelative === '..' || projectRelative.startsWith('../') ||
      projectRelative.startsWith('/')) {
    fail(`path escapes project root: ${path}`);
  }
  return projectRelative;
}

function run(command, argv, options = {}) {
  const result = spawnSync(command, argv, {
    cwd: options.cwd ?? PROJECT_ROOT,
    encoding: 'utf8',
    env: options.env ?? { ...process.env, LC_ALL: 'C' },
    maxBuffer: options.maxBuffer ?? 64 * 1024 * 1024,
    shell: false,
  });
  if (result.error && result.error.code !== 'EPERM') throw result.error;
  return result;
}

function runChecked(command, argv, options = {}) {
  const result = run(command, argv, options);
  if (result.status !== 0 || result.signal !== null) {
    fail(`${command} ${argv.join(' ')} failed: ${(result.stderr ?? '').trim()}`);
  }
  return result.stdout ?? '';
}

function verifyWhy3() {
  const version = runChecked('why3', ['--version']).trim();
  if (version !== 'Why3 platform, version 1.7.2') {
    fail(`expected Why3 1.7.2, got ${JSON.stringify(version)}`);
  }
}

function sourceRecord(absolutePath, extra = {}) {
  const metadata = lstatSync(absolutePath);
  const record = {
    path: projectPath(absolutePath),
    sha256: sha256(readFileSync(absolutePath)),
    kind: metadata.isSymbolicLink() ? 'symlink' : 'regular',
    ...extra,
  };
  if (metadata.isSymbolicLink()) record.symlinkTarget = readlinkSync(absolutePath);
  return record;
}

function bytesName(hex) {
  if (!/^(?:[0-9a-f]{2})*$/u.test(hex)) fail(`invalid bytes hex ${hex}`);
  const bytes = Buffer.from(hex, 'hex');
  const utf8 = bytes.toString('utf8');
  if (!Buffer.from(utf8, 'utf8').equals(bytes)) {
    fail(`Why3 emitted a non-UTF-8 unit/goal name: ${hex}`);
  }
  return { utf8, bytesHex: hex };
}

function compileGoalExporter(directory) {
  const output = join(directory, 'export-fixture-goals');
  const source = join(directory, 'export_fixture_goals.ml');
  writeFileSync(source, readFileSync(
    join(SCRIPT_DIRECTORY, 'export_fixture_goals.ml'),
  ));
  runChecked('ocamlfind', [
    'ocamlopt',
    '-linkpkg',
    '-package',
    'why3',
    source,
    '-o',
    output,
  ], { cwd: directory });
  return output;
}

function readGoalInventory(exporter, sourcePath) {
  const output = runChecked(exporter, [STDLIB_ROOT, sourcePath]);
  const units = new Map();
  for (const line of output.trimEnd().split('\n')) {
    if (line === '') continue;
    const [unitHex, ordinalText, goalHex, ...extra] = line.split('\t');
    if (extra.length !== 0 || !unitHex || ordinalText === undefined ||
        goalHex === undefined) {
      fail(`invalid fixture goal exporter line: ${JSON.stringify(line)}`);
    }
    const unitName = bytesName(unitHex);
    let unit = units.get(unitName.utf8);
    if (!unit) {
      unit = { ...unitName, goals: [] };
      units.set(unitName.utf8, unit);
    }
    if (ordinalText === '-') {
      if (goalHex !== '-' || unit.goals.length !== 0) {
        fail(`invalid empty goal inventory line: ${JSON.stringify(line)}`);
      }
      continue;
    }
    if (!/^\d+$/u.test(ordinalText)) fail(`invalid goal ordinal ${ordinalText}`);
    const ordinal = Number(ordinalText);
    if (ordinal !== unit.goals.length) {
      fail(`non-contiguous goal ordinal for ${unitName.utf8}: ${ordinal}`);
    }
    unit.goals.push({ ordinal, ...bytesName(goalHex) });
  }
  return units;
}

function selectUnits(allUnits, selectedNames) {
  return selectedNames.map((name, ordinal) => {
    const unit = allUnits.get(name);
    if (!unit) fail(`fixture is missing selected unit ${name}`);
    return { ordinal, utf8: unit.utf8, bytesHex: unit.bytesHex, goals: unit.goals };
  });
}

function expectedWhy3Rejection(sourcePath, expectedPattern) {
  const relativePath = projectPath(sourcePath);
  const result = run('why3', ['prove', '--type-only', relativePath]);
  if (result.status === 0 || result.signal !== null || result.stdout !== '') {
    fail(`expected deterministic Why3 rejection for ${relativePath}`);
  }
  const stderr = result.stderr ?? '';
  if (!expectedPattern.test(stderr)) {
    fail(`unexpected Why3 rejection for ${relativePath}: ${stderr.trim()}`);
  }
  return {
    exitCode: result.status,
    stderrUtf8: stderr,
    stderrSha256: sha256(stderr),
  };
}

function featureAssertions(features, fixtureId) {
  return features.variants
    .filter(variant =>
      variant.fixtureId === fixtureId || variant.rejectionFixtureId === fixtureId)
    .map(variant => ({
      enum: variant.enum,
      variant: variant.variant,
      role: variant.fixtureId === fixtureId ? 'primary' : 'rejection',
      disposition: variant.disposition,
      classificationStage: variant.classificationStage,
      errorKind: variant.errorKind,
    }));
}

function semanticEntry({
  id,
  source,
  units,
  featureTags,
  expected,
  assertions,
  referenceWhy3,
}) {
  return {
    id,
    kind: 'whyml-semantic',
    source,
    loadpathProfile: 'why3-stdlib-v1',
    featureTags: [...featureTags].sort(compareUtf8),
    expected,
    units,
    goalInventory: units.flatMap(unit =>
      unit.goals.map(goal => ({
        unitOrdinal: unit.ordinal,
        unitBytesHex: unit.bytesHex,
        goalOrdinal: goal.ordinal,
        goalBytesHex: goal.bytesHex,
      }))),
    featureAssertions: assertions,
    ...(referenceWhy3 ? { referenceWhy3 } : {}),
  };
}

function contractEntry(id, path, featureTags, inventory) {
  return {
    id,
    kind: 'contract-vector',
    source: sourceRecord(join(PROJECT_ROOT, path)),
    loadpathProfile: 'none',
    featureTags: [...featureTags].sort(compareUtf8),
    expected: { stage: 'contract-validation', kind: 'Exact', lane: 'exact' },
    units: [],
    goalInventory: [],
    inventory,
  };
}

function parseArguments(argv) {
  if (argv.length === 0) return { mode: 'stdout', path: null };
  if (argv.length !== 2 || !['--output', '--check'].includes(argv[0])) {
    fail('usage: generate_pr_corpus.mjs [--output PATH | --check PATH]');
  }
  return { mode: argv[0].slice(2), path: resolve(argv[1]) };
}

async function buildManifest() {
  verifyWhy3();
  const parserInventory = await enumerateFixtures(PARSER_ROOT);
  if (parserInventory.regular !== 976 || parserInventory.symlink !== 13 ||
      parserInventory.total !== 989) {
    fail(`parser fixture inventory drift: ${JSON.stringify(parserInventory)}`);
  }
  const parserManifest = JSON.parse(readFileSync(
    join(PROJECT_ROOT, 'tools', 'why3_reject_manifest.json'),
    'utf8',
  ));
  validateParserManifest(
    parserManifest,
    parserInventory.fixtures.map(fixture => fixture.relativePath),
  );
  const featuresPath = join(PROJECT_ROOT, 'tools', 'contracts', 'features-v1.json');
  const features = JSON.parse(readFileSync(featuresPath, 'utf8'));
  const driverPath = join(PROJECT_ROOT, 'tools', 'contracts', 'driver-closure-v1.json');
  const driver = JSON.parse(readFileSync(driverPath, 'utf8'));
  if (driver.semanticSnapshot.stdlibTree.sha256 !== STDLIB_TREE_SHA256) {
    fail('stdlib tree hash drifted from the fixed profile');
  }

  const parserSources = [];
  const parserEntries = [];
  const parserGroups = {
    'parser.ptree-exact': [],
    'parser.why3-rejects': [],
    'parser.module-interface-extension': [],
  };
  for (const fixture of parserInventory.fixtures) {
    const manifestEntry = parserManifest.entries[fixture.relativePath];
    let lane = 'exact';
    let group = 'parser.ptree-exact';
    let expectedKind = 'PtreeExact';
    if (manifestEntry?.lane === 'reject') {
      lane = 'reject';
      group = 'parser.why3-rejects';
      expectedKind = manifestEntry.moonbitKind;
    } else if (manifestEntry?.lane === 'extension') {
      lane = 'intentional-divergence';
      group = 'parser.module-interface-extension';
      expectedKind = 'AcceptExtension';
    }
    const id = `parser:${fixture.relativePath}`;
    const source = sourceRecord(fixture.absolutePath, {
      snapshotRelativePath: fixture.relativePath,
    });
    parserSources.push(source);
    parserGroups[group].push(id);
    parserEntries.push({
      id,
      kind: 'whyml-parser',
      source,
      loadpathProfile: 'none',
      featureTags: ['parser', group],
      expected: { stage: 'parser', kind: expectedKind, lane },
      units: [],
      goalInventory: [],
      ...(manifestEntry ? { parserReference: manifestEntry } : {}),
    });
  }

  const temporary = mkdtempSync(join(tmpdir(), 'why3-pr-corpus-'));
  let semanticEntries;
  try {
    const exporter = compileGoalExporter(temporary);
    const goalCache = new Map();
    function successfulCase({ id, path, unitNames, featureTags, expected }) {
      const absolutePath = join(PROJECT_ROOT, path);
      let inventory = goalCache.get(absolutePath);
      if (!inventory) {
        inventory = readGoalInventory(exporter, absolutePath);
        goalCache.set(absolutePath, inventory);
      }
      return semanticEntry({
        id,
        source: sourceRecord(absolutePath),
        units: selectUnits(inventory, unitNames),
        featureTags,
        expected,
        assertions: featureAssertions(features, id),
      });
    }

    const exactStages = [
      'parser',
      'typing',
      'typed-unit',
      'raw-task',
      'driver-update',
      'transform-checkpoints',
      'prepared-task',
      'smt-token-stream',
      'prover-result',
    ];
    const supported = [
      ['mvp.logic-core', 'tools/why3_oracle/fixtures/mvp.mlw', ['LogicCore', 'LogicReal'], ['bool', 'int', 'real', 'uninterpreted-symbols', 'ordinary-attribute'], 'Supported'],
      ['mvp.logic-polymorphism', 'tools/why3_oracle/fixtures/mvp.mlw', ['LogicPolymorphism'], ['abstract-type', 'alias-type', 'polymorphism', 'multiple-instantiations'], 'Supported'],
      ['mvp.logic-quantifiers', 'tools/why3_oracle/fixtures/mvp.mlw', ['LogicQuantifiers'], ['forall', 'exists', 'trigger'], 'Supported'],
      ['mvp.unit', 'tools/why3_oracle/fixtures/mvp.mlw', ['UnitMvp'], ['tuple0', 'unit'], 'Supported'],
      ['mvp.abs', 'tools/why3_oracle/fixtures/mvp.mlw', ['Abs'], ['if', 'program-int', 'requires-ensures', 'result', 'raw-vc'], 'Supported'],
      ['mvp.namespace', 'tools/why3_oracle/fixtures/mvp.mlw', ['NamespaceMvp'], ['qualified-lookup', 'scope', 'use'], 'Supported'],
      ['mvp.multiple-units', 'tools/why3_oracle/fixtures/mvp.mlw', ['MultiFirst', 'MultiSecond'], ['ordered-units', 'goal-inventory'], 'Supported'],
      ['mvp.routine-call', 'tools/why3_oracle/fixtures/mvp.mlw', ['RoutineCall'], ['program-call', 'requires-ensures', 'result'], 'Supported'],
      ['mvp.assert-assume', 'tools/why3_oracle/fixtures/mvp.mlw', ['AssertAssume'], ['assert', 'assume', 'requires-ensures'], 'Supported'],
      ['mvp.program-real', 'tools/why3_oracle/fixtures/mvp.mlw', ['ProgramReal'], ['program-real', 'program-call', 'requires-ensures', 'result'], 'Supported'],
      ['mutation.false-postcondition', 'tests/vc/false-post.mlw', ['FalsePost'], ['false-postcondition', 'mutation', 'program-int'], 'MutationExpectedNonValid'],
      ['transform.polymorphism', 'tools/why3_oracle/fixtures/transform-polymorphism.mlw', ['LogicPolymorphism'], ['free-type-variable', 'monomorphise-goal', 'polymorphic-checkpoints'], 'Supported'],
      ['transform.polymorphic-definition', 'tools/why3_oracle/fixtures/transform-polymorphic-definition.mlw', ['LogicPolymorphicDefinition'], ['polymorphic-definition', 'discriminate', 'encoding-guards'], 'Supported'],
      ['transform.inductive-snapshot', 'tools/why3_oracle/fixtures/transform-inductive.mlw', ['InductiveSnapshot'], ['oracle-only', 'trusted-inductive', 'eliminate-inductive', 'higher-order-encoding'], 'OracleOnlyTrusted'],
      ['smt.identifier-safety', 'tools/why3_oracle/fixtures/smt-identifiers.mlw', ['SmtIdentifiers'], ['generated-name-collision', 'goal-negation', 'reserved-smt-identifier'], 'Supported'],
      ['solver.outcomes', 'tools/why3_oracle/fixtures/solver-outcomes.mlw', ['SolverOutcomes'], ['solver-sat', 'solver-unknown', 'solver-unsat'], 'Supported'],
    ].map(([id, path, unitNames, featureTags, kind]) => successfulCase({
      id,
      path,
      unitNames,
      featureTags,
      expected: id === 'transform.inductive-snapshot'
        ? {
            stage: 'oracle-pipeline',
            kind,
            lane: 'exact',
            gateStages: [
              'typed-unit',
              'raw-task',
              'driver-update',
              'transform-checkpoints',
              'prepared-task',
              'smt-token-stream',
            ],
          }
        : { stage: 'full-pipeline', kind, lane: 'exact', gateStages: exactStages },
    }));

    const unsupportedDefinitions = [
      ['unsupported.check', 'check.mlw', ['CheckAssertion'], 'UnsupportedFeature(CheckAssertion)'],
      ['unsupported.clone', 'clone.mlw', ['CloneBase', 'CloneUse'], 'UnsupportedFeature(Clone)'],
      ['unsupported.control-attribute', 'control-attribute.mlw', ['ControlAttribute', 'UserStopSplit'], 'UnsupportedFeature(ControlAttribute)'],
      ['unsupported.datatypes', 'datatypes.mlw', ['Datatypes'], 'UnsupportedFeature(TypeDeclarationShape)'],
      ['unsupported.driver-only-theory', 'driver-only-theory.mlw', ['DriverOnlyTheory'], 'UnsupportedFeature(ExternalOrDriverOnlyImport)'],
      ['unsupported.effects', 'effects.mlw', ['TypePurification'], 'UnsupportedFeature(TypePurification)'],
      ['unsupported.exceptions', 'exceptions.mlw', ['Exceptions'], 'UnsupportedFeature(Exception)'],
      ['unsupported.function-kinds', 'function-kinds.mlw', ['FunctionKinds'], 'UnsupportedFeature(RoutineKind)'],
      ['unsupported.ghost', 'ghost.mlw', ['GhostResult'], 'UnsupportedFeature(Ghost)'],
      ['unsupported.higher-order', 'higher-order.mlw', ['HigherOrder'], 'UnsupportedFeature(HigherOrder)'],
      ['unsupported.inductive', 'inductive.mlw', ['Inductive'], 'UnsupportedFeature(Inductive)'],
      ['unsupported.lambda', 'lambda.mlw', ['Lambda'], 'UnsupportedFeature(Lambda)'],
      ['unsupported.logic-term', 'logic-term.mlw', ['ProofControl'], 'UnsupportedFeature(ProofControlConnective)'],
      ['unsupported.loops', 'loops.mlw', ['Loops'], 'UnsupportedFeature(Loop)'],
      ['unsupported.meta', 'meta.mlw', ['UserMeta'], 'UnsupportedFeature(UserMeta)'],
      ['unsupported.old-at', 'old-at.mlw', ['OldAt'], 'UnsupportedFeature(OldAt)'],
      ['unsupported.patterns', 'patterns.mlw', ['Patterns'], 'UnsupportedFeature(DestructuringPattern)'],
      ['unsupported.polymorphic-program', 'polymorphic-program.mlw', ['PolymorphicProgram'], 'TypeError(PolymorphicProgramRoutine)'],
      ['unsupported.program-expression', 'program-expression.mlw', ['ProgramExpression'], 'UnsupportedFeature(ProgramExpression)'],
      ['unsupported.recursion', 'recursion.mlw', ['Recursion'], 'UnsupportedFeature(Recursion)'],
      ['unsupported.references', 'references.mlw', ['References'], 'UnsupportedFeature(Reference)'],
      ['unsupported.strings', 'strings.mlw', ['Strings'], 'UnsupportedFeature(StringLiteral)'],
      ['unsupported.tuple', 'tuple.mlw', ['Tuple', 'TupleProgram'], 'UnsupportedFeature(TupleType)'],
    ].map(([id, file, unitNames, kind]) => successfulCase({
      id,
      path: `tools/why3_oracle/fixtures/unsupported/${file}`,
      unitNames,
      featureTags: [id, 'negative-capability'],
      expected: {
        stage: id === 'unsupported.polymorphic-program' ? 'program-typing' : 'feature-classification',
        kind,
        lane: 'unsupported',
        gateStages: ['parser', 'typing-reference', 'feature-classification'],
      },
    }));

    const epsilonPath = join(FIXTURE_ROOT, 'unsupported', 'epsilon.mlw');
    const epsilonReference = expectedWhy3Rejection(
      epsilonPath,
      /^Epsilon terms are currently not supported in WhyML\n$/u,
    );
    const epsilon = semanticEntry({
      id: 'unsupported.epsilon',
      source: sourceRecord(epsilonPath),
      units: [],
      featureTags: ['negative-capability', 'unsupported.epsilon'],
      expected: {
        stage: 'parser',
        kind: 'ParseError(UnsupportedEpsilon)',
        lane: 'unsupported',
        gateStages: ['parser', 'typing-reference-reject'],
      },
      assertions: featureAssertions(features, 'unsupported.epsilon'),
      referenceWhy3: epsilonReference,
    });

    const typingErrors = [
      ['typing.type-mismatch', 'typing-mismatch.mlw', /This term has type int, but is expected to have type bool/u, 'TypeError(TypeMismatch)'],
      ['typing.arity-mismatch', 'typing-arity.mlw', /This term has type int -> int, but is expected to have type int/u, 'TypeError(ArityMismatch)'],
      ['typing.occurs-check', 'typing-occurs.mlw', /This term has type 'xi -> 'xi1, but is expected to have type 'xi/u, 'TypeError(OccursCheck)'],
    ].map(([id, file, pattern, kind]) => {
      const absolutePath = join(FIXTURE_ROOT, file);
      return semanticEntry({
        id,
        source: sourceRecord(absolutePath),
        units: [],
        featureTags: ['negative-typing', id],
        expected: { stage: 'typing', kind, lane: 'reject', gateStages: ['parser', 'typing'] },
        assertions: [],
        referenceWhy3: expectedWhy3Rejection(absolutePath, pattern),
      });
    });
    semanticEntries = [...supported, ...typingErrors, ...unsupportedDefinitions, epsilon];
  } finally {
    rmSync(temporary, { recursive: true, force: true });
  }

  const canonicalVectors = JSON.parse(readFileSync(
    join(PROJECT_ROOT, 'tools/contracts/canonical-vectors-v1.json'), 'utf8'));
  const transformProfile = JSON.parse(readFileSync(
    join(PROJECT_ROOT, 'tools/contracts/transform-profile-v1.json'), 'utf8'));
  const contracts = [
    contractEntry(
      'contract.canonical-vectors',
      'tools/contracts/canonical-vectors-v1.json',
      ['canonical-encoding', 'cross-language-sha256'],
      canonicalVectors.vectors.map(vector => vector.name),
    ),
    contractEntry(
      'contract.driver-profile',
      'tools/contracts/driver-closure-v1.json',
      ['driver-catalog', 'driver-closure', 'trusted-snapshot'],
      {
        driverFiles: driver.driver.loadOrder,
        theoryRoots: driver.driver.theoryRoots,
        transforms: driver.driver.transformations,
      },
    ),
    contractEntry(
      'contract.transform-profile',
      'tools/contracts/transform-profile-v1.json',
      ['checkpoint-order', 'driver-transforms'],
      {
        raw: transformProfile.rawCheckpoint,
        monomorphic: transformProfile.tracePatch.checkpointSequences.monomorphic,
        polymorphic: transformProfile.tracePatch.checkpointSequences.polymorphic,
        final: transformProfile.finalCheckpoints,
      },
    ),
  ];

  const entries = [...parserEntries, ...semanticEntries, ...contracts]
    .sort((left, right) => compareUtf8(left.id, right.id));
  const entryIds = new Set(entries.map(entry => entry.id));
  if (entryIds.size !== entries.length) fail('duplicate corpus entry id');

  const fixtureGroups = [
    ...Object.entries(parserGroups).map(([id, members]) => ({ id, members })),
    {
      id: 'parser.literal-kinds',
      members: ['parser:tests/test-literals.mlw', 'mvp.logic-core'],
    },
  ].sort((left, right) => compareUtf8(left.id, right.id));
  const groupIds = new Set(fixtureGroups.map(group => group.id));
  for (const group of fixtureGroups) {
    for (const member of group.members) {
      if (!entryIds.has(member)) fail(`fixture group ${group.id} has unknown member ${member}`);
    }
  }
  const resolvableFixtures = new Set([...entryIds, ...groupIds]);
  for (const variant of features.variants) {
    for (const id of [variant.fixtureId, variant.rejectionFixtureId]) {
      if (id && !resolvableFixtures.has(id)) {
        fail(`feature ${variant.enum}.${variant.variant} has unresolved fixture ${id}`);
      }
    }
  }
  for (const lane of features.parserLanes) {
    if (!resolvableFixtures.has(lane.fixtureId)) {
      fail(`parser lane has unresolved fixture ${lane.fixtureId}`);
    }
  }

  const capabilityCoverage = [
    ['identity-shadowing-qualified-lookup', ['mvp.logic-core', 'mvp.namespace']],
    ['unify-occurs-arity-type-mismatch', ['typing.arity-mismatch', 'typing.occurs-check', 'typing.type-mismatch']],
    ['function-predicate-formula-value', ['mvp.logic-core']],
    ['bool-int-real-unit', ['mvp.logic-core', 'mvp.unit']],
    ['polymorphic-logic-and-multiple-instantiations', ['mvp.logic-polymorphism']],
    ['uninterpreted-sort-function-predicate', ['mvp.logic-core']],
    ['let-if-forall-exists-trigger', ['mvp.logic-core', 'mvp.logic-quantifiers']],
    ['axiom-lemma-goal-inventory', ['mvp.logic-core', 'mvp.multiple-units']],
    ['use-import-scope', ['mvp.namespace']],
    ['requires-ensures-result-assert-assume-call', ['mvp.abs', 'mvp.assert-assume', 'mvp.routine-call']],
    ['raw-vc-and-transform-checkpoints', ['mvp.abs', 'contract.transform-profile']],
    ['polymorphic-driver-checkpoints', ['transform.polymorphism', 'transform.polymorphic-definition', 'contract.transform-profile']],
    ['trusted-inductive-elimination-checkpoint', ['transform.inductive-snapshot', 'contract.transform-profile']],
    ['smt-generated-name-reserved-word-negation', ['smt.identifier-safety']],
    ['driver-catalog-and-trusted-types', ['contract.driver-profile', 'unsupported.driver-only-theory']],
    ['program-real', ['mvp.program-real']],
    ['program-false-postcondition', ['mutation.false-postcondition']],
    ['real-solver-unsat-sat-unknown', ['solver.outcomes']],
    [
      'all-unsupported-feature-groups',
      [...entryIds].filter(id => id.startsWith('unsupported.')).sort(compareUtf8),
    ],
    ['parser-989', ['parser.ptree-exact', 'parser.why3-rejects', 'parser.module-interface-extension']],
  ].map(([id, members]) => ({ id, members }));
  for (const capability of capabilityCoverage) {
    for (const member of capability.members) {
      if (!resolvableFixtures.has(member)) {
        fail(`capability ${capability.id} has unknown member ${member}`);
      }
    }
  }

  const parserSourceInventory = parserSources.map(source => ({
    path: source.snapshotRelativePath,
    kind: source.kind,
    sha256: source.sha256,
    ...(source.symlinkTarget ? { symlinkTarget: source.symlinkTarget } : {}),
  }));
  const localSources = [...new Map(
    semanticEntries.map(entry => [entry.source.path, entry.source]),
  ).values()].sort((left, right) => compareUtf8(left.path, right.path));
  return {
    schemaVersion: 1,
    profile: 'why3-1.7.2-z3-4.8.12-pr-corpus-v2',
    why3: { version: '1.7.2', commit: WHY3_COMMIT, shapeVersion: 6 },
    policy: {
      entryOrder: 'id bytewise ascending',
      sourceHash: 'SHA-256 of exact source bytes after resolving a recorded symlink',
      nameEncoding: 'UTF-8 diagnostic text plus authoritative lowercase bytesHex',
      noGlobsRangesOrDeferredSelection: true,
      portableRecordsExcludeMachineContext: true,
    },
    loadpathProfiles: [
      { id: 'none', entries: [] },
      {
        id: 'why3-stdlib-v1',
        entries: [{ path: 'fixtures/why3-1.7.2/stdlib', treeSha256: STDLIB_TREE_SHA256 }],
      },
    ],
    sourceInventories: {
      parserSnapshot: {
        root: 'fixtures/why3-1.7.2',
        regular: parserInventory.regular,
        symlink: parserInventory.symlink,
        total: parserInventory.total,
        sha256: canonicalSha(parserSourceInventory),
        entries: parserSourceInventory,
      },
      curated: {
        total: localSources.length,
        sha256: canonicalSha(localSources),
        entries: localSources,
      },
    },
    contractHashes: {
      featuresV1Sha256: sha256(readFileSync(featuresPath)),
      driverClosureV1Sha256: sha256(readFileSync(driverPath)),
      canonicalVectorsV1Sha256: sha256(readFileSync(join(PROJECT_ROOT, 'tools/contracts/canonical-vectors-v1.json'))),
      transformProfileV1Sha256: sha256(readFileSync(join(PROJECT_ROOT, 'tools/contracts/transform-profile-v1.json'))),
    },
    counts: {
      entries: entries.length,
      parserExact: parserGroups['parser.ptree-exact'].length,
      parserReject: parserGroups['parser.why3-rejects'].length,
      parserIntentionalDivergence: parserGroups['parser.module-interface-extension'].length,
      semantic: semanticEntries.length,
      contracts: contracts.length,
      goals: entries.reduce((count, entry) => count + entry.goalInventory.length, 0),
    },
    entriesSha256: canonicalSha(entries),
    fixtureGroupsSha256: canonicalSha(fixtureGroups),
    capabilityCoverageSha256: canonicalSha(capabilityCoverage),
    entries,
    fixtureGroups,
    capabilityCoverage,
  };
}

async function main() {
  const arguments_ = parseArguments(process.argv.slice(2));
  const rendered = `${JSON.stringify(await buildManifest(), null, 2)}\n`;
  if (arguments_.mode === 'output') {
    writeFileSync(arguments_.path, rendered);
  } else if (arguments_.mode === 'check') {
    if (readFileSync(arguments_.path, 'utf8') !== rendered) {
      fail(`${projectPath(arguments_.path)} does not match the generated PR corpus`);
    }
  } else {
    process.stdout.write(rendered);
  }
}

try {
  await main();
} catch (error) {
  process.stderr.write(`generate_pr_corpus: ${error.message}\n`);
  process.exitCode = 1;
}
