// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import {
  existsSync,
  readFileSync,
  readdirSync,
} from 'node:fs';
import { dirname, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const CONTRACT_ROOT = join(PROJECT_ROOT, 'tools', 'contracts');
const WHY3_COMMIT = '1343338d3bb1941c0d4f134283bb0790816113c4';
const LICENSE_SHA256 = '4b9eb976aecd9de79a0aff3a3bfea7134e8f4874d36b0783110c13ba837a8858';
const LICENSE_EXPRESSION = 'LGPL-2.1-only WITH OCaml-LGPL-linking-exception';
const SHA256_PATTERN = /^[0-9a-f]{64}$/u;
const COMMIT_PATTERN = /^[0-9a-f]{40}$/u;
const DIGEST_PATTERN = /^sha256:[0-9a-f]{64}$/u;
const SETUP_MOONBIT_ACTION =
  'moonbit-community/setup-moonbit@04293a8a813bfd4b6c2fce22701b52ae1050d100';
const LANES = new Set(['exact', 'reject', 'intentional-divergence', 'unsupported']);
const TOOLCHAIN_ARTIFACTS = [
  ['canonical-schema-v2', 'tools/contracts/canonical-schema-v2.json'],
  ['canonical-vectors-v1', 'tools/contracts/canonical-vectors-v1.json'],
  ['canonical-record-v2-json-schema', 'tools/contracts/schema/canonical-record-v2.schema.json'],
  ['driver-closure-v1', 'tools/contracts/driver-closure-v1.json'],
  ['features-v1', 'tools/contracts/features-v1.json'],
  ['moon-dependencies-v1', 'tools/contracts/moon-dependencies-v1.json'],
  ['oracle-goal-envelope-v1-json-schema', 'tools/contracts/schema/oracle-goal-envelope-v1.schema.json'],
  ['pr-corpus-v1', 'tools/contracts/pr-corpus-v1.json'],
  ['pr-golden-manifest-v1', 'tools/why3_oracle/goldens/pr-v1/manifest.json'],
  ['pr-prover-result-v1', 'tools/why3_oracle/goldens/pr-v1/prover-result.json'],
  ['runner-vectors-v1', 'tools/contracts/runner-vectors-v1.json'],
  ['semantic-profile-v1', 'tools/contracts/semantic-profile-v1.json'],
  ['toolchain-inputs-v1', 'tools/contracts/toolchain-inputs-v1.json'],
  ['toolchain-lock-v1-json-schema', 'tools/contracts/schema/toolchain-lock-v1.schema.json'],
  ['transform-profile-v1', 'tools/contracts/transform-profile-v1.json'],
  ['translated-files-v1', 'tools/contracts/translated-files-v1.json'],
  ['trusted-snapshot-schema-v1', 'tools/contracts/trusted-snapshot-schema-v1.json'],
  ['z3-static-profile-v1', 'prover/z3/z3-static-profile-v1.json'],
];

export function fail(message) {
  throw new Error(message);
}

export function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

export function canonicalSha(value) {
  return sha256(`${JSON.stringify(value)}\n`);
}

function compareUtf8(left, right) {
  return Buffer.compare(Buffer.from(left, 'utf8'), Buffer.from(right, 'utf8'));
}

function projectFile(path) {
  return join(PROJECT_ROOT, path);
}

function rootedFile(root, path) {
  return join(root, path);
}

function readJson(path) {
  return JSON.parse(readFileSync(projectFile(path), 'utf8'));
}

function assert(condition, message) {
  if (!condition) fail(message);
}

function assertEqual(actual, expected, message) {
  if (JSON.stringify(actual) !== JSON.stringify(expected)) {
    fail(`${message}: expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
  }
}

function runChecked(command, argv) {
  const result = spawnSync(command, argv, {
    cwd: PROJECT_ROOT,
    encoding: 'utf8',
    env: { ...process.env, LC_ALL: 'C' },
    maxBuffer: 128 * 1024 * 1024,
    shell: false,
  });
  if (result.status !== 0 || result.signal !== null || result.error) {
    const detail = `${result.stdout ?? ''}${result.stderr ?? ''}${result.error?.message ?? ''}`.trim();
    fail(`${command} ${argv.join(' ')} failed: ${detail}`);
  }
}

function parseArguments(argv) {
  const result = {
    why3Root: resolve(PROJECT_ROOT, '..', 'why3'),
    why3Archive: null,
    quick: false,
    requireToolchainLock: false,
    skipToolchainLock: false,
  };
  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index];
    if (argument === '--quick') result.quick = true;
    else if (argument === '--require-toolchain-lock') result.requireToolchainLock = true;
    else if (argument === '--skip-toolchain-lock') result.skipToolchainLock = true;
    else if (argument === '--why3-root' || argument === '--why3-archive') {
      const value = argv[index + 1];
      if (!value) fail(`${argument} requires a path`);
      if (argument === '--why3-root') result.why3Root = resolve(value);
      else result.why3Archive = resolve(value);
      index += 1;
    } else fail(`unknown argument ${argument}`);
  }
  if (result.requireToolchainLock && result.skipToolchainLock) {
    fail('--require-toolchain-lock and --skip-toolchain-lock are mutually exclusive');
  }
  return result;
}

function enumerateFiles(root, suffix) {
  const result = [];
  function visit(directory) {
    for (const child of readdirSync(directory, { withFileTypes: true })
      .sort((left, right) => compareUtf8(left.name, right.name))) {
      const path = join(directory, child.name);
      if (child.isDirectory()) {
        if (child.name !== '.git' && child.name !== '.mooncakes' && child.name !== '_build') visit(path);
      } else if (child.isFile() && child.name.endsWith(suffix)) result.push(path);
    }
  }
  visit(root);
  return result;
}

export function checkLicenseAndAttribution() {
  assertEqual(sha256(readFileSync(projectFile('LICENSE'))), LICENSE_SHA256, 'LICENSE hash');
  const moonMod = readFileSync(projectFile('moon.mod'), 'utf8');
  assert(
    moonMod.includes(`license = "${LICENSE_EXPRESSION}"`),
    'moon.mod license expression is not the project license',
  );
  for (const path of ['README.mbt.md', 'NOTICE']) {
    const source = readFileSync(projectFile(path), 'utf8');
    assert(source.includes('GNU Lesser General Public License'), `${path} omits LGPL attribution`);
    assert(source.includes('special linking exception'), `${path} omits the Why3 linking exception`);
    assert(source.includes(WHY3_COMMIT), `${path} omits the pinned Why3 commit`);
  }

  const manifest = readJson('tools/contracts/translated-files-v1.json');
  assertEqual(manifest.licenseExpression, LICENSE_EXPRESSION, 'translated-file license');
  assertEqual(manifest.why3.commit, WHY3_COMMIT, 'translated-file Why3 commit');
  const paths = manifest.entries.map(entry => entry.path);
  const adapterPaths = manifest.ocamlOracleAdapters.map(entry => entry.path);
  const allPaths = [...paths, ...adapterPaths];
  assertEqual(new Set(allPaths).size, allPaths.length, 'translated-file paths must be unique');
  const expectedHeader = `${manifest.requiredHeaderLines.join('\n')}\n`;
  for (const entry of manifest.entries) {
    assert(!entry.path.startsWith('/') && !entry.path.includes('..'), `unsafe translated path ${entry.path}`);
    const source = readFileSync(projectFile(entry.path), 'utf8');
    assert(source.startsWith(expectedHeader), `${entry.path} is missing the exact attribution header`);
    assert(/^\d{4}-\d{2}-\d{2}$/u.test(entry.translationDate), `${entry.path} has invalid translation date`);
    assert(
      /^\d{4}-\d{2}-\d{2}$/u.test(entry.lastSemanticModificationDate),
      `${entry.path} has invalid modification date`,
    );
    assert(entry.upstreamSources.length > 0, `${entry.path} has no upstream source mapping`);
    for (const upstream of entry.upstreamSources) {
      assert(!upstream.startsWith('/') && !upstream.includes('..'), `unsafe upstream path ${upstream}`);
    }
  }
  const manifested = new Set(paths);
  for (const absolutePath of enumerateFiles(PROJECT_ROOT, '.mbt')) {
    const source = readFileSync(absolutePath, 'utf8');
    if (source.includes('// Derived from Why3 1.7.2')) {
      const path = relative(PROJECT_ROOT, absolutePath).split(sep).join('/');
      assert(manifested.has(path), `${path} has a Why3-derived header but no manifest entry`);
    }
  }
  const manifestedAdapters = new Set(adapterPaths);
  for (const entry of manifest.ocamlOracleAdapters) {
    assert(!entry.path.startsWith('/') && !entry.path.includes('..'), `unsafe adapter path ${entry.path}`);
    const source = readFileSync(projectFile(entry.path), 'utf8');
    for (const required of [
      'The Why3 Verification Platform',
      'Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University',
      'GNU Lesser',
      'special exception',
      entry.lastSemanticModificationDate,
    ]) {
      assert(source.includes(required), `${entry.path} omits Why3 attribution ${required}`);
    }
    assert(/^\d{4}-\d{2}-\d{2}$/u.test(entry.translationDate), `${entry.path} has invalid translation date`);
    assert(
      /^\d{4}-\d{2}-\d{2}$/u.test(entry.lastSemanticModificationDate),
      `${entry.path} has invalid modification date`,
    );
    assert(entry.upstreamSources.length > 0, `${entry.path} has no upstream source mapping`);
    for (const upstream of entry.upstreamSources) {
      assert(!upstream.startsWith('/') && !upstream.includes('..'), `unsafe upstream path ${upstream}`);
    }
  }
  for (const absolutePath of enumerateFiles(join(PROJECT_ROOT, 'tools', 'why3_oracle'), '.ml')) {
    const source = readFileSync(absolutePath, 'utf8');
    if (source.includes('The Why3 Verification Platform')) {
      const path = relative(PROJECT_ROOT, absolutePath).split(sep).join('/');
      assert(manifestedAdapters.has(path), `${path} has a Why3 header but no adapter manifest entry`);
    }
  }
}

export function checkCanonicalContracts() {
  const schema = readJson('tools/contracts/canonical-schema-v2.json');
  const recordSchema = readJson('tools/contracts/schema/canonical-record-v2.schema.json');
  const envelopeSchema = readJson('tools/contracts/schema/oracle-goal-envelope-v1.schema.json');
  assertEqual(schema.schemaVersion, 2, 'canonical schema version');
  assertEqual(schema.recordVersion, 2, 'canonical record version');
  assert(!Object.hasOwn(schema.nodeFieldOrder, 'Dind.Coind'), 'Dind.Coind must remain outside schema v2');
  assertEqual(
    Object.keys(recordSchema.properties),
    schema.recordFieldOrder.CanonicalRecord,
    'canonical record property order',
  );
  assertEqual(
    Object.keys(envelopeSchema.properties),
    schema.recordFieldOrder.OracleGoalEnvelope,
    'oracle envelope property order',
  );
  assertEqual(envelopeSchema.properties.record.$ref, 'canonical-record-v2.schema.json', 'envelope record ref');
  const vectors = readJson('tools/contracts/canonical-vectors-v1.json');
  assertEqual(vectors.canonicalSchemaVersion, schema.schemaVersion, 'vector canonical schema version');
  const names = new Set();
  for (const vector of vectors.vectors) {
    assert(typeof vector.name === 'string' && !names.has(vector.name), 'canonical vector names must be unique');
    names.add(vector.name);
    const bytes = `${JSON.stringify(vector.canonical)}\n`;
    assertEqual(vector.canonicalBytesUtf8, bytes, `${vector.name} canonical bytes`);
    assertEqual(vector.canonicalSha256, sha256(bytes), `${vector.name} canonical hash`);
  }
}

export function checkDriverAndTrustedSchema() {
  const driver = readJson('tools/contracts/driver-closure-v1.json');
  assertEqual(driver.why3.commit, WHY3_COMMIT, 'driver Why3 commit');
  assertEqual(driver.why3.shapeVersion, 6, 'Why3 shape version');
  const { sha256: recordedDriverSha, ...driverContent } = driver.driver;
  assertEqual(recordedDriverSha, canonicalSha(driverContent), 'driver closure hash');
  assertEqual(
    driver.semanticSnapshot.stdlibTree.sha256,
    canonicalSha(driver.semanticSnapshot.stdlibTree.entries),
    'stdlib tree hash',
  );
  const snapshot = driver.semanticSnapshot;
  assertEqual(snapshot.sha256, canonicalSha({
    userVisibleProgramRoots: snapshot.userVisibleProgramRoots,
    theories: snapshot.theories,
    modules: snapshot.modules,
    records: snapshot.records,
    observedVariants: snapshot.observedVariants,
    stdlibTreeSha256: snapshot.stdlibTree.sha256,
  }), 'semantic snapshot hash');
  assertEqual(driver.driver.files.length, 7, 'recursive driver file count');
  assertEqual(driver.auxiliaryDrivers.map(file => file.path), ['why3.drv', 'why3_smt.drv'], 'auxiliary drivers');

  const trusted = readJson('tools/contracts/trusted-snapshot-schema-v1.json');
  assertEqual(trusted.why3Commit, WHY3_COMMIT, 'trusted schema Why3 commit');
  assertEqual(trusted.closureEvidence.driverSha256, driver.driver.sha256, 'trusted driver evidence');
  assertEqual(
    trusted.closureEvidence.semanticSnapshotSha256,
    snapshot.sha256,
    'trusted semantic evidence',
  );
  const observedMappings = {
    typeNode: 'type-node',
    typeSymbolDefinition: 'type-symbol-definition',
    constant: 'constant',
    termNode: 'term-node',
    patternNode: 'pattern-node',
    programDeclaration: 'program-declaration',
    programComputation: 'program-computation',
    programTypeNode: 'program-type-node',
    programEffect: 'program-effect',
    programTermination: 'program-termination',
    programMask: 'program-mask',
    programTypeWitness: 'program-type-witness',
    routineLogic: 'routine-logic',
  };
  for (const [allowedKey, observedKey] of Object.entries(observedMappings)) {
    const allowed = new Set(trusted.allowedVariants[allowedKey]);
    for (const variant of snapshot.observedVariants.semanticNodes[observedKey] ?? []) {
      assert(allowed.has(variant), `trusted schema omits observed ${observedKey} variant ${variant}`);
    }
    const rejected = new Set(trusted.explicitlyRejectedTrustedVariants[allowedKey] ?? []);
    for (const variant of snapshot.observedVariants.semanticNodes[observedKey] ?? []) {
      assert(!rejected.has(variant), `observed trusted variant is also rejected: ${observedKey}.${variant}`);
    }
  }
  assert(trusted.allowedVariants.declaration.includes('Dind:Ind'), 'trusted Dind:Ind is not allowed');
  assert(
    trusted.explicitlyRejectedTrustedVariants.declaration.includes('Dind:Coind'),
    'trusted Dind:Coind is not explicitly rejected',
  );
}

export function checkFeaturesAndCorpus() {
  const features = readJson('tools/contracts/features-v1.json');
  const corpus = readJson('tools/contracts/pr-corpus-v1.json');
  assertEqual(features.why3Commit, WHY3_COMMIT, 'feature Why3 commit');
  const variantKeys = features.variants.map(item => `${item.enum}.${item.variant}`);
  assertEqual(new Set(variantKeys).size, variantKeys.length, 'feature variants must be unique');
  assertEqual(features.variants.length, 169, 'Ptree variant inventory count');
  for (const variant of features.variants) {
    assert(LANES.has(variant.lane), `invalid feature lane ${variant.lane}`);
    assert(variant.allowedShapes.length + variant.rejectedShapes.length > 0, `${variantKeys} has no shapes`);
    if (variant.disposition === 'unsupported') {
      assert(variant.allowedShapes.length === 0, `${variant.enum}.${variant.variant} unexpectedly allows a shape`);
      assert(variant.errorKind !== null, `${variant.enum}.${variant.variant} has no stable error kind`);
    }
  }
  assert(features.controlAttributes.allowlist.length > 0, 'control attribute allowlist is empty');
  assert(features.controlAttributes.explicitUserRejects.includes('vc:sp'), 'vc:sp is not rejected');
  assert(features.controlAttributes.explicitUserRejects.includes('vc:wp'), 'vc:wp is not rejected');

  const ids = corpus.entries.map(entry => entry.id);
  assertEqual(ids, [...ids].sort(compareUtf8), 'corpus entry order');
  assertEqual(new Set(ids).size, ids.length, 'corpus ids must be unique');
  assertEqual(corpus.entriesSha256, canonicalSha(corpus.entries), 'corpus entry hash');
  assertEqual(corpus.fixtureGroupsSha256, canonicalSha(corpus.fixtureGroups), 'fixture group hash');
  assertEqual(
    corpus.capabilityCoverageSha256,
    canonicalSha(corpus.capabilityCoverage),
    'capability coverage hash',
  );
  const computedCounts = {
    entries: corpus.entries.length,
    parserExact: corpus.entries.filter(entry => entry.kind === 'whyml-parser' && entry.expected.lane === 'exact').length,
    parserReject: corpus.entries.filter(entry => entry.kind === 'whyml-parser' && entry.expected.lane === 'reject').length,
    parserIntentionalDivergence: corpus.entries.filter(entry => entry.kind === 'whyml-parser' && entry.expected.lane === 'intentional-divergence').length,
    semantic: corpus.entries.filter(entry => entry.kind === 'whyml-semantic').length,
    contracts: corpus.entries.filter(entry => entry.kind === 'contract-vector').length,
    goals: corpus.entries.reduce((count, entry) => count + entry.goalInventory.length, 0),
  };
  assertEqual(corpus.counts, computedCounts, 'corpus counts');
  assertEqual(
    corpus.sourceInventories.parserSnapshot.total,
    989,
    'parser snapshot fixture count',
  );
  const resolvable = new Set([
    ...ids,
    ...corpus.fixtureGroups.map(group => group.id),
  ]);
  for (const entry of corpus.entries) {
    assert(LANES.has(entry.expected.lane), `${entry.id} has invalid lane`);
    assert(Array.isArray(entry.featureTags) && entry.featureTags.length > 0, `${entry.id} has no feature tags`);
    assert(Array.isArray(entry.units) && Array.isArray(entry.goalInventory), `${entry.id} has no explicit inventory`);
    assert(!/[?*\[\]]/u.test(entry.source.path), `${entry.id} source path contains a glob`);
    if (entry.id === 'contract.canonical-vectors') {
      assert(Array.isArray(entry.inventory), `${entry.id} inventory is not an array`);
      assert(entry.inventory.every(item => item !== null), `${entry.id} contains a null vector id`);
    }
  }
  for (const variant of features.variants) {
    for (const fixture of [variant.fixtureId, variant.rejectionFixtureId]) {
      if (fixture !== null) assert(resolvable.has(fixture), `${variant.enum}.${variant.variant} fixture is unresolved`);
    }
  }
}

export function checkProfilesAndVectors() {
  const driver = readJson('tools/contracts/driver-closure-v1.json');
  const transform = readJson('tools/contracts/transform-profile-v1.json');
  assertEqual(transform.why3Commit, WHY3_COMMIT, 'transform Why3 commit');
  assertEqual(transform.driverClosureSha256, driver.driver.sha256, 'transform driver closure');
  assertEqual(transform.orderedDriverTransforms, driver.driver.transformations, 'ordered driver transforms');
  assertEqual(transform.tracePatch.status, 'active', 'trace patch lifecycle');
  assertEqual(transform.tracePatch.targetWhy3Commit, WHY3_COMMIT, 'trace patch target');
  assertEqual(
    transform.tracePatch.patchSha256,
    sha256(readFileSync(projectFile(transform.tracePatch.path))),
    'trace patch hash',
  );
  const monomorphicCheckpoints = [
    transform.driverUpdateCheckpoint,
    ...transform.orderedDriverTransforms,
  ];
  const polymorphicCheckpoints = [transform.driverUpdateCheckpoint];
  for (const name of transform.orderedDriverTransforms) {
    if (name === 'discriminate_if_poly') {
      polymorphicCheckpoints.push('discriminate_if_poly:monomorphise_goal');
    }
    if (name === 'encoding_smt_if_poly') {
      polymorphicCheckpoints.push(
        'encoding_smt_if_poly:monomorphise_goal',
        'encoding_smt_if_poly:select_kept',
        'encoding_smt_if_poly:keep_field_types',
        'encoding_smt_if_poly:twin',
        'encoding_smt_if_poly:guards',
      );
    }
    polymorphicCheckpoints.push(name);
  }
  assertEqual(
    transform.tracePatch.checkpointSequences,
    { monomorphic: monomorphicCheckpoints, polymorphic: polymorphicCheckpoints },
    'trace patch checkpoint sequences',
  );
  const z3Profile = readJson('prover/z3/z3-static-profile-v1.json');
  assertEqual(
    z3Profile.tracePatch,
    {
      targetWhy3Commit: WHY3_COMMIT,
      checkpointSequences: transform.tracePatch.checkpointSequences,
    },
    'Z3 profile trace patch binding',
  );
  assertEqual(new Set(transform.instrumentedSubcheckpoints).size, transform.instrumentedSubcheckpoints.length, 'subcheckpoint uniqueness');
  const runner = readJson('tools/contracts/runner-vectors-v1.json');
  const ids = [
    ...runner.resultParser,
    ...runner.runner,
    ...runner.cli,
    ...runner.context,
  ].map(vector => vector.id);
  assertEqual(new Set(ids).size, ids.length, 'runner vector ids must be unique');
  for (const required of [
    'runner.default-timeout',
    'runner.answer-then-cap',
    'runner.parent-deadline',
    'cli.valid-exit',
    'cli.nonvalid-exit',
    'cli.error-exit',
    'context.absolute-root-independence',
  ]) {
    assert(ids.includes(required), `runner contract omits ${required}`);
  }
  const semantic = readJson('tools/contracts/semantic-profile-v1.json');
  assertEqual(semantic.why3Commit, WHY3_COMMIT, 'semantic profile Why3 commit');
  for (const artifact of semantic.artifacts) {
    assertEqual(artifact.sha256, sha256(readFileSync(projectFile(artifact.path))), `${artifact.id} artifact hash`);
  }
  assertEqual(semantic.semanticProfileSha256, canonicalSha(semantic.artifacts), 'semantic profile hash');
}

function checkNoPlaceholder(value, path = '$') {
  if (Array.isArray(value)) {
    value.forEach((item, index) => checkNoPlaceholder(item, `${path}[${index}]`));
  } else if (value !== null && typeof value === 'object') {
    for (const [key, item] of Object.entries(value)) checkNoPlaceholder(item, `${path}.${key}`);
  } else if (typeof value === 'string') {
    assert(!/^(?:todo|tbd|placeholder|unknown|\.\.\.)$/iu.test(value), `placeholder at ${path}`);
    assert(!/^0{40}$|^0{64}$|^sha256:0{64}$/u.test(value), `zero placeholder at ${path}`);
  }
}

export function validateToolchainLock(
  lock,
  { projectRoot = PROJECT_ROOT, checkWorkflowSource = null } = {},
) {
  const readRoot = path => readFileSync(rootedFile(projectRoot, path));
  const readRootJson = path => JSON.parse(readRoot(path));
  const inputs = readRootJson('tools/contracts/toolchain-inputs-v1.json');
  const semanticProfile = readRootJson('tools/contracts/semantic-profile-v1.json');
  checkNoPlaceholder(lock);
  assert(!Object.hasOwn(inputs, 'moon'), 'toolchain inputs must not lock MoonBit');
  assert(!Object.hasOwn(inputs, 'moonDependencies'), 'toolchain inputs must not embed Moon dependencies');
  assert(!Object.hasOwn(lock, 'moon'), 'toolchain lock must not contain MoonBit');
  assert(!Object.hasOwn(lock, 'moonDependencies'), 'toolchain lock must not contain Moon dependencies');
  assertEqual(lock.schemaVersion, 1, 'toolchain lock schema version');
  assertEqual(lock.profile, 'why3-1.7.2-z3-4.8.12-mvp-v1', 'toolchain lock profile');
  assertEqual(lock.platform, inputs.oraclePlatform, 'toolchain platform');
  assert(DIGEST_PATTERN.test(lock.image.digest), 'toolchain image digest is invalid');
  assertEqual(lock.image.repository, 'ghcr.io/moonbit-community/why3.mbt-why3', 'toolchain image repository');
  assert(COMMIT_PATTERN.test(lock.buildRecipe.commit), 'toolchain build recipe commit is invalid');
  const { lockSha256, ...content } = lock;
  assertEqual(lockSha256, canonicalSha(content), 'toolchain lock self hash');
  assertEqual(lock.image.reference, `${lock.image.repository}@${lock.image.digest}`, 'toolchain image reference');
  assertEqual(lock.buildRecipe.path, inputs.buildRecipe.path, 'toolchain build recipe path');
  assertEqual(lock.buildRecipe.sha256, inputs.buildRecipe.sha256, 'toolchain build recipe hash');
  assertEqual(
    lock.buildRecipe.frontendImage,
    inputs.buildRecipe.frontendImage,
    'Dockerfile frontend image',
  );
  assertEqual(lock.buildRecipe.baseImage, inputs.baseImage, 'toolchain base image');
  assertEqual(
    lock.buildRecipe.sourceArchiveKeptInImage,
    inputs.buildRecipe.sourceArchiveKeptInImage,
    'Why3 source archive image path',
  );
  assertEqual(lock.githubActions, inputs.githubActions, 'toolchain GitHub Actions');
  assertEqual(lock.why3.version, inputs.why3.version, 'Why3 version');
  assertEqual(
    lock.why3.versionOutput,
    `Why3 platform, version ${inputs.why3.version}`,
    'Why3 version output',
  );
  assertEqual(lock.why3.commit, inputs.why3.commit, 'Why3 commit');
  assertEqual(lock.why3.shapeVersion, inputs.why3.shapeVersion, 'Why3 shape version');
  assertEqual(lock.why3.executable.path, inputs.why3.executablePath, 'Why3 executable path');
  assert(SHA256_PATTERN.test(lock.why3.executable.sha256), 'Why3 executable hash is invalid');
  assertEqual(lock.why3.datadir.path, inputs.why3.datadirPath, 'Why3 datadir path');
  assert(SHA256_PATTERN.test(lock.why3.datadir.treeSha256), 'Why3 datadir tree hash is invalid');
  assertEqual(
    lock.why3.datadir.stdlibTreeSha256,
    inputs.why3.stdlibTreeSha256,
    'Why3 stdlib tree',
  );
  assertEqual(lock.why3.driverClosureSha256, inputs.why3.driverClosureSha256, 'Why3 driver closure');
  assertEqual(
    lock.why3.semanticSnapshotSha256,
    inputs.why3.semanticSnapshotSha256,
    'Why3 semantic snapshot',
  );
  assertEqual(
    lock.why3.proverDetectionSha256,
    inputs.why3.proverDetectionSha256,
    'Why3 prover detection data',
  );
  assertEqual(
    lock.why3.sourceArchiveSha256,
    inputs.why3.referenceArchive.sha256,
    'Why3 retained source archive',
  );
  assertEqual(lock.why3.referenceArchive, inputs.why3.referenceArchive, 'Why3 reference archive');
  assertEqual(lock.why3.opamRecipe, inputs.why3.opamRecipe, 'Why3 opam recipe');
  assertEqual(lock.z3.version, inputs.z3.version, 'Z3 version');
  assertEqual(lock.z3.versionOutput, `Z3 version ${inputs.z3.version} - 64 bit`, 'Z3 version output');
  assertEqual(lock.z3.commit, inputs.z3.commit, 'Z3 commit');
  assertEqual(lock.z3.archive, inputs.z3.archive, 'Z3 archive');
  assertEqual(lock.z3.executable, inputs.z3.executable, 'Z3 executable');
  assertEqual(lock.environment, inputs.environment, 'fixed oracle environment');
  assertEqual(
    lock.contracts.semanticProfileSha256,
    semanticProfile.semanticProfileSha256,
    'locked semantic profile',
  );
  assertEqual(
    lock.contracts.prCorpusSha256,
    sha256(readRoot('tools/contracts/pr-corpus-v1.json')),
    'locked PR corpus',
  );
  const expectedArtifacts = TOOLCHAIN_ARTIFACTS.map(([id, path]) => ({
    id,
    path,
    sha256: sha256(readRoot(path)),
  }));
  assertEqual(lock.contracts.artifacts, expectedArtifacts, 'toolchain contract artifacts');
  const checkWorkflow = checkWorkflowSource ??
    readRoot('.github/workflows/check.yml').toString('utf8');
  assert(
    checkWorkflow.includes(`image: ${lock.image.reference}`),
    'check workflow image is not the literal locked digest',
  );
  assert(
    checkWorkflow.includes(`WHY3_ORACLE_IMAGE_DIGEST: ${lock.image.digest}`),
    'check workflow does not expose the literal locked digest to run-fixed',
  );
  assert(
    checkWorkflow.includes('--require-toolchain-lock'),
    'check workflow does not require the promoted toolchain lock',
  );
  assert(
    checkWorkflow.includes('tools/why3_oracle/run-fixed mvp.abs --'),
    'check workflow does not smoke-test the fixed Why3 entrypoint',
  );
  return lock;
}

export function checkToolchainLock(requireLock) {
  const lockPath = projectFile('tools/contracts/toolchain-lock.json');
  if (!existsSync(lockPath)) {
    if (requireLock) fail('tools/contracts/toolchain-lock.json is required but has not been promoted');
    return { present: false };
  }
  const lock = JSON.parse(readFileSync(lockPath, 'utf8'));
  validateToolchainLock(lock);
  return { present: true };
}

export function checkWorkflowPolicy() {
  for (const path of [
    '.github/workflows/check.yml',
    '.github/workflows/nightly-oracle.yml',
    '.github/workflows/update-oracle.yml',
    '.github/workflows/why3-image.yml',
  ]) {
    const source = readFileSync(projectFile(path), 'utf8');
    assert(!/uses:\s*[^\s]+@(?:main|master|v\d+)\b/u.test(source), `${path} has a floating action ref`);
    assert(source.includes(`uses: ${SETUP_MOONBIT_ACTION}`), `${path} omits pinned setup-moonbit`);
    assert(source.includes('          version: stable'), `${path} does not select MoonBit stable`);
    assert(!/\bmoon install\b/u.test(source), `${path} uses deprecated moon install`);
    const bootstrap = source.indexOf('moon update && moon check');
    const dependencyCheck = source.indexOf(
      'node tools/why3_oracle/generate_moon_dependency_inventory.mjs',
    );
    assert(bootstrap >= 0, `${path} omits moon update && moon check`);
    assert(dependencyCheck > bootstrap, `${path} does not verify dependencies after moon update`);
    assert(
      !/0\.1\.20260720|MOON_ARCHIVE_SHA256|\/opt\/moonbit|cli\.moonbitlang\.com/u.test(source),
      `${path} still locks the MoonBit toolchain`,
    );
  }
  const dockerfile = readFileSync(projectFile('Dockerfile'), 'utf8');
  assert(
    !/\bMOON_(?:VERSION|ARCHIVE_SHA256)\b|\/opt\/moonbit|cli\.moonbitlang\.com/u.test(dockerfile),
    'Dockerfile still installs or locks the MoonBit toolchain',
  );
  const imageWorkflow = readFileSync(projectFile('.github/workflows/why3-image.yml'), 'utf8');
  for (const required of [
    'platforms: linux/amd64',
    'steps.build.outputs.digest',
    'tools/why3_oracle/inspect_toolchain.mjs',
    'tools/why3_oracle/generate_toolchain_lock.mjs',
    'tools/why3_oracle/promote_toolchain_lock.mjs',
    '--project-root "$promotion_root"',
    '--skip-toolchain-lock',
    '--require-toolchain-lock',
    'tools/why3_oracle/run-fixed mvp.abs --',
    'tools/why3_oracle/run_elab_differential.mjs',
    'tools/why3_oracle/manage_pr_goldens.mjs --check',
    'tools/why3_oracle/sync_pr_golden_lock.mjs --check',
    'tools/why3_oracle/run_unsupported_gate.mjs',
    'tools/why3_oracle/run_result_differential.mjs',
    'moon test --target all --serial --release',
    'node --test tools/*.test.mjs',
    'node tools/check_why3_fixtures.mjs',
    'actions/upload-artifact@',
  ]) {
    assert(imageWorkflow.includes(required), `why3-image workflow omits ${required}`);
  }
  const checkWorkflow = readFileSync(projectFile('.github/workflows/check.yml'), 'utf8');
  assert(
    !checkWorkflow.includes('--skip-toolchain-lock'),
    'ordinary check workflow must validate the promoted toolchain lock',
  );
  for (const required of [
    'tools/why3_oracle/inspect_toolchain.mjs',
    'generate_moon_dependency_inventory.mjs',
    'moon check --target all --warn-list +73',
    'moon test --target all --serial --release',
    'node tools/check_why3_fixtures.mjs',
    'tools/why3_oracle/run_elab_differential.mjs',
    'tools/why3_oracle/manage_pr_goldens.mjs --check',
    'tools/why3_oracle/sync_pr_golden_lock.mjs --check',
    'tools/why3_oracle/run_unsupported_gate.mjs',
    'tools/why3_oracle/run_result_differential.mjs',
    'moon info',
    'moon fmt',
  ]) {
    assert(checkWorkflow.includes(required), `check workflow omits ${required}`);
  }
}

function runGeneratedChecks(arguments_) {
  const scripts = [
    ['tools/why3_oracle/generate_feature_manifest.mjs', '--check', 'tools/contracts/features-v1.json'],
    ['tools/why3_oracle/generate_schema_vectors.mjs', '--check', 'tools/contracts/canonical-vectors-v1.json'],
    ['tools/why3_oracle/generate_moon_dependency_inventory.mjs', '--check', 'tools/contracts/moon-dependencies-v1.json'],
    ['tools/why3_oracle/generate_semantic_profile.mjs', '--check', 'tools/contracts/semantic-profile-v1.json'],
    ['tools/why3_oracle/generate_toolchain_inputs.mjs', '--check', 'tools/contracts/toolchain-inputs-v1.json'],
  ];
  if (!arguments_.quick) {
    scripts.push([
      'tools/why3_oracle/generate_pr_corpus.mjs',
      '--check',
      'tools/contracts/pr-corpus-v1.json',
    ]);
    const driverSource = arguments_.why3Archive === null
      ? ['--why3-root', arguments_.why3Root]
      : ['--why3-archive', arguments_.why3Archive];
    scripts.push([
      'tools/why3_oracle/export_driver_inventory.mjs',
      ...driverSource,
      '--check',
      'tools/contracts/driver-closure-v1.json',
    ]);
  }
  for (const [script, ...argv] of scripts) runChecked(process.execPath, [script, ...argv]);
}

export function checkAll(arguments_) {
  checkLicenseAndAttribution();
  checkCanonicalContracts();
  checkDriverAndTrustedSchema();
  checkFeaturesAndCorpus();
  checkProfilesAndVectors();
  checkWorkflowPolicy();
  const toolchainLock = arguments_.skipToolchainLock
    ? { present: false, skipped: true }
    : checkToolchainLock(arguments_.requireToolchainLock);
  runGeneratedChecks(arguments_);
  return { toolchainLock };
}

const isMain = process.argv[1] !== undefined &&
  pathToFileURL(resolve(process.argv[1])).href === import.meta.url;
if (isMain) {
  try {
    const result = checkAll(parseArguments(process.argv.slice(2)));
    const lockStatus = result.toolchainLock.skipped
      ? 'candidate replacement'
      : result.toolchainLock.present ? 'promoted' : 'candidate pending';
    process.stdout.write(`PR-00 contracts verified (toolchain lock: ${lockStatus})\n`);
  } catch (error) {
    process.stderr.write(`check_pr00_contracts: ${error.message}\n`);
    process.exitCode = 1;
  }
}
