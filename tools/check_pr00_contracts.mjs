// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import {
  readFileSync,
  readdirSync,
} from 'node:fs';
import { dirname, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import referenceEnvironment from './why3_reference/reference_environment.cjs';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const WHY3_COMMIT = '1343338d3bb1941c0d4f134283bb0790816113c4';
const LICENSE_SHA256 = '4b9eb976aecd9de79a0aff3a3bfea7134e8f4874d36b0783110c13ba837a8858';
const LICENSE_EXPRESSION = 'LGPL-2.1-only WITH OCaml-LGPL-linking-exception';
const LANES = new Set(['exact', 'reject', 'intentional-divergence', 'unsupported']);
const { validateEnvironmentLock } = referenceEnvironment;

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
  if (result.status !== 0 || result.signal !== null ||
      (result.error && result.error.code !== 'EPERM')) {
    const detail = `${result.stdout ?? ''}${result.stderr ?? ''}${result.error?.message ?? ''}`.trim();
    fail(`${command} ${argv.join(' ')} failed: ${detail}`);
  }
}

function parseArguments(argv) {
  const result = {
    why3Root: resolve(PROJECT_ROOT, '..', 'why3'),
    why3Archive: null,
    quick: false,
  };
  let explicitRoot = false;
  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index];
    if (argument === '--quick') result.quick = true;
    else if (argument === '--why3-root' || argument === '--why3-archive') {
      const value = argv[index + 1];
      if (!value) fail(`${argument} requires a path`);
      if (argument === '--why3-root') {
        result.why3Root = resolve(value);
        explicitRoot = true;
      }
      else result.why3Archive = resolve(value);
      index += 1;
    } else fail(`unknown argument ${argument}`);
  }
  if (explicitRoot && result.why3Archive !== null) {
    fail('--why3-root and --why3-archive are mutually exclusive');
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
  const adapterPaths = manifest.ocamlReferenceAdapters.map(entry => entry.path);
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
  for (const entry of manifest.ocamlReferenceAdapters) {
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
  for (const absolutePath of enumerateFiles(join(PROJECT_ROOT, 'tools', 'why3_reference'), '.ml')) {
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
  const envelopeSchema = readJson('tools/contracts/schema/reference-goal-envelope-v1.schema.json');
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
    schema.recordFieldOrder.ReferenceGoalEnvelope,
    'reference envelope property order',
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

export function checkProfiles() {
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

export function checkReferenceEnvironmentLock() {
  const lock = validateEnvironmentLock(
    readJson('tools/contracts/reference-environment-lock-v1.json'),
  );
  checkNoPlaceholder(lock);
  const driver = readJson('tools/contracts/driver-closure-v1.json');
  assertEqual(
    {
      version: lock.why3.version,
      commit: lock.why3.commit,
      tree: lock.why3.tree,
      archive: {
        url: lock.why3.archive.url,
        sha256: lock.why3.archive.sha256,
      },
    },
    {
      version: driver.why3.version,
      commit: driver.why3.commit,
      tree: driver.why3.tree,
      archive: driver.why3.sourceArchive,
    },
    'reference environment Why3 identity',
  );
  const dockerfile = readFileSync(projectFile('infra/reference-env/Dockerfile'), 'utf8');
  assert(
    dockerfile.includes(
      `FROM ${lock.ocaml.base.repository}:${lock.ocaml.base.tag}@${lock.ocaml.base.digest}`,
    ),
    'reference Dockerfile base does not match the environment lock',
  );
  for (const forbidden of [
    'COPY ',
    'driver-trace.patch',
    'runtime-dependencies-v1.json',
    'tools/contracts',
    'baselines/',
  ]) {
    assert(!dockerfile.includes(forbidden), `reference Dockerfile contains ${forbidden}`);
  }
  return lock;
}

export function checkReferenceRollout() {
  const imageWorkflow = readFileSync(
    projectFile('.github/workflows/why3-image.yml'),
    'utf8',
  );
  assert(
    imageWorkflow.includes('context: infra/reference-env'),
    'reference image workflow does not use the isolated build context',
  );
  assert(
    imageWorkflow.includes('tools/why3_reference/generate_environment_lock_candidate.mjs'),
    'reference image workflow does not emit an environment lock candidate',
  );

  const baselineWorkflow = readFileSync(
    projectFile('.github/workflows/update-baselines.yml'),
    'utf8',
  );
  for (const command of [
    'node tools/run.mjs baselines candidate',
    'node tools/run.mjs baselines promote',
  ]) {
    assert(
      baselineWorkflow.includes(command),
      `baseline update workflow is missing ${command}`,
    );
  }
  assert(
    readFileSync(projectFile('.github/workflows/check.yml'), 'utf8')
      .includes('node tools/run.mjs reference'),
    'ordinary CI must run the complete reference and baseline check',
  );
  for (const path of [
    '.github/workflows/check.yml',
    '.github/workflows/nightly-reference.yml',
    '.github/workflows/update-baselines.yml',
  ]) {
    const source = readFileSync(projectFile(path), 'utf8');
    assert(
      source.includes('reference-environment-lock-v1.json'),
      `${path} does not read the environment lock`,
    );
    assert(
      source.includes('needs.environment.outputs.image'),
      `${path} does not route the environment job output into container.image`,
    );
    assert(
      !/sha256:[0-9a-f]{64}/u.test(source),
      `${path} embeds an environment digest outside the lock`,
    );
  }
}

function runGeneratedChecks(arguments_) {
  const scripts = [
    ['tools/why3_reference/generate_feature_manifest.mjs', '--check', 'tools/contracts/features-v1.json'],
    [
      'tools/why3_reference/generate_canonical_vectors.mjs',
      'schema',
      '--check',
      'tools/contracts/canonical-vectors-v1.json',
    ],
    ['tools/why3_reference/generate_semantic_profile.mjs', '--check', 'tools/contracts/semantic-profile-v1.json'],
  ];
  if (!arguments_.quick) {
    const driverSource = arguments_.why3Archive === null
      ? ['--why3-root', arguments_.why3Root]
      : ['--why3-archive', arguments_.why3Archive];
    scripts.push([
      'tools/why3_reference/generate_pr_corpus.mjs',
      ...driverSource,
      '--check',
      'tools/contracts/pr-corpus-v1.json',
    ]);
    scripts.push([
      'tools/why3_reference/export_driver_inventory.mjs',
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
  checkProfiles();
  const environmentLock = checkReferenceEnvironmentLock();
  checkReferenceRollout();
  runGeneratedChecks(arguments_);
  return { environmentLock };
}

const isMain = process.argv[1] !== undefined &&
  pathToFileURL(resolve(process.argv[1])).href === import.meta.url;
if (isMain) {
  try {
    checkAll(parseArguments(process.argv.slice(2)));
    process.stdout.write('PR-00 project contracts and reference environment lock verified\n');
  } catch (error) {
    process.stderr.write(`check_pr00_contracts: ${error.message}\n`);
    process.exitCode = 1;
  }
}
