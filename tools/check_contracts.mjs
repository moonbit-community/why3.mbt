// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import referenceEnvironment from './why3_reference/reference_environment.cjs';
import {
  validateUpstreamCorpusContract,
} from './why3_reference/upstream_corpus.mjs';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const WHY3_COMMIT = '1343338d3bb1941c0d4f134283bb0790816113c4';
const LICENSE_SHA256 = '4b9eb976aecd9de79a0aff3a3bfea7134e8f4874d36b0783110c13ba837a8858';
const TARGET_LANES = new Set(['exact', 'reject']);
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

export function checkLicenseAndAttribution() {
  assertEqual(sha256(readFileSync(projectFile('LICENSE'))), LICENSE_SHA256, 'LICENSE hash');
}

export function checkCanonicalContracts() {
  const schemaV3 = readJson('tools/contracts/canonical-schema-v3.json');
  const recordSchemaV3 = readJson(
    'tools/contracts/schema/canonical-record-v3.schema.json',
  );
  const diagnosticSchema = readJson(
    'tools/contracts/schema/diagnostic-record-v1.schema.json',
  );
  const diagnosticContract = readJson('tools/contracts/diagnostics-v1.json');
  assertEqual(
    Object.keys(diagnosticSchema.oneOf[0].properties),
    diagnosticContract.fieldOrder.accepted,
    'accepted diagnostic field order',
  );
  assertEqual(
    Object.keys(diagnosticSchema.oneOf[1].properties),
    diagnosticContract.fieldOrder.rejected,
    'rejected diagnostic field order',
  );
  assertEqual(
    diagnosticContract.recordSchema.sha256,
    sha256(readFileSync(projectFile(diagnosticContract.recordSchema.path))),
    'diagnostic record schema hash',
  );
  assertEqual(
    diagnosticContract.targetFeatures.sha256,
    sha256(readFileSync(projectFile(diagnosticContract.targetFeatures.path))),
    'diagnostic target feature hash',
  );
  assertEqual(
    diagnosticContract.referenceInstrumentation.sha256,
    sha256(readFileSync(projectFile(
      diagnosticContract.referenceInstrumentation.path,
    ))),
    'diagnostic instrumentation hash',
  );
  assertEqual(
    diagnosticContract.activeParserMappingsSha256,
    canonicalSha(diagnosticContract.activeParserMappings),
    'diagnostic parser mapping hash',
  );
  const {
    diagnosticContractSha256,
    ...diagnosticContractBody
  } = diagnosticContract;
  assertEqual(
    diagnosticContractSha256,
    canonicalSha(diagnosticContractBody),
    'diagnostic contract hash',
  );
  assertEqual(
    diagnosticContract.parserCorpus.locatedRejects +
      diagnosticContract.parserCorpus.unlocatedRejects,
    diagnosticContract.parserCorpus.totalRejects,
    'diagnostic parser location counts',
  );
  assertEqual(
    Object.values(diagnosticContract.parserCorpus.categoryCounts)
      .reduce((sum, count) => sum + count, 0),
    diagnosticContract.parserCorpus.totalRejects,
    'diagnostic parser category counts',
  );

  const targetFeatures = readJson('tools/contracts/features-v2.json');
  assertEqual(schemaV3.schemaVersion, 3, 'canonical v3 schema version');
  assertEqual(schemaV3.recordVersion, 3, 'canonical v3 record version');
  assertEqual(
    schemaV3.status,
    'active',
    'canonical v3 status',
  );
  assertEqual(
    Object.keys(recordSchemaV3.properties),
    schemaV3.recordFieldOrder.CanonicalRecordV3,
    'canonical v3 record property order',
  );
  assertEqual(
    schemaV3.inputs.targetFeatures.sha256,
    sha256(readFileSync(projectFile(schemaV3.inputs.targetFeatures.path))),
    'canonical v3 target feature hash',
  );
  assertEqual(
    schemaV3.inputs.targetFeatures.variantInventorySha256,
    targetFeatures.variantInventorySha256,
    'canonical v3 variant inventory binding',
  );
  assertEqual(
    schemaV3.inputs.targetFeatures.recordInventorySha256,
    targetFeatures.recordInventorySha256,
    'canonical v3 record inventory binding',
  );
  assertEqual(
    schemaV3.inputs.targetFeatures.opaqueProjectionInventorySha256,
    targetFeatures.opaqueProjectionInventorySha256,
    'canonical v3 opaque projection inventory binding',
  );
  assertEqual(
    schemaV3.inputs.structuredDiagnostics.sha256,
    sha256(readFileSync(projectFile(
      schemaV3.inputs.structuredDiagnostics.path,
    ))),
    'canonical v3 diagnostic contract hash',
  );
  assertEqual(
    schemaV3.inputs.structuredDiagnostics.diagnosticContractSha256,
    diagnosticContract.diagnosticContractSha256,
    'canonical v3 structured diagnostic binding',
  );
  assertEqual(
    schemaV3.inputs.recordSchema.sha256,
    sha256(readFileSync(projectFile(schemaV3.inputs.recordSchema.path))),
    'canonical v3 record schema hash',
  );
  const expectedVariantCoverage = targetFeatures.variants.map(entry => ({
    featureId: entry.id,
    canonicalTag: entry.id,
    fieldOrder: ['payload'],
    payloadEncoding:
      'Unit for nullary constructors; otherwise one value or Product in OCaml source tuple order',
  }));
  const expectedRecordCoverage = targetFeatures.records.map(entry => ({
    featureId: entry.id,
    canonicalTag: entry.id,
    fieldOrder: entry.canonicalV3Fields,
    excluded: entry.excludedFromCanonicalV3,
  }));
  assertEqual(
    schemaV3.featureCoverage,
    {
      variants: expectedVariantCoverage,
      records: expectedRecordCoverage,
      opaqueProjections: targetFeatures.opaqueProjections,
    },
    'canonical v3 complete feature coverage',
  );
  assertEqual(
    schemaV3.featureCoverageSha256,
    canonicalSha(schemaV3.featureCoverage),
    'canonical v3 feature coverage hash',
  );
  const nodeTags = Object.keys(schemaV3.nodeFieldOrder);
  assertEqual(
    nodeTags,
    [...nodeTags].sort(compareUtf8),
    'canonical v3 node tag order',
  );
  assertEqual(
    new Set(nodeTags).size,
    nodeTags.length,
    'canonical v3 node tag uniqueness',
  );
  for (const entry of expectedVariantCoverage) {
    assertEqual(
      schemaV3.nodeFieldOrder[entry.canonicalTag],
      entry.fieldOrder,
      `${entry.featureId} canonical v3 node fields`,
    );
  }
  for (const entry of expectedRecordCoverage) {
    assertEqual(
      schemaV3.nodeFieldOrder[entry.canonicalTag],
      entry.fieldOrder,
      `${entry.featureId} canonical v3 node fields`,
    );
  }
  const expectedV3Counts = {
    baseNodes:
      nodeTags.length -
      targetFeatures.variants.length -
      targetFeatures.records.length,
    definitionKinds: schemaV3.identity.definitionKinds.length,
    variantTags: targetFeatures.variants.length,
    recordTags: targetFeatures.records.length,
    opaqueProjections: targetFeatures.opaqueProjections.length,
    nodeTags: nodeTags.length,
    excludedRawFields: targetFeatures.records.reduce(
      (count, entry) =>
        count + Object.keys(entry.excludedFromCanonicalV3).length,
      0,
    ),
  };
  assertEqual(schemaV3.counts, expectedV3Counts, 'canonical v3 counts');
  assertEqual(
    new Set(schemaV3.identity.definitionKinds).size,
    schemaV3.identity.definitionKinds.length,
    'canonical v3 definition kind uniqueness',
  );
  const {
    canonicalSchemaSha256,
    ...schemaV3Body
  } = schemaV3;
  assertEqual(
    canonicalSchemaSha256,
    canonicalSha(schemaV3Body),
    'canonical v3 schema hash',
  );

  const vectors = readJson('tools/contracts/canonical-vectors-v1.json');
  assertEqual(
    vectors.canonicalSchemaVersion,
    schemaV3.schemaVersion,
    'vector canonical schema version',
  );
  const names = new Set();
  for (const vector of vectors.vectors) {
    assert(typeof vector.name === 'string' && !names.has(vector.name), 'canonical vector names must be unique');
    names.add(vector.name);
    const bytes = `${JSON.stringify(vector.canonical)}\n`;
    assertEqual(vector.canonicalBytesUtf8, bytes, `${vector.name} canonical bytes`);
    assertEqual(vector.canonicalSha256, sha256(bytes), `${vector.name} canonical hash`);
  }
}

export function checkDriverContract() {
  const driver = readJson('tools/contracts/driver-closure-v1.json');
  assertEqual(driver.why3.commit, WHY3_COMMIT, 'driver Why3 commit');
  assertEqual(driver.why3.shapeVersion, 6, 'Why3 shape version');
  const { sha256: recordedDriverSha, ...driverContent } = driver.driver;
  assertEqual(recordedDriverSha, canonicalSha(driverContent), 'driver closure hash');
  assertEqual(
    driver.sourceCatalog.stdlibTree.sha256,
    canonicalSha(driver.sourceCatalog.stdlibTree.entries),
    'stdlib tree hash',
  );
  assertEqual(
    driver.sourceCatalog.theoryRoots,
    driver.driver.theoryRoots,
    'source catalog theory roots',
  );
  assertEqual(driver.sourceCatalog.sha256, canonicalSha({
    theoryRoots: driver.sourceCatalog.theoryRoots,
    stdlibTreeSha256: driver.sourceCatalog.stdlibTree.sha256,
  }), 'source catalog hash');
}

export function checkFeaturesAndCorpus() {
  const projectAst = readJson('tools/contracts/parser-ast-inventory-v1.json');
  const targetFeatures = readJson('tools/contracts/features-v2.json');
  const corpus = readJson('tools/contracts/pr-corpus-v1.json');
  validateUpstreamCorpusContract(
    readJson('tools/contracts/upstream-corpus-v1.json'),
  );
  assertEqual(projectAst.why3Commit, WHY3_COMMIT, 'project AST Why3 commit');
  assertEqual(
    projectAst.contract,
    'why3mbt-project-parser-ast-inventory-v1',
    'project AST contract',
  );
  assertEqual(
    projectAst.scope.upstreamPtreeInventory,
    false,
    'project AST must not claim to be the upstream Ptree inventory',
  );
  assertEqual(
    projectAst.policy.lanesAssignedHere,
    false,
    'project AST inventory must not assign support lanes',
  );
  const projectVariantIds = projectAst.variants.map(item => item.id);
  assertEqual(
    projectVariantIds,
    [...projectVariantIds].sort(compareUtf8),
    'project AST variant order',
  );
  assertEqual(
    new Set(projectVariantIds).size,
    projectVariantIds.length,
    'project AST variants must be unique',
  );
  assertEqual(
    projectAst.counts,
    {
      sourceFiles: projectAst.sourceInventory.length,
      enums: new Set(projectAst.variants.map(item => item.enum)).size,
      variants: projectAst.variants.length,
    },
    'project AST counts',
  );
  assertEqual(
    projectAst.sourceInventorySha256,
    canonicalSha(projectAst.sourceInventory),
    'project AST source inventory hash',
  );
  assertEqual(
    projectAst.variantInventorySha256,
    canonicalSha(projectAst.variants),
    'project AST variant inventory hash',
  );

  assertEqual(targetFeatures.schemaVersion, 2, 'target feature schema version');
  assertEqual(
    targetFeatures.policy.targetLanes,
    ['exact', 'reject'],
    'target feature lanes',
  );
  assertEqual(
    targetFeatures.policy.intentionalDivergenceCount,
    0,
    'target intentional divergence count',
  );
  assertEqual(
    targetFeatures.projectParserAstInventory.sha256,
    sha256(readFileSync(projectFile(
      targetFeatures.projectParserAstInventory.path,
    ))),
    'target feature project AST binding',
  );
  assertEqual(
    targetFeatures.projectParserAstInventory.enumCount,
    projectAst.counts.enums,
    'target feature project AST enum count',
  );
  assertEqual(
    targetFeatures.projectParserAstInventory.variantCount,
    projectAst.counts.variants,
    'target feature project AST variant count',
  );
  const targetVariantIds = targetFeatures.variants.map(entry => entry.id);
  assertEqual(
    targetVariantIds,
    [...targetVariantIds].sort(compareUtf8),
    'target feature variant order',
  );
  assertEqual(
    new Set(targetVariantIds).size,
    targetVariantIds.length,
    'target feature variant uniqueness',
  );
  assert(
    targetFeatures.variants.every(entry => entry.targetLane === 'exact'),
    'every official target constructor must be exact',
  );
  assertEqual(
    targetFeatures.variantInventorySha256,
    canonicalSha(targetFeatures.variants),
    'target feature variant hash',
  );
  const targetRecordIds = targetFeatures.records.map(entry => entry.id);
  assertEqual(
    targetRecordIds,
    [...targetRecordIds].sort(compareUtf8),
    'target feature record order',
  );
  assertEqual(
    new Set(targetRecordIds).size,
    targetRecordIds.length,
    'target feature record uniqueness',
  );
  for (const record of targetFeatures.records) {
    assertEqual(
      [
        ...record.canonicalV3Fields,
        ...Object.keys(record.excludedFromCanonicalV3),
      ].sort(compareUtf8),
      [...record.rawFields].sort(compareUtf8),
      `${record.id} target canonical field partition`,
    );
  }
  assertEqual(
    targetFeatures.recordInventorySha256,
    canonicalSha(targetFeatures.records),
    'target feature record hash',
  );
  assertEqual(
    targetFeatures.sourceInventorySha256,
    canonicalSha(targetFeatures.sourceInventory),
    'target feature source hash',
  );
  assertEqual(
    targetFeatures.opaqueProjectionInventorySha256,
    canonicalSha(targetFeatures.opaqueProjections),
    'target feature opaque projection hash',
  );
  assertEqual(
    targetFeatures.fullFileGrammar.envelopePatch.sha256,
    sha256(readFileSync(projectFile(
      targetFeatures.fullFileGrammar.envelopePatch.path,
    ))),
    'target feature full-file patch binding',
  );
  assertEqual(
    targetFeatures.counts,
    {
      variantFamilies: new Set(targetFeatures.variants.map(entry =>
        `${entry.owner}.${entry.type}`)).size,
      variants: targetFeatures.variants.length,
      recordFamilies: targetFeatures.records.length,
      opaqueProjections: targetFeatures.opaqueProjections.length,
      canonicalV3Fields: targetFeatures.records.reduce(
        (count, entry) => count + entry.canonicalV3Fields.length,
        0,
      ),
      excludedRawFields: targetFeatures.records.reduce(
        (count, entry) =>
          count + Object.keys(entry.excludedFromCanonicalV3).length,
        0,
      ),
    },
    'target feature counts',
  );
  const ids = corpus.entries.map(entry => entry.id);
  assertEqual(ids, [...ids].sort(compareUtf8), 'corpus entry order');
  assertEqual(new Set(ids).size, ids.length, 'corpus ids must be unique');
  assertEqual(corpus.entriesSha256, canonicalSha(corpus.entries), 'corpus entry hash');
  assertEqual(corpus.fixtureGroupsSha256, canonicalSha(corpus.fixtureGroups), 'fixture group hash');
  assertEqual(
    corpus.contractHashes.targetFeaturesV2Sha256,
    sha256(readFileSync(projectFile('tools/contracts/features-v2.json'))),
    'corpus target feature binding',
  );
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
  for (const entry of corpus.entries) {
    assert(TARGET_LANES.has(entry.expected.lane), `${entry.id} has invalid lane`);
    assert(Array.isArray(entry.featureTags) && entry.featureTags.length > 0, `${entry.id} has no feature tags`);
    assert(Array.isArray(entry.units) && Array.isArray(entry.goalInventory), `${entry.id} has no explicit inventory`);
    assert(!/[?*\[\]]/u.test(entry.source.path), `${entry.id} source path contains a glob`);
    if (entry.id === 'contract.canonical-vectors') {
      assert(Array.isArray(entry.inventory), `${entry.id} inventory is not an array`);
      assert(entry.inventory.every(item => item !== null), `${entry.id} contains a null vector id`);
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
  const semanticV3 = readJson('tools/contracts/semantic-profile-v3.json');
  assertEqual(semanticV3.profileVersion, 3, 'semantic v3 profile version');
  assertEqual(semanticV3.why3Commit, WHY3_COMMIT, 'semantic v3 Why3 commit');
  assertEqual(
    semanticV3.canonicalSchemaVersion,
    3,
    'semantic v3 canonical schema version',
  );
  assertEqual(
    semanticV3.diagnosticSchemaVersion,
    1,
    'semantic v3 diagnostic schema version',
  );
  assertEqual(semanticV3.status, 'active', 'semantic v3 status');
  assertEqual(
    semanticV3.policy.canonicalV3IsOnlyCanonicalRecord,
    true,
    'semantic v3 exclusive canonical policy',
  );
  const semanticV3ArtifactIds = [
    'canonical-schema-v3',
    'canonical-record-v3-json-schema',
    'diagnostic-record-v1-json-schema',
    'diagnostics-v1',
    'features-v2',
    'driver-closure-v1',
    'transform-profile-v1',
    'z3-static-profile-v1',
  ];
  assertEqual(
    semanticV3.artifacts.map(artifact => artifact.id),
    semanticV3ArtifactIds,
    'semantic v3 artifact order',
  );
  for (const artifact of semanticV3.artifacts) {
    assertEqual(
      artifact.sha256,
      sha256(readFileSync(projectFile(artifact.path))),
      `${artifact.id} v3 artifact hash`,
    );
  }
  const {
    semanticProfileSha256: semanticV3Hash,
    ...semanticV3Body
  } = semanticV3;
  assertEqual(
    semanticV3Hash,
    canonicalSha(semanticV3Body),
    'semantic v3 profile hash',
  );
  const diagnostics = readJson('tools/contracts/diagnostics-v1.json');
  const moonCanonicalRecord = readFileSync(
    projectFile('canonical/record.mbt'),
    'utf8',
  );
  for (const [label, digest] of [
    ['semantic profile', semanticV3Hash],
    ['diagnostic contract', diagnostics.diagnosticContractSha256],
  ]) {
    assert(
      moonCanonicalRecord.includes(`b"${digest}"`),
      `MoonBit canonical record has stale ${label} hash`,
    );
  }
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
  for (const dependency of [
    'ppx_deriving.5.2.1',
    'ppx_sexp_conv.v0.15.1',
    'sexplib.v0.15.1',
  ]) {
    assert(
      dockerfile.includes(dependency),
      `reference Dockerfile is missing pinned S-expression dependency ${dependency}`,
    );
  }
  for (const requirement of [
    '--enable-sexp',
    'pp --output=sexp',
    'test -s "$sexp_output"',
  ]) {
    assert(
      dockerfile.includes(requirement),
      `reference Dockerfile is missing S-expression requirement ${requirement}`,
    );
  }
  for (const forbidden of [
    'COPY ',
    'driver-trace.patch',
    'full-mlw-export.patch',
    'runtime-dependencies-v1.json',
    'tools/contracts',
    'baselines/',
  ]) {
    assert(!dockerfile.includes(forbidden), `reference Dockerfile contains ${forbidden}`);
  }
  return lock;
}

function runGeneratedChecks(arguments_) {
  const scripts = [
    [
      'tools/why3_reference/generate_parser_ast_inventory.mjs',
      '--check',
      'tools/contracts/parser-ast-inventory-v1.json',
    ],
    [
      'tools/why3_reference/generate_canonical_vectors.mjs',
      'schema',
      '--check',
      'tools/contracts/canonical-vectors-v1.json',
    ],
    [
      'tools/why3_reference/generate_diagnostic_contract.mjs',
      '--check',
      'tools/contracts/diagnostics-v1.json',
    ],
    [
      'tools/why3_reference/generate_canonical_schema_v3.mjs',
      '--check',
      'tools/contracts/canonical-schema-v3.json',
    ],
    [
      'tools/why3_reference/generate_semantic_profile_v3.mjs',
      '--check',
      'tools/contracts/semantic-profile-v3.json',
    ],
    [
      'tools/why3_reference/generate_canonical_v3_profile_ml.mjs',
      '--check',
      'tools/why3_reference/canonical_v3_profile.ml',
    ],
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
      'tools/why3_reference/generate_target_feature_contract.mjs',
      ...driverSource,
      '--check',
      'tools/contracts/features-v2.json',
    ]);
    scripts.push([
      'tools/why3_reference/export_driver_inventory.mjs',
      ...driverSource,
      '--check',
      'tools/contracts/driver-closure-v1.json',
    ]);
    scripts.push([
      'tools/why3_reference/check_full_whyml_reference.mjs',
      ...driverSource,
    ]);
    scripts.push([
      'tools/why3_reference/generate_upstream_corpus.mjs',
      ...driverSource,
      '--check',
      'tools/contracts/upstream-corpus-v1.json',
    ]);
  }
  for (const [script, ...argv] of scripts) runChecked(process.execPath, [script, ...argv]);
}

export function checkAll(arguments_) {
  checkLicenseAndAttribution();
  checkCanonicalContracts();
  checkDriverContract();
  checkFeaturesAndCorpus();
  checkProfiles();
  const environmentLock = checkReferenceEnvironmentLock();
  runGeneratedChecks(arguments_);
  return { environmentLock };
}

const isMain = process.argv[1] !== undefined &&
  pathToFileURL(resolve(process.argv[1])).href === import.meta.url;
if (isMain) {
  try {
    checkAll(parseArguments(process.argv.slice(2)));
    process.stdout.write('project contracts and reference environment lock verified\n');
  } catch (error) {
    process.stderr.write(`check_contracts: ${error.message}\n`);
    process.exitCode = 1;
  }
}
