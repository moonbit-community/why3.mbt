// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..');
const IMAGE_REPOSITORY = 'ghcr.io/moonbit-community/why3.mbt-why3';
const SHA256_PATTERN = /^[0-9a-f]{64}$/u;
const DIGEST_PATTERN = /^sha256:[0-9a-f]{64}$/u;
const COMMIT_PATTERN = /^[0-9a-f]{40}$/u;
const CONTRACT_ARTIFACTS = [
  ['canonical-schema-v2', 'tools/contracts/canonical-schema-v2.json'],
  ['canonical-vectors-v1', 'tools/contracts/canonical-vectors-v1.json'],
  ['canonical-record-v2-json-schema', 'tools/contracts/schema/canonical-record-v2.schema.json'],
  ['driver-closure-v1', 'tools/contracts/driver-closure-v1.json'],
  ['features-v1', 'tools/contracts/features-v1.json'],
  ['moon-dependencies-v1', 'tools/contracts/moon-dependencies-v1.json'],
  ['oracle-goal-envelope-v1-json-schema', 'tools/contracts/schema/oracle-goal-envelope-v1.schema.json'],
  ['pr-corpus-v1', 'tools/contracts/pr-corpus-v1.json'],
  ['runner-vectors-v1', 'tools/contracts/runner-vectors-v1.json'],
  ['semantic-profile-v1', 'tools/contracts/semantic-profile-v1.json'],
  ['toolchain-inputs-v1', 'tools/contracts/toolchain-inputs-v1.json'],
  ['toolchain-lock-v1-json-schema', 'tools/contracts/schema/toolchain-lock-v1.schema.json'],
  ['transform-profile-v1', 'tools/contracts/transform-profile-v1.json'],
  ['translated-files-v1', 'tools/contracts/translated-files-v1.json'],
  ['trusted-snapshot-schema-v1', 'tools/contracts/trusted-snapshot-schema-v1.json'],
];

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function canonicalSha(value) {
  return sha256(`${JSON.stringify(value)}\n`);
}

function parseArguments(argv) {
  const result = { report: null, imageDigest: null, buildCommit: null, mode: 'stdout', path: null };
  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index];
    const value = argv[index + 1];
    if (!value) fail(`${argument} requires a value`);
    if (argument === '--report') result.report = resolve(value);
    else if (argument === '--image-digest') result.imageDigest = value;
    else if (argument === '--build-recipe-commit') result.buildCommit = value;
    else if (argument === '--output' || argument === '--check') {
      if (result.mode !== 'stdout') fail('--output and --check are mutually exclusive');
      result.mode = argument.slice(2);
      result.path = resolve(value);
    } else fail(`unknown argument ${argument}`);
    index += 1;
  }
  if (result.report === null || result.imageDigest === null || result.buildCommit === null) {
    fail('--report, --image-digest, and --build-recipe-commit are required');
  }
  if (!DIGEST_PATTERN.test(result.imageDigest)) fail('invalid OCI image digest');
  if (!COMMIT_PATTERN.test(result.buildCommit)) fail('invalid build recipe commit');
  return result;
}

function readProject(path) {
  return readFileSync(join(PROJECT_ROOT, path));
}

function buildLock(arguments_) {
  const inputs = JSON.parse(readProject('tools/contracts/toolchain-inputs-v1.json'));
  const report = JSON.parse(readFileSync(arguments_.report, 'utf8'));
  if (report.schemaVersion !== 1) fail('unsupported toolchain report schema');
  if (report.platform.oci !== 'linux/amd64') fail('toolchain report is not linux/amd64');
  if (JSON.stringify(report.platform) !== JSON.stringify(inputs.oraclePlatform)) {
    fail('toolchain report platform drift');
  }
  if (report.toolchainInputs.fileSha256 !== sha256(readProject('tools/contracts/toolchain-inputs-v1.json'))) {
    fail('toolchain report used different toolchain input bytes');
  }
  if (report.toolchainInputs.contentSha256 !== inputs.toolchainInputsSha256) {
    fail('toolchain report used different toolchain inputs');
  }
  if (report.z3.version !== inputs.z3.version ||
      report.z3.versionOutput !== `Z3 version ${inputs.z3.version} - 64 bit` ||
      JSON.stringify(report.z3.executable) !== JSON.stringify(inputs.z3.executable)) {
    fail('Z3 executable drift');
  }
  if (report.why3.version !== inputs.why3.version ||
      report.why3.versionOutput !== `Why3 platform, version ${inputs.why3.version}` ||
      report.why3.commit !== inputs.why3.commit ||
      report.why3.shapeVersion !== inputs.why3.shapeVersion ||
      report.why3.executable.path !== inputs.why3.executablePath ||
      !SHA256_PATTERN.test(report.why3.executable.sha256) ||
      report.why3.datadir.path !== inputs.why3.datadirPath ||
      !SHA256_PATTERN.test(report.why3.datadir.treeSha256) ||
      report.why3.driverClosureSha256 !== inputs.why3.driverClosureSha256 ||
      report.why3.datadir.stdlibTreeSha256 !== inputs.why3.stdlibTreeSha256 ||
      report.why3.proverDetectionSha256 !== inputs.why3.proverDetectionSha256 ||
      report.why3.sourceArchiveSha256 !== inputs.why3.referenceArchive.sha256) {
    fail('Why3 installed data drift');
  }
  if (JSON.stringify(report.environment) !== JSON.stringify({ LC_ALL: 'C', LANG: 'C', TZ: 'UTC' })) {
    fail('toolchain report environment drift');
  }
  const artifacts = CONTRACT_ARTIFACTS.map(([id, path]) => ({
    id,
    path,
    sha256: sha256(readProject(path)),
  }));
  const semanticProfile = JSON.parse(readProject('tools/contracts/semantic-profile-v1.json'));
  const corpusBytes = readProject('tools/contracts/pr-corpus-v1.json');
  const value = {
    schemaVersion: 1,
    profile: 'why3-1.7.2-z3-4.8.12-mvp-v1',
    platform: inputs.oraclePlatform,
    image: {
      repository: IMAGE_REPOSITORY,
      digest: arguments_.imageDigest,
      reference: `${IMAGE_REPOSITORY}@${arguments_.imageDigest}`,
    },
    buildRecipe: {
      commit: arguments_.buildCommit,
      path: inputs.buildRecipe.path,
      sha256: inputs.buildRecipe.sha256,
      frontendImage: inputs.buildRecipe.frontendImage,
      baseImage: inputs.baseImage,
      sourceArchiveKeptInImage: inputs.buildRecipe.sourceArchiveKeptInImage,
    },
    githubActions: inputs.githubActions,
    why3: {
      ...report.why3,
      semanticSnapshotSha256: inputs.why3.semanticSnapshotSha256,
      referenceArchive: inputs.why3.referenceArchive,
      opamRecipe: inputs.why3.opamRecipe,
    },
    z3: { ...report.z3, commit: inputs.z3.commit, archive: inputs.z3.archive },
    contracts: {
      semanticProfileSha256: semanticProfile.semanticProfileSha256,
      prCorpusSha256: sha256(corpusBytes),
      artifacts,
    },
    environment: inputs.environment,
  };
  for (const artifact of artifacts) {
    if (!SHA256_PATTERN.test(artifact.sha256)) fail(`invalid artifact hash ${artifact.id}`);
  }
  return { ...value, lockSha256: canonicalSha(value) };
}

try {
  const arguments_ = parseArguments(process.argv.slice(2));
  const rendered = `${JSON.stringify(buildLock(arguments_), null, 2)}\n`;
  if (arguments_.mode === 'output') {
    writeFileSync(arguments_.path, rendered);
  } else if (arguments_.mode === 'check') {
    if (readFileSync(arguments_.path, 'utf8') !== rendered) {
      fail(`${arguments_.path} does not match the inspected toolchain`);
    }
  } else {
    process.stdout.write(rendered);
  }
} catch (error) {
  process.stderr.write(`generate_toolchain_lock: ${error.message}\n`);
  process.exitCode = 1;
}
