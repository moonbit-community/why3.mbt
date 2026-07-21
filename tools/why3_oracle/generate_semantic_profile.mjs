// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..');
const ARTIFACTS = [
  ['canonical-schema-v2', 'tools/contracts/canonical-schema-v2.json'],
  ['canonical-record-v2-json-schema', 'tools/contracts/schema/canonical-record-v2.schema.json'],
  ['driver-closure-v1', 'tools/contracts/driver-closure-v1.json'],
  ['features-v1', 'tools/contracts/features-v1.json'],
  ['transform-profile-v1', 'tools/contracts/transform-profile-v1.json'],
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
  if (argv.length === 0) return { mode: 'stdout', path: null };
  if (argv.length !== 2 || !['--output', '--check'].includes(argv[0])) {
    fail('usage: generate_semantic_profile.mjs [--output PATH | --check PATH]');
  }
  return { mode: argv[0].slice(2), path: resolve(argv[1]) };
}

function buildProfile() {
  const artifacts = ARTIFACTS.map(([id, path]) => ({
    id,
    path,
    sha256: sha256(readFileSync(join(PROJECT_ROOT, path))),
  }));
  return {
    schemaVersion: 1,
    profile: 'why3-1.7.2-z3-4.8.12-mvp-v1',
    why3Commit: '1343338d3bb1941c0d4f134283bb0790816113c4',
    canonicalSchemaVersion: 2,
    driverProfile: 'z3_487',
    policy: {
      portableOnly: true,
      excludesMachineEnvironmentAndAbsolutePaths: true,
      hashInput: 'compact JSON artifact array plus one LF',
      artifactOrder: 'the fixed order in this manifest',
    },
    artifacts,
    semanticProfileSha256: canonicalSha(artifacts),
  };
}

try {
  const arguments_ = parseArguments(process.argv.slice(2));
  const rendered = `${JSON.stringify(buildProfile(), null, 2)}\n`;
  if (arguments_.mode === 'output') {
    writeFileSync(arguments_.path, rendered);
  } else if (arguments_.mode === 'check') {
    if (readFileSync(arguments_.path, 'utf8') !== rendered) {
      fail(`${arguments_.path} does not match the generated semantic profile`);
    }
  } else {
    process.stdout.write(rendered);
  }
} catch (error) {
  process.stderr.write(`generate_semantic_profile: ${error.message}\n`);
  process.exitCode = 1;
}
