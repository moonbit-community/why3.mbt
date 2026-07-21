#!/usr/bin/env node
// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import referenceEnvironment from './reference_environment.cjs';

const {
  ENVIRONMENT_LOCK_PATH,
  sha256,
  validateEnvironmentLock,
  validateManifest,
} = referenceEnvironment;

function fail(message) {
  throw new Error(message);
}

function parseArguments(argv) {
  const result = { imageDigest: null, manifest: null, output: null };
  for (let index = 0; index < argv.length; index += 1) {
    const option = argv[index];
    if (!['--image-digest', '--manifest', '--output'].includes(option)) {
      fail(`unknown option ${option}`);
    }
    const value = argv[index + 1];
    if (!value || value.startsWith('--')) fail(`${option} requires a value`);
    if (option === '--image-digest') result.imageDigest = value;
    else if (option === '--manifest') result.manifest = resolve(value);
    else result.output = resolve(value);
    index += 1;
  }
  if (Object.values(result).some(value => value === null)) {
    fail('usage: generate_environment_lock_candidate.mjs --image-digest DIGEST --manifest PATH --output PATH');
  }
  return result;
}

export function renderCandidate(lock, imageDigest, manifestBytes) {
  const candidate = structuredClone(lock);
  candidate.image.digest = imageDigest;
  validateEnvironmentLock(candidate);
  if (sha256(manifestBytes) !== candidate.manifest.sha256) {
    fail('candidate image manifest hash differs from the environment lock');
  }
  validateManifest(JSON.parse(manifestBytes), candidate);
  return `${JSON.stringify(candidate, null, 2)}\n`;
}

function main() {
  const arguments_ = parseArguments(process.argv.slice(2));
  if (existsSync(arguments_.output)) fail(`candidate already exists: ${arguments_.output}`);
  const lock = validateEnvironmentLock(JSON.parse(readFileSync(ENVIRONMENT_LOCK_PATH, 'utf8')));
  const rendered = renderCandidate(
    lock,
    arguments_.imageDigest,
    readFileSync(arguments_.manifest),
  );
  writeFileSync(arguments_.output, rendered);
  process.stdout.write(`${arguments_.output}\n`);
}

const isMain = process.argv[1] !== undefined &&
  resolve(process.argv[1]) === fileURLToPath(import.meta.url);
if (isMain) {
  try {
    main();
  } catch (error) {
    process.stderr.write(`generate_environment_lock_candidate: ${error.message}\n`);
    process.exitCode = 1;
  }
}
