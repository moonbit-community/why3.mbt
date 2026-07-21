#!/usr/bin/env node
// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..');
const LOCK_PATH = join(PROJECT_ROOT, 'tools', 'contracts', 'toolchain-lock.json');
const CURRENT_MANIFEST = join(
  PROJECT_ROOT,
  'tools',
  'why3_oracle',
  'goldens',
  'pr-v1',
  'manifest.json',
);
const CURRENT_RESULT = join(
  PROJECT_ROOT,
  'tools',
  'why3_oracle',
  'goldens',
  'pr-v1',
  'prover-result.json',
);

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function parseArguments(argv) {
  if (argv.length === 0 || (argv.length === 1 && argv[0] === '--check')) {
    return {
      mode: 'check',
      manifest: CURRENT_MANIFEST,
      result: CURRENT_RESULT,
      output: LOCK_PATH,
    };
  }
  let mode = null;
  let manifest = null;
  let result = null;
  let output = null;
  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index];
    if (argument === '--candidate' || argument === '--promote') {
      if (mode !== null) fail('mode may be specified only once');
      mode = argument.slice(2);
      continue;
    }
    const value = argv[index + 1];
    if (value === undefined) fail(`${argument} requires a path`);
    if (argument === '--manifest') manifest = resolve(value);
    else if (argument === '--result') result = resolve(value);
    else if (argument === '--output') output = resolve(value);
    else fail(`unknown argument: ${argument}`);
    index += 1;
  }
  if (mode === null || manifest === null || result === null) {
    fail(
      'usage: sync_pr_golden_lock.mjs [--check | ' +
      '--candidate --manifest PATH --result PATH --output PATH | ' +
      '--promote --manifest PATH --result PATH]',
    );
  }
  if (mode === 'candidate' && output === null) fail('--candidate requires --output');
  if (mode === 'promote' && output !== null) fail('--promote writes only the repository lock');
  return { mode, manifest, result, output: output ?? LOCK_PATH };
}

function renderLock(manifestBytes, resultBytes) {
  const lock = JSON.parse(readFileSync(LOCK_PATH, 'utf8'));
  const updates = new Map([
    ['pr-golden-manifest-v1', sha256(manifestBytes)],
    ['pr-prover-result-v1', sha256(resultBytes)],
  ]);
  for (const artifact of lock.contracts.artifacts) {
    const digest = updates.get(artifact.id);
    if (digest !== undefined) {
      artifact.sha256 = digest;
      updates.delete(artifact.id);
    }
  }
  if (updates.size !== 0) {
    fail(`toolchain lock is missing golden artifact(s): ${[...updates.keys()]}`);
  }
  delete lock.lockSha256;
  lock.lockSha256 = sha256(`${JSON.stringify(lock)}\n`);
  return `${JSON.stringify(lock, null, 2)}\n`;
}

function main() {
  const arguments_ = parseArguments(process.argv.slice(2));
  const manifestBytes = readFileSync(arguments_.manifest);
  const resultBytes = readFileSync(arguments_.result);
  const rendered = renderLock(manifestBytes, resultBytes);
  if (arguments_.mode === 'check') {
    if (readFileSync(LOCK_PATH, 'utf8') !== rendered) {
      fail('repository toolchain lock does not bind the current PR goldens');
    }
    process.stdout.write('sync_pr_golden_lock: checked-in golden hashes exact\n');
  } else if (arguments_.mode === 'candidate') {
    if (existsSync(arguments_.output)) {
      fail(`candidate already exists: ${arguments_.output}`);
    }
    writeFileSync(arguments_.output, rendered);
    process.stdout.write(
      `${JSON.stringify({
        candidate: arguments_.output,
        sha256: sha256(rendered),
      }, null, 2)}\n`,
    );
  } else {
    writeFileSync(LOCK_PATH, rendered);
    process.stdout.write(
      `sync_pr_golden_lock: promoted golden hashes into ${LOCK_PATH}\n`,
    );
  }
}

try {
  main();
} catch (error) {
  process.stderr.write(`sync_pr_golden_lock: ${error.message}\n`);
  process.exitCode = 1;
}
