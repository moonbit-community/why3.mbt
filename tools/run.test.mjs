// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  parseGoldensOptions,
  parseOracleOptions,
  renderGoldenLock,
} from './run.mjs';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');

test('oracle task options keep source and lock policy explicit', () => {
  const options = parseOracleOptions(
    ['--why3-archive', 'reference.tar.gz', '--require-toolchain-lock'],
    { locks: true },
  );
  assert.match(options.why3Archive, /reference\.tar\.gz$/u);
  assert.equal(options.why3Root, null);
  assert.equal(options.requireToolchainLock, true);
  assert.equal(options.skipToolchainLock, false);
  assert.throws(
    () => parseOracleOptions(
      ['--why3-root', 'why3', '--why3-archive', 'why3.tar.gz'],
      { locks: true },
    ),
    /mutually exclusive/u,
  );
});

test('golden candidate combines structural, result, and optional lock outputs', () => {
  const options = parseGoldensOptions([
    'candidate',
    '--records',
    'records',
    '--result',
    'result.json',
    '--lock',
    'lock.json',
    '--compare',
  ]);
  assert.equal(options.mode, 'candidate');
  assert.match(options.records, /records$/u);
  assert.match(options.result, /result\.json$/u);
  assert.match(options.lock, /lock\.json$/u);
  assert.equal(options.compare, true);
});

test('golden modes reject partial or unsafe combinations', () => {
  assert.deepEqual(parseGoldensOptions(['check']), {
    mode: 'check',
    records: null,
    result: null,
    lock: null,
    compare: false,
  });
  assert.throws(
    () => parseGoldensOptions(['candidate', '--records', 'records']),
    /requires --records and --result/u,
  );
  assert.throws(
    () => parseGoldensOptions([
      'promote',
      '--records',
      'records',
      '--result',
      'result.json',
      '--compare',
    ]),
    /valid only for goldens candidate/u,
  );
});

test('merged golden-lock synchronizer reproduces the checked-in lock', () => {
  const goldenRoot = join(PROJECT_ROOT, 'tools', 'why3_oracle', 'goldens', 'pr-v1');
  const lockPath = join(PROJECT_ROOT, 'tools', 'contracts', 'toolchain-lock.json');
  assert.equal(
    readFileSync(lockPath, 'utf8'),
    renderGoldenLock(
      readFileSync(join(goldenRoot, 'manifest.json')),
      readFileSync(join(goldenRoot, 'prover-result.json')),
    ),
  );
});
