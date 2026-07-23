// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  main,
  parseBaselinesOptions,
  parseReferenceOptions,
} from './run.mjs';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');

test('reference task options expose only explicit Why3 source selection', () => {
  const options = parseReferenceOptions([
    '--why3-archive',
    'reference.tar.gz',
  ]);
  assert.match(options.why3Archive, /reference\.tar\.gz$/u);
  assert.equal(options.why3Root, null);
  assert.throws(
    () => parseReferenceOptions(['--require-toolchain-lock']),
    /unknown option/u,
  );
  assert.throws(
    () => parseReferenceOptions(['--skip-toolchain-lock']),
    /unknown option/u,
  );
  assert.throws(
    () => parseReferenceOptions([
      '--why3-root', 'why3', '--why3-archive', 'why3.tar.gz',
    ]),
    /mutually exclusive/u,
  );
});

test('baseline candidate combines only structural and result outputs', () => {
  const options = parseBaselinesOptions([
    'candidate',
    '--records',
    'records',
    '--result',
    'result.json',
    '--compare',
  ]);
  assert.deepEqual(Object.keys(options).sort(), [
    'compare', 'mode', 'records', 'result',
  ]);
  assert.equal(options.mode, 'candidate');
  assert.match(options.records, /records$/u);
  assert.match(options.result, /result\.json$/u);
  assert.equal(options.compare, true);
  assert.throws(
    () => parseBaselinesOptions([
      'candidate', '--records', 'records', '--result', 'result.json',
      '--lock', 'environment.json',
    ]),
    /unknown option --lock/u,
  );
});

test('baseline modes reject partial or unsafe combinations', () => {
  assert.deepEqual(parseBaselinesOptions(['check']), {
    mode: 'check',
    records: null,
    result: null,
    compare: false,
  });
  assert.throws(
    () => parseBaselinesOptions(['candidate', '--records', 'records']),
    /requires --records and --result/u,
  );
  assert.throws(
    () => parseBaselinesOptions([
      'promote', '--records', 'records', '--result', 'result.json', '--compare',
    ]),
    /valid only for baselines candidate/u,
  );
});

test('removed toolchain command has no compatibility alias', () => {
  assert.throws(() => main(['toolchain', 'inspect']), /unknown command toolchain/u);
});

test('baseline bytes contain behavior only and are absent from the environment lock', () => {
  const result = JSON.parse(readFileSync(join(
    PROJECT_ROOT,
    'tools',
    'why3_reference',
    'baselines',
    'pr-v1',
    'prover-result.json',
  )));
  assert.equal(Object.hasOwn(result, 'referenceImageDigest'), false);
  assert.equal(Object.hasOwn(result, 'z3'), false);
  assert.deepEqual(Object.keys(result.comparisonTarget), ['why3', 'z3']);

  const lockSource = readFileSync(join(
    PROJECT_ROOT,
    'tools',
    'contracts',
    'reference-environment-lock-v1.json',
  ), 'utf8');
  assert.doesNotMatch(lockSource, /baseline|prCorpus|contracts|tracePatch/u);
});
