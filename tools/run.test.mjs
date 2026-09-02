// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  changedProjectPaths,
  main,
  parseCheckOptions,
  parseReferenceOptions,
  runCheckPipeline,
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

test('check task combines project and reference options', () => {
  const options = parseCheckOptions([
    '--moon-diff-only',
    '--why3-archive',
    'reference.tar.gz',
  ]);
  assert.equal(options.moonDiffOnly, true);
  assert.match(options.why3Archive, /reference\.tar\.gz$/u);
  assert.equal(options.why3Root, null);
  assert.equal(options.quick, false);
  assert.throws(
    () => parseCheckOptions(['--moon-diff-only', '--moon-diff-only']),
    /duplicate option --moon-diff-only/u,
  );
  assert.throws(
    () => parseCheckOptions(['--quick']),
    /unknown option --quick/u,
  );
});

test('complete check runs lower-cost work before tests and adapter preflight', () => {
  const calls = [];
  const record = name => value => calls.push([name, value]);
  const options = {
    moonDiffOnly: true,
    why3Archive: '/tmp/why3.tar.gz',
    why3Root: null,
    quick: false,
  };
  runCheckPipeline(options, {
    projectHygiene: record('projectHygiene'),
    quickTests: record('quickTests'),
    smoke: record('smoke'),
    projectTests: record('projectTests'),
    fixtures: record('fixtures'),
    preflight: record('preflight'),
    contracts: record('contracts'),
    upstream: record('upstream'),
    layers: record('layers'),
    finalCleanliness: record('finalCleanliness'),
  });
  assert.deepEqual(calls.map(([name]) => name), [
    'projectHygiene',
    'quickTests',
    'smoke',
    'projectTests',
    'fixtures',
    'preflight',
    'contracts',
    'upstream',
    'layers',
    'finalCleanliness',
  ]);
  assert.deepEqual(calls[0][1], { moonDiffOnly: true });
  assert.equal(calls[6][1], options);
  assert.equal(calls[7][1], options);
  assert.equal(calls[8][1], options);
  assert.deepEqual(calls[9][1], { moonDiffOnly: true });
});

test('project mutation checks compare content against the starting worktree', () => {
  const before = new Map([
    ['already-dirty.mbt', 'initial-dirty-content'],
    ['stable.mbti', 'stable-content'],
    ['removed.mbt', 'present'],
  ]);
  const after = new Map([
    ['already-dirty.mbt', 'new-content'],
    ['stable.mbti', 'stable-content'],
    ['created.mbt', 'created'],
  ]);
  assert.deepEqual(changedProjectPaths(before, after), [
    'already-dirty.mbt',
    'created.mbt',
    'removed.mbt',
  ]);
});

test('removed toolchain command has no compatibility alias', () => {
  assert.throws(() => main(['toolchain', 'inspect']), /unknown command toolchain/u);
});

test('merged aggregate commands have no compatibility aliases', () => {
  assert.throws(() => main(['project']), /unknown command project/u);
  assert.throws(() => main(['reference']), /unknown command reference/u);
  assert.throws(() => main(['baselines', 'check']), /unknown command baselines/u);
});

test('the environment lock contains no behavioral baseline state', () => {
  const lockSource = readFileSync(join(
    PROJECT_ROOT,
    'tools',
    'contracts',
    'reference-environment-lock-v1.json',
  ), 'utf8');
  assert.doesNotMatch(lockSource, /baseline|prCorpus|contracts|tracePatch/u);
});
