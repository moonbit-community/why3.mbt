// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  parseCheckArguments,
  productMismatch,
} from './why3_reference/check_upstream_corpus.mjs';
import {
  parseGeneratorArguments,
} from './why3_reference/generate_upstream_corpus.mjs';
import {
  typeOnlyArguments,
  validateUpstreamCorpusContract,
} from './why3_reference/upstream_corpus.mjs';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');

test('checked-in upstream corpus is the complete fixed Why3 matrix', () => {
  const contract = validateUpstreamCorpusContract(JSON.parse(readFileSync(
    join(PROJECT_ROOT, 'tools', 'contracts', 'upstream-corpus-v1.json'),
    'utf8',
  )));
  assert.deepEqual(contract.counts, {
    examples: 446,
    tests: 58,
    total: 504,
    accepted: 459,
    rejected: 45,
  });
  assert.equal(
    contract.entriesSha256,
    '866c50a6a92c9b14eb1c2dacee9d29e79b5bc628cf69bd499c97aed8c897b1fd',
  );
  assert.equal(
    contract.entries.some(entry =>
      entry.path.startsWith('examples_in_progress/')),
    false,
  );
  assert.deepEqual(
    [...new Set(contract.entries
      .filter(entry => !entry.accepted)
      .map(entry => entry.officialExitCode))],
    [1],
  );
});

test('upstream generator and checker accept one explicit source form', () => {
  const generated = parseGeneratorArguments([
    '--why3-root',
    'why3',
    '--check',
    'contract.json',
  ]);
  assert.match(generated.why3Root, /why3$/u);
  assert.match(generated.output, /contract\.json$/u);
  assert.equal(generated.check, true);

  const checked = parseCheckArguments([
    '--why3-archive',
    'why3.tar.gz',
    '--contract',
    'contract.json',
  ]);
  assert.match(checked.why3Archive, /why3\.tar\.gz$/u);
  assert.match(checked.contract, /contract\.json$/u);
  assert.throws(
    () => parseGeneratorArguments([
      '--why3-root',
      'why3',
      '--why3-archive',
      'why3.tar.gz',
    ]),
    /mutually exclusive/u,
  );
  assert.throws(
    () => parseCheckArguments([
      '--why3-root',
      'why3',
      '--why3-archive',
      'why3.tar.gz',
    ]),
    /mutually exclusive/u,
  );
});

test('type-only target invocation uses explicit stdlib and source loadpaths', () => {
  const argv = typeOnlyArguments('/fixed/why3', '/corpus/example.mlw');
  assert.deepEqual(argv, [
    'prove',
    '--no-load-default-plugins',
    '--no-stdlib',
    '-L',
    '/fixed/why3/stdlib',
    '-L',
    '/corpus',
    '--type-only',
    '/corpus/example.mlw',
  ]);
});

test('target result comparison covers acceptance, exit status, and timeout', () => {
  const accepted = { accepted: true, officialExitCode: 0 };
  const rejected = { accepted: false, officialExitCode: 1 };
  const success = {
    status: 0,
    signal: null,
    timedOut: false,
    error: null,
  };
  const rejection = {
    status: 1,
    signal: null,
    timedOut: false,
    error: null,
  };
  assert.equal(productMismatch(accepted, success), false);
  assert.equal(productMismatch(rejected, rejection), false);
  assert.equal(productMismatch(accepted, rejection), true);
  assert.equal(productMismatch(rejected, { ...rejection, status: 2 }), true);
  assert.equal(productMismatch(accepted, { ...success, timedOut: true }), true);
});
