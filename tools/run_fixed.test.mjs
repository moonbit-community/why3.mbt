// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const RUN_FIXED = join(PROJECT_ROOT, 'tools', 'why3_reference', 'run-fixed');

test('extensionless run-fixed remains Node 18 CommonJS-compatible', () => {
  const source = readFileSync(RUN_FIXED, 'utf8');
  assert.doesNotMatch(source, /^\s*(?:import|export)\b/gmu);
  assert.doesNotMatch(source, /\bimport\.meta\b/u);
  assert.doesNotMatch(source, /WHY3_REFERENCE_IMAGE_DIGEST|toolchain-lock/u);
  assert.match(source, /reference_environment\.cjs/u);
});

test('run-fixed documents its fixture-scoped command boundary', () => {
  const result = spawnSync(RUN_FIXED, ['--help'], {
    cwd: PROJECT_ROOT,
    encoding: 'utf8',
    shell: false,
  });
  if (result.error?.code === 'EPERM') return;
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /<fixture-id>/u);
  assert.match(result.stdout, /-- <why3 arguments/u);
});

test('run-fixed rejects wrapper options outside its fixed profile', () => {
  const result = spawnSync(RUN_FIXED, [
    'mvp.abs',
    '--foreign-option',
    '--',
    'prove',
    'tools/why3_reference/fixtures/mvp.mlw',
  ], {
    cwd: PROJECT_ROOT,
    encoding: 'utf8',
    shell: false,
  });
  if (result.error?.code === 'EPERM') return;
  assert.notEqual(result.status, 0);
  assert.match(result.stderr, /unknown wrapper option/u);
});
