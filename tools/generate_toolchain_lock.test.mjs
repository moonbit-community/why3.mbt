// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import assert from 'node:assert/strict';
import {
  mkdtempSync,
  readFileSync,
  rmSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';
import {
  generateCandidate,
  loadToolchainInputs,
  reportFixture,
} from './toolchain_lock_test_helpers.mjs';

test('toolchain lock candidate closes over every fixed input', () => {
  const directory = mkdtempSync(join(tmpdir(), 'why3-toolchain-lock-test-'));
  try {
    const { inputBytes, inputs } = loadToolchainInputs();
    const { candidatePath, result } = generateCandidate(
      reportFixture(inputs, inputBytes),
      directory,
    );
    assert.equal(result.status, 0, result.stderr);
    const candidate = JSON.parse(readFileSync(candidatePath, 'utf8'));
    assert.equal(candidate.image.digest, `sha256:${'a'.repeat(64)}`);
    assert.deepEqual(candidate.buildRecipe.frontendImage, inputs.buildRecipe.frontendImage);
    assert.deepEqual(candidate.buildRecipe.baseImage, inputs.baseImage);
    assert.deepEqual(candidate.githubActions, inputs.githubActions);
    assert.equal(Object.hasOwn(candidate, 'moon'), false);
    assert.equal(Object.hasOwn(candidate, 'moonDependencies'), false);
    assert.equal(candidate.why3.semanticSnapshotSha256, inputs.why3.semanticSnapshotSha256);
    assert.deepEqual(candidate.why3.opamRecipe, inputs.why3.opamRecipe);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});

test('toolchain lock candidate rejects a fixed solver version drift', () => {
  const directory = mkdtempSync(join(tmpdir(), 'why3-toolchain-lock-test-'));
  try {
    const { inputBytes, inputs } = loadToolchainInputs();
    const report = reportFixture(inputs, inputBytes);
    report.z3.version = '0.0.0';
    const { result } = generateCandidate(report, directory);
    assert.notEqual(result.status, 0);
    assert.match(result.stderr, /Z3 executable drift/u);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});
