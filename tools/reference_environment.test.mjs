// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';

import referenceEnvironment from './why3_reference/reference_environment.cjs';
import { renderCandidate } from './why3_reference/generate_environment_lock_candidate.mjs';

const {
  ENVIRONMENT_LOCK_PATH,
  renderExpectedManifest,
  validateEnvironmentLock,
  validateManifest,
} = referenceEnvironment;

function lockFixture() {
  return JSON.parse(readFileSync(ENVIRONMENT_LOCK_PATH, 'utf8'));
}

test('environment lock uses a strict upstream-only whitelist', () => {
  const lock = validateEnvironmentLock(lockFixture());
  assert.deepEqual(Object.keys(lock), [
    'schemaVersion', 'platform', 'image', 'ocaml', 'why3', 'z3', 'manifest',
  ]);
  for (const forbidden of [
    'githubActions', 'contracts', 'baseline', 'patch', 'adapter',
    'executableSha256', 'buildRecipe',
  ]) {
    assert.doesNotMatch(JSON.stringify(lock), new RegExp(forbidden, 'iu'));
  }
  const changed = structuredClone(lock);
  changed.contracts = {};
  assert.throws(() => validateEnvironmentLock(changed), /keys/u);

  const changedPath = structuredClone(lock);
  changedPath.manifest.path = '/tmp/manifest.json';
  assert.throws(() => validateEnvironmentLock(changedPath), /manifest path/u);
});

test('embedded manifest content and hash are deterministic', () => {
  const lock = validateEnvironmentLock(lockFixture());
  const rendered = renderExpectedManifest(lock);
  assert.equal(referenceEnvironment.sha256(rendered), lock.manifest.sha256);
  assert.doesNotThrow(() => validateManifest(JSON.parse(rendered), lock));

  const changed = JSON.parse(rendered);
  changed.why3.runtime.executable = '/tmp/foreign-why3';
  assert.throws(
    () => validateManifest(changed, lock),
    /embedded manifest content/u,
  );
});

test('environment promotion changes only the image digest', () => {
  const lock = validateEnvironmentLock(lockFixture());
  const digest = `sha256:${'a'.repeat(64)}`;
  const candidate = JSON.parse(renderCandidate(
    lock,
    digest,
    Buffer.from(renderExpectedManifest(lock)),
  ));
  assert.deepEqual(candidate, {
    ...lock,
    image: { ...lock.image, digest },
  });
});

test('runtime verification rejects manifest bytes before executing tools', () => {
  const directory = mkdtempSync(join(tmpdir(), 'reference-manifest-reject-'));
  try {
    const path = join(directory, 'manifest.json');
    writeFileSync(path, '{}\n');
    assert.throws(
      () => referenceEnvironment.verifyReferenceEnvironment(lockFixture(), {
        manifestPath: path,
        run: () => assert.fail('runtime tool must not execute after a manifest rejection'),
      }),
      /embedded manifest file hash/u,
    );
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});
