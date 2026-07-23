// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import assert from 'node:assert/strict';
import test from 'node:test';
import {
  canonicalSha,
  checkAll,
  checkCanonicalContracts,
  checkDriverAndTrustedSchema,
  checkFeaturesAndCorpus,
  checkLicenseAndAttribution,
  checkProfiles,
  checkReferenceEnvironmentLock,
  checkReferenceRollout,
} from './check_pr00_contracts.mjs';

test('PR-00 checked-in contracts are internally closed', () => {
  assert.doesNotThrow(checkLicenseAndAttribution);
  assert.doesNotThrow(checkCanonicalContracts);
  assert.doesNotThrow(checkDriverAndTrustedSchema);
  assert.doesNotThrow(checkFeaturesAndCorpus);
  assert.doesNotThrow(checkProfiles);
  assert.doesNotThrow(checkReferenceEnvironmentLock);
  assert.doesNotThrow(checkReferenceRollout);
});

test('canonical contract hashes include compact JSON and one LF', () => {
  assert.equal(
    canonicalSha(['why3', 1]),
    '8791ddf4d4de3d4cbf9a06820c13281b299b86731c74fafe50c30cd15da5c1ad',
  );
});

test('reference environment lock contains only upstream environment identity', () => {
  const lock = checkReferenceEnvironmentLock();
  assert.deepEqual(Object.keys(lock), [
    'schemaVersion', 'platform', 'image', 'ocaml', 'why3', 'z3', 'manifest',
  ]);
});

test('quick aggregate check reruns deterministic generators', () => {
  assert.doesNotThrow(() => checkAll({
    why3Root: '../why3',
    why3Archive: null,
    quick: true,
  }));
});
