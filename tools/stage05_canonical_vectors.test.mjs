// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';
import {
  renderStage05CanonicalVectors,
} from './why3_reference/generate_canonical_vectors.mjs';

const vectorPath = resolve(
  dirname(fileURLToPath(import.meta.url)),
  'contracts',
  'stage05-canonical-vectors-v1.json',
);

test('Stage 05 cross-language canonical vectors are current', () => {
  assert.equal(readFileSync(vectorPath, 'utf8'), renderStage05CanonicalVectors());
});
