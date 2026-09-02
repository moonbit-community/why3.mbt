// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import test from 'node:test';

import {
  bindCasesToCorpus,
} from './why3_reference/run_result_differential.mjs';

const corpus = JSON.parse(
  readFileSync(new URL('./contracts/pr-corpus-v1.json', import.meta.url)),
);

test('fixed result cases exactly cover the contracted prover-result goals', () => {
  const expected = corpus.entries
    .filter(entry =>
      entry.kind === 'whyml-semantic' &&
      entry.expected.gateStages.includes('prover-result'),
    )
    .reduce(
      (count, entry) =>
        count + entry.units.reduce(
          (unitCount, unit) => unitCount + unit.goals.length,
          0,
        ),
      0,
    );
  assert.equal(bindCasesToCorpus(corpus).length, expected);
});
