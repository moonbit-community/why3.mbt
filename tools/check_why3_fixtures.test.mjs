import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import test from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  enumerateFixtures,
  parseMoonbitDiagnostic,
  parseWhy3Position,
  sameNumbers,
  validateManifest,
} from './check_why3_fixtures.mjs';

const fixtureRoot = fileURLToPath(
  new URL('../fixtures/why3-1.7.2/', import.meta.url),
);
const manifestPath = fileURLToPath(
  new URL('./why3_reject_manifest.json', import.meta.url),
);

test('fixture inventory and reject manifest are exact', async () => {
  const inventory = await enumerateFixtures(fixtureRoot);
  assert.deepEqual(
    {
      regular: inventory.regular,
      symlink: inventory.symlink,
      total: inventory.total,
    },
    { regular: 976, symlink: 13, total: 989 },
  );
  const manifest = JSON.parse(await readFile(manifestPath, 'utf8'));
  assert.deepEqual(
    validateManifest(
      manifest,
      inventory.fixtures.map(fixture => fixture.relativePath),
    ),
    { reject: 58, extension: 2 },
  );
});

test('Why3 and MoonBit diagnostic positions are parsed structurally', () => {
  assert.deepEqual(
    parseWhy3Position(
      'File "x.mlw", line 12, characters 3-9:\nsyntax error\n',
    ),
    [12, 3, 9],
  );
  assert.equal(
    parseWhy3Position('Epsilon terms are currently not supported in WhyML\n'),
    null,
  );
  assert.deepEqual(
    parseMoonbitDiagnostic(
      'pprint_whyml_sexp: parse error UnexpectedToken 12:3-12:9: bad token\n',
    ),
    { kind: 'UnexpectedToken', position: [12, 3, 12, 9] },
  );
  assert.equal(parseMoonbitDiagnostic('not a parser diagnostic\n'), null);
  assert.equal(sameNumbers(null, null), true);
  assert.equal(sameNumbers(null, [1, 2, 3]), false);
  assert.equal(sameNumbers([1, 2, 3], [1, 2, 3]), true);
  assert.equal(sameNumbers([1, 2, 3], [1, 2, 4]), false);
});
