// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const zeroDigest = '0'.repeat(64);
const userG = ['Origin.User', '67', ['none'], []];
const emptyTheory = [
  'Theory',
  ['TheoryKey', ['64656d6f'], '456d707479'],
  ['Origin.User', '456d707479', ['none'], []],
  [],
  ['Namespace', [], [], [], []],
];
const programOrigin = [
  'Origin.Snapshot',
  '696e74',
  ['SnapshotSymbolKey', '64656d6f2e496e74', 1, 0, 'program', zeroDigest],
  [],
];

const cases = [
  {
    name: 'empty-theory-preserves-key-name-history-and-namespace',
    canonical: emptyTheory,
  },
  {
    name: 'single-goal-task-preserves-goal-last-item',
    canonical: [
      'Task',
      [[
        'TaskItem.Decl',
        [
          'Decl',
          userG,
          [],
          [
            'Dprop.Pgoal',
            ['PrSymbol', ['proposition', 0], '67', userG],
            ['Ttrue'],
          ],
        ],
      ]],
    ],
  },
  {
    name: 'empty-pmodule-contains-its-pure-theory-projection',
    canonical: [
      'Pmodule',
      ['PmoduleKey', ['64656d6f'], '456d707479'],
      emptyTheory,
      [],
      ['ProgramNamespace', [], [], [], []],
    ],
  },
  {
    name: 'program-type-symbol-preserves-flags-and-definition',
    canonical: [
      'ProgramTypeSymbol',
      ['program', 0],
      ['type', 0],
      programOrigin,
      [false, false, false, false, [], []],
      ['TypeDefinition.NoDef'],
    ],
  },
  {
    name: 'pure-ity-preserves-program-and-logic-type-identities',
    canonical: [
      'ItyApp',
      ['program', 0],
      [],
      [],
      ['TyApp', ['type', 0], []],
    ],
  },
];

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

export function renderStage05CanonicalVectors() {
  const vectors = cases.map(entry => {
    const canonicalBytesUtf8 = `${JSON.stringify(entry.canonical)}\n`;
    return {
      ...entry,
      canonicalBytesUtf8,
      canonicalSha256: sha256(canonicalBytesUtf8),
    };
  });
  return `${JSON.stringify({
    schemaVersion: 1,
    canonicalSchemaVersion: 2,
    stage: 5,
    hashInputIncludesFinalLf: true,
    vectors,
  }, null, 2)}\n`;
}

function fail(message) {
  throw new Error(message);
}

function main(argv) {
  if (argv.length !== 2 || !['--output', '--check'].includes(argv[0])) {
    fail('usage: generate_stage05_canonical_vectors.mjs --output PATH | --check PATH');
  }
  const path = resolve(argv[1]);
  const rendered = renderStage05CanonicalVectors();
  if (argv[0] === '--output') writeFileSync(path, rendered);
  else if (readFileSync(path, 'utf8') !== rendered) fail(`${path} is stale`);
}

if (process.argv[1] !== undefined &&
    resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    main(process.argv.slice(2));
  } catch (error) {
    process.stderr.write(`generate_stage05_canonical_vectors: ${error.message}\n`);
    process.exitCode = 1;
  }
}
