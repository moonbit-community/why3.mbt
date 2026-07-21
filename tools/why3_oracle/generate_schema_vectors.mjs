// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

function sha256(value) {
  return createHash('sha256').update(value).digest('hex');
}

const cases = [
  {
    name: 'bytes-are-lowercase-hex-without-utf8-decoding',
    purpose: 'Raw identifier bytes remain lossless, including invalid UTF-8.',
    abstractInput: { bytes: [0x00, 0xc3, 0xa9, 0xff] },
    canonical: ['bytes', '00c3a9ff'],
  },
  {
    name: 'option-none-has-an-explicit-sentinel',
    purpose: 'An absent field cannot disappear from a canonical node.',
    abstractInput: { option: null },
    canonical: ['none'],
  },
  {
    name: 'option-some-wraps-the-value',
    purpose: 'Some(value) remains distinct from value and from None.',
    abstractInput: { option: { bytes: [0x41] } },
    canonical: ['some', ['bytes', '41']],
  },
  {
    name: 'semantic-map-sorts-by-canonical-byte-key',
    purpose: 'Map insertion order cannot affect canonical output.',
    abstractInput: {
      insertionOrder: [['62', 'b'], ['6161', 'aa'], ['00', 'zero'], ['61', 'a']],
    },
    canonical: ['map', [['00', 'zero'], ['61', 'a'], ['6161', 'aa'], ['62', 'b']]],
  },
  {
    name: 'global-symbols-number-at-first-preorder-encounter',
    purpose: 'A reference before declaration owns index zero; equal names do not merge identities.',
    abstractInput: {
      events: [
        ['reference', 'logic-symbol-A-named-x'],
        ['declaration', 'logic-symbol-A-named-x'],
        ['declaration', 'logic-symbol-B-named-x'],
      ],
    },
    canonical: [
      'events',
      [
        ['reference', ['logic', 0], '78'],
        ['declaration', ['logic', 0], '78'],
        ['declaration', ['logic', 1], '78'],
      ],
    ],
  },
  {
    name: 'bound-variables-use-de-bruijn-indices',
    purpose: 'Binder spelling and runtime identity do not affect canonical output.',
    abstractInput: 'forall x. exists y. pair(x,y)',
    canonical: [
      'forall',
      [['type', 'int']],
      ['exists', [['type', 'int']], ['app', 'pair', [['bound', 1], ['bound', 0]]]],
    ],
  },
  {
    name: 'clone-witness-preserves-source-and-sorts-instantiations',
    purpose: 'Clone history cannot collapse into its expanded declarations.',
    abstractInput: {
      source: 'theory-key-T',
      sourceItemIdentity: 7,
      typeInstantiationInsertionOrder: [['62', 'int'], ['61', 'bool']],
    },
    canonical: [
      'CloneWitness',
      ['theory-key', '54'],
      7,
      [['61', 'bool'], ['62', 'int']],
      [],
      [],
    ],
  },
  {
    name: 'generated-origin-carries-stage-but-no-context-token',
    purpose: 'SMT alpha normalization is eligible only for explicit generated provenance.',
    abstractInput: {
      contextToken: 'must-not-serialize',
      origin: { kind: 'Generated', stage: 'wp', displayNameBytes: [0x76, 0x63] },
    },
    canonical: ['Origin.Generated', 'wp', '7663', ['none'], []],
  },
];

const vectors = cases.map(vector => {
  const canonicalBytesUtf8 = `${JSON.stringify(vector.canonical)}\n`;
  return {
    ...vector,
    canonicalBytesUtf8,
    canonicalSha256: sha256(canonicalBytesUtf8),
  };
});

function fail(message) {
  throw new Error(message);
}

function parseArguments(argv) {
  if (argv.length === 0) return { mode: 'stdout', path: null };
  if (argv.length !== 2 || !['--output', '--check'].includes(argv[0])) {
    fail('usage: generate_schema_vectors.mjs [--output PATH | --check PATH]');
  }
  return { mode: argv[0].slice(2), path: resolve(argv[1]) };
}

const rendered = `${JSON.stringify({
  schemaVersion: 1,
  canonicalSchemaVersion: 2,
  hashInputIncludesFinalLf: true,
  vectors,
}, null, 2)}\n`;

try {
  const arguments_ = parseArguments(process.argv.slice(2));
  if (arguments_.mode === 'output') {
    writeFileSync(arguments_.path, rendered);
  } else if (arguments_.mode === 'check') {
    if (readFileSync(arguments_.path, 'utf8') !== rendered) {
      fail(`${arguments_.path} does not match generated canonical vectors`);
    }
  } else {
    process.stdout.write(rendered);
  }
} catch (error) {
  process.stderr.write(`generate_schema_vectors: ${error.message}\n`);
  process.exitCode = 1;
}
