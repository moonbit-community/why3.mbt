#!/usr/bin/env node
// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..');
const FEATURES_PATH = 'tools/contracts/features-v2.json';
const DIAGNOSTICS_PATH = 'tools/contracts/diagnostics-v1.json';
const RECORD_SCHEMA_PATH =
  'tools/contracts/schema/canonical-record-v3.schema.json';
const WHY3_COMMIT = '1343338d3bb1941c0d4f134283bb0790816113c4';

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function canonicalSha(value) {
  return sha256(`${JSON.stringify(value)}\n`);
}

function compareUtf8(left, right) {
  return Buffer.compare(Buffer.from(left, 'utf8'), Buffer.from(right, 'utf8'));
}

function parseArguments(argv) {
  if (argv.length === 0) return { mode: 'stdout', path: null };
  if (argv.length !== 2 || !['--output', '--check'].includes(argv[0])) {
    fail('usage: generate_canonical_schema_v3.mjs [--output PATH | --check PATH]');
  }
  return { mode: argv[0].slice(2), path: resolve(argv[1]) };
}

function sortedObject(entries) {
  return Object.fromEntries(
    [...entries].sort(([left], [right]) => compareUtf8(left, right)),
  );
}

const BASE_NODES = {
  'Boolean': ['value'],
  'Bytes': ['lowercase_hex'],
  'DeBruijn': ['zero_based_index'],
  'Definition': ['kind', 'zero_based_index', 'value'],
  'GraphV3': ['roots', 'definitions'],
  'Integer': ['canonical_decimal'],
  'Map': ['entries_sorted_by_canonical_key_then_value'],
  'Option.None': [],
  'Option.Some': ['value'],
  'Origin.Generated': ['stage', 'name', 'source_span', 'attributes'],
  'Origin.User': ['name', 'source_span', 'attributes'],
  'Product': ['values_in_source_tuple_order'],
  'Reference': ['kind', 'zero_based_index'],
  'Sequence': ['values_in_semantic_order'],
  'Set': ['values_sorted_by_canonical_key'],
  'SourceSpan': [
    'relative_path_hex',
    'start_byte',
    'end_byte',
    'start_line',
    'start_column',
    'end_line',
    'end_column',
  ],
  'Unit': [],
};

const DEFINITION_KINDS = [
  'attribute',
  'identifier',
  'type-variable',
  'type-symbol',
  'type',
  'logic-variable',
  'logic-symbol',
  'proposition-symbol',
  'pattern',
  'term',
  'declaration',
  'theory',
  'theory-declaration',
  'task',
  'program-type-symbol',
  'region',
  'program-variable',
  'exception-symbol',
  'computation-type',
  'routine-symbol',
  'program-pattern',
  'expression',
  'computation-expression',
  'program-declaration',
  'module',
];

function buildSchema() {
  const featureBytes = readFileSync(join(PROJECT_ROOT, FEATURES_PATH));
  const features = JSON.parse(featureBytes);
  const diagnosticBytes = readFileSync(join(PROJECT_ROOT, DIAGNOSTICS_PATH));
  const diagnostics = JSON.parse(diagnosticBytes);
  const recordSchemaBytes = readFileSync(join(PROJECT_ROOT, RECORD_SCHEMA_PATH));
  if (features.schemaVersion !== 2 || features.why3Commit !== WHY3_COMMIT) {
    fail('canonical v3 requires the pinned complete feature contract v2');
  }
  if (features.variants.some(entry => entry.targetLane !== 'exact')) {
    fail('canonical v3 target constructor inventory contains a non-exact lane');
  }

  const variantCoverage = features.variants.map(entry => ({
    featureId: entry.id,
    canonicalTag: entry.id,
    fieldOrder: ['payload'],
    payloadEncoding:
      'Unit for nullary constructors; otherwise one value or Product in OCaml source tuple order',
  }));
  const recordCoverage = features.records.map(entry => ({
    featureId: entry.id,
    canonicalTag: entry.id,
    fieldOrder: entry.canonicalV3Fields,
    excluded: entry.excludedFromCanonicalV3,
  }));
  const nodeEntries = [
    ...Object.entries(BASE_NODES),
    ...variantCoverage.map(entry => [entry.canonicalTag, entry.fieldOrder]),
    ...recordCoverage.map(entry => [entry.canonicalTag, entry.fieldOrder]),
  ];
  const duplicateTags = nodeEntries
    .map(([tag]) => tag)
    .filter((tag, index, tags) => tags.indexOf(tag) !== index);
  if (duplicateTags.length !== 0) {
    fail(`duplicate canonical v3 tags: ${JSON.stringify(duplicateTags)}`);
  }
  const nodeFieldOrder = sortedObject(nodeEntries);
  const featureCoverage = {
    variants: variantCoverage,
    records: recordCoverage,
    opaqueProjections: features.opaqueProjections,
  };
  const coverageIds = new Set([
    ...variantCoverage.map(entry => entry.featureId),
    ...recordCoverage.map(entry => entry.featureId),
    ...features.opaqueProjections.map(entry => entry.id),
  ]);
  const expectedIds = new Set([
    ...features.variants.map(entry => entry.id),
    ...features.records.map(entry => entry.id),
    ...features.opaqueProjections.map(entry => entry.id),
  ]);
  if (coverageIds.size !== expectedIds.size ||
      [...expectedIds].some(id => !coverageIds.has(id))) {
    fail('canonical v3 does not cover the complete target feature inventory');
  }

  const body = {
    schemaVersion: 3,
    recordVersion: 3,
    profile: 'why3-1.7.2-complete-graph-v3',
    status: 'active',
    why3Commit: WHY3_COMMIT,
    inputs: {
      targetFeatures: {
        path: FEATURES_PATH,
        sha256: sha256(featureBytes),
        variantInventorySha256: features.variantInventorySha256,
        recordInventorySha256: features.recordInventorySha256,
        opaqueProjectionInventorySha256:
          features.opaqueProjectionInventorySha256,
      },
      structuredDiagnostics: {
        path: DIAGNOSTICS_PATH,
        sha256: sha256(diagnosticBytes),
        diagnosticContractSha256: diagnostics.diagnosticContractSha256,
      },
      recordSchema: {
        path: RECORD_SCHEMA_PATH,
        sha256: sha256(recordSchemaBytes),
      },
    },
    encoding: {
      json:
        'UTF-8 compact JSON, node arrays, object fields in record order, exactly one LF terminator',
      bytes: 'lowercase hexadecimal without prefix',
      integers:
        'canonical base-10 string with optional leading minus and no redundant leading zeroes',
      sourceSequences: 'preserve semantic source/history order',
      product:
        'constructor tuple payload in OCaml source order; never rely on OCaml evaluation order',
      option: 'Option.None or Option.Some',
      maps:
        'Map entries are [key,value] pairs sorted by canonical key bytes then canonical value bytes',
      sets: 'Set values sorted by canonical bytes',
      paths: 'fixture-root-relative POSIX path encoded as lowercase byte hex',
      locations:
        'one-based lines, zero-based byte columns, zero-based half-open byte offsets',
    },
    identity: {
      definitionKinds: DEFINITION_KINDS,
      allocation:
        'assign [kind,index] on first deterministic preorder encounter from roots',
      references:
        'every shared graph object is emitted once as Definition and subsequently as Reference',
      boundVariables: 'DeBruijn with zero denoting the innermost binder',
      sourceNames: 'preserved as Bytes even when not valid UTF-8',
      origin:
        'user/generated provenance is semantic and serialized without runtime tags',
      physicalIdentitySerialized: false,
      runtimeTagsSerialized: false,
      cachesSerialized: false,
      localizedMessagesSerialized: false,
    },
    constructorPayloadEncoding: {
      nullary: ['Unit'],
      unary: '<canonical value>',
      tuple: ['Product', '<values in OCaml source tuple order>'],
      record:
        'record tag followed by canonicalV3Fields in upstream declaration order',
      recursiveReference:
        'Reference when the object already has a Definition; otherwise allocate before descending',
    },
    recordFieldOrder: {
      CanonicalRecordV3: [
        'schema',
        'semantic_profile_sha256',
        'diagnostic_contract_sha256',
        'fixture',
        'source_sha256',
        'scope',
        'unit_kind',
        'unit_name_hex',
        'goal_name_hex',
        'goal_ordinal',
        'stage',
        'canonical_sha256',
        'canonical',
      ],
    },
    nodeEncoding:
      'Each node is a JSON array whose first element is its exact tag and whose remaining elements follow nodeFieldOrder.',
    nodeFieldOrder,
    featureCoverage,
    featureCoverageSha256: canonicalSha(featureCoverage),
    counts: {
      baseNodes: Object.keys(BASE_NODES).length,
      definitionKinds: DEFINITION_KINDS.length,
      variantTags: variantCoverage.length,
      recordTags: recordCoverage.length,
      opaqueProjections: features.opaqueProjections.length,
      nodeTags: Object.keys(nodeFieldOrder).length,
      excludedRawFields: recordCoverage.reduce(
        (count, entry) => count + Object.keys(entry.excluded).length,
        0,
      ),
    },
  };
  return {
    ...body,
    canonicalSchemaSha256: canonicalSha(body),
  };
}

try {
  const arguments_ = parseArguments(process.argv.slice(2));
  const rendered = `${JSON.stringify(buildSchema(), null, 2)}\n`;
  if (arguments_.mode === 'output') {
    writeFileSync(arguments_.path, rendered);
  } else if (arguments_.mode === 'check') {
    if (readFileSync(arguments_.path, 'utf8') !== rendered) {
      fail(`${arguments_.path} does not match the generated canonical v3 schema`);
    }
  } else {
    process.stdout.write(rendered);
  }
} catch (error) {
  process.stderr.write(`generate_canonical_schema_v3: ${error.message}\n`);
  process.exitCode = 1;
}
