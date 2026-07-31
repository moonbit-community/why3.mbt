#!/usr/bin/env node
// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const SCHEMA_PATH =
  'tools/contracts/schema/diagnostic-record-v1.schema.json';
const PARSER_MANIFEST_PATH = 'tools/why3_reject_manifest.json';
const TARGET_FEATURES_PATH = 'tools/contracts/features-v2.json';
const FULL_MLW_PATCH_PATH =
  'tools/why3_reference/patches/full-mlw-export.patch';
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

function projectFile(path) {
  return join(PROJECT_ROOT, path);
}

function parseArguments(argv) {
  if (argv.length === 0) return { mode: 'stdout', path: null };
  if (argv.length !== 2 || !['--output', '--check'].includes(argv[0])) {
    fail('usage: generate_diagnostic_contract.mjs [--output PATH | --check PATH]');
  }
  return { mode: argv[0].slice(2), path: resolve(argv[1]) };
}

const CATEGORY_BY_MOON_KIND = {
  NestedModule: 'NestedUnit',
  UnexpectedToken: 'Syntax',
  UnsupportedEpsilon: 'UnsupportedConcreteSyntax',
};

function buildContract() {
  const schemaBytes = readFileSync(projectFile(SCHEMA_PATH));
  const parserManifestBytes = readFileSync(projectFile(PARSER_MANIFEST_PATH));
  const parserManifest = JSON.parse(parserManifestBytes);
  const targetFeatureBytes = readFileSync(projectFile(TARGET_FEATURES_PATH));
  const fullPatchBytes = readFileSync(projectFile(FULL_MLW_PATCH_PATH));
  const rejectEntries = Object.entries(parserManifest.entries)
    .filter(([, entry]) => entry.lane === 'reject')
    .map(([path, entry]) => {
      const category = CATEGORY_BY_MOON_KIND[entry.moonbitKind];
      if (category === undefined) {
        fail(`no structured parser category for ${entry.moonbitKind}`);
      }
      return {
        path,
        stage: 'parsing',
        category,
        referencePosition: entry.why3Position,
        moonbitKind: entry.moonbitKind,
        moonbitPosition: entry.moonbitPosition ?? null,
      };
    });
  if (rejectEntries.length !== 58) {
    fail(`expected 58 parser rejects, got ${rejectEntries.length}`);
  }
  const categoryCounts = Object.fromEntries(
    Object.values(CATEGORY_BY_MOON_KIND).sort().map(category => [
      category,
      rejectEntries.filter(entry => entry.category === category).length,
    ]),
  );
  const activeParserMappings = Object.entries(CATEGORY_BY_MOON_KIND)
    .sort(([left], [right]) => left.localeCompare(right))
    .map(([moonbitKind, category]) => ({ moonbitKind, category }));
  const body = {
    schemaVersion: 1,
    contract: 'why3-1.7.2-structured-diagnostics-v1',
    why3Commit: WHY3_COMMIT,
    recordSchema: {
      path: SCHEMA_PATH,
      sha256: sha256(schemaBytes),
    },
    targetFeatures: {
      path: TARGET_FEATURES_PATH,
      sha256: sha256(targetFeatureBytes),
    },
    referenceInstrumentation: {
      path: FULL_MLW_PATCH_PATH,
      sha256: sha256(fullPatchBytes),
      changesSemanticAcceptance: false,
      purpose:
        'replace prose-only parser branches with stable categories while preserving source locations',
    },
    fieldOrder: {
      accepted: ['schema', 'accepted'],
      rejected: [
        'schema',
        'accepted',
        'stage',
        'severity',
        'category',
        'warning_code',
        'relative_path_hex',
        'start_byte',
        'end_byte',
        'start_line',
        'start_column',
        'end_line',
        'end_column',
      ],
    },
    policy: {
      compared: ['stage', 'severity', 'category', 'warning_code', 'source_span'],
      notCompared: ['localized_message', 'formatted_type_message', 'backtrace'],
      warningCode: 'stable Why3 warning identifier; null for errors',
      path: 'fixture-root-relative POSIX path encoded as lowercase byte hex',
      byteOffsets: 'zero-based half-open byte offsets',
      lines: 'one-based',
      columns: 'zero-based byte columns',
      absentSpan:
        'all six numeric span fields are null; relative_path_hex remains present',
    },
    stages: [
      'lexing',
      'parsing',
      'typing',
      'program-typing',
      'module-interface',
      'vc-generation',
      'transformation',
      'driver',
      'prover',
    ],
    categoryEncoding:
      'stable constructor-style identifier, independent of English exception printers',
    activeParserMappings,
    activeParserMappingsSha256: canonicalSha(activeParserMappings),
    parserCorpus: {
      command: 'why3 prove --parse-only',
      totalRejects: rejectEntries.length,
      locatedRejects: rejectEntries.filter(entry =>
        entry.referencePosition !== null).length,
      unlocatedRejects: rejectEntries.filter(entry =>
        entry.referencePosition === null).length,
      categoryCounts,
      entriesSha256: canonicalSha(rejectEntries),
    },
  };
  return {
    ...body,
    diagnosticContractSha256: canonicalSha(body),
  };
}

try {
  const arguments_ = parseArguments(process.argv.slice(2));
  const rendered = `${JSON.stringify(buildContract(), null, 2)}\n`;
  if (arguments_.mode === 'output') {
    writeFileSync(arguments_.path, rendered);
  } else if (arguments_.mode === 'check') {
    if (readFileSync(arguments_.path, 'utf8') !== rendered) {
      fail(`${arguments_.path} does not match the generated diagnostic contract`);
    }
  } else {
    process.stdout.write(rendered);
  }
} catch (error) {
  process.stderr.write(`generate_diagnostic_contract: ${error.message}\n`);
  process.exitCode = 1;
}
