// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import {
  copyFileSync,
  mkdtempSync,
  readFileSync,
  rmSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import {
  prepareReferenceRuntime,
  referenceRuntimeEnvironment,
} from './reference_runtime.mjs';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const MANIFEST_PATH = join(PROJECT_ROOT, 'tools', 'why3_reject_manifest.json');
const DIAGNOSTIC_CONTRACT_PATH = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'diagnostics-v1.json',
);
const TARGET_FEATURES_PATH = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'features-v2.json',
);
const CANONICAL_SCHEMA_V3_PATH = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'canonical-schema-v3.json',
);
const SEMANTIC_PROFILE_V3_PATH = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'semantic-profile-v3.json',
);
const EXPORTER_SOURCE = join(SCRIPT_DIRECTORY, 'export_full_mlw.ml');
const CANONICAL_V3_PROFILE_SOURCE = join(
  SCRIPT_DIRECTORY,
  'canonical_v3_profile.ml',
);
const CANONICAL_V3_SOURCE = join(SCRIPT_DIRECTORY, 'canonical_v3.ml');
const PPRINT_WHYML_SEXP = join(
  PROJECT_ROOT,
  '_build/native/debug/build/cmd/pprint_whyml_sexp/pprint_whyml_sexp.exe',
);

function fail(message) {
  throw new Error(message);
}

function parseArguments(argv) {
  const result = {
    why3Root: resolve(PROJECT_ROOT, '..', 'why3'),
    why3Archive: null,
  };
  let explicitRoot = false;
  for (let index = 0; index < argv.length; index += 1) {
    const option = argv[index];
    if (option !== '--why3-root' && option !== '--why3-archive') {
      fail(`unknown argument ${option}`);
    }
    const value = argv[index + 1];
    if (value === undefined) fail(`${option} requires a path`);
    if (option === '--why3-root') {
      result.why3Root = resolve(value);
      explicitRoot = true;
    } else {
      result.why3Archive = resolve(value);
    }
    index += 1;
  }
  if (explicitRoot && result.why3Archive !== null) {
    fail('--why3-root and --why3-archive are mutually exclusive');
  }
  return result;
}

function run(command, argv, options = {}) {
  const result = spawnSync(command, argv, {
    cwd: options.cwd ?? PROJECT_ROOT,
    encoding: 'utf8',
    env: options.env ?? process.env,
    maxBuffer: 128 * 1024 * 1024,
    shell: false,
  });
  if (result.status !== 0 || result.signal !== null ||
      (result.error && result.error.code !== 'EPERM')) {
    const detail = `${result.stdout ?? ''}${result.stderr ?? ''}${result.error?.message ?? ''}`.trim();
    fail(`${command} ${argv.join(' ')} failed: ${detail}`);
  }
  return result.stdout;
}

function firstDifference(left, right) {
  const length = Math.min(left.length, right.length);
  let offset = 0;
  while (offset < length && left.charCodeAt(offset) === right.charCodeAt(offset)) {
    offset += 1;
  }
  return offset;
}

function compareExact(reference, moon, fixture) {
  if (reference === moon) return;
  const offset = firstDifference(reference, moon);
  const from = Math.max(0, offset - 120);
  fail(
    `lossless full-file mismatch for ${fixture} at byte ${offset}\n` +
    `reference: ${JSON.stringify(reference.slice(from, offset + 240))}\n` +
    `moon:      ${JSON.stringify(moon.slice(from, offset + 240))}`,
  );
}

function parserManifestEntries() {
  const manifest = JSON.parse(readFileSync(MANIFEST_PATH, 'utf8'));
  return Object.entries(manifest.entries).map(([path, entry]) => ({
    relativePath: path,
    fixture: join(PROJECT_ROOT, 'fixtures', 'why3-1.7.2', path),
    entry,
  }));
}

function parseCompactRecord(output, label) {
  if (!output.endsWith('\n') || output.slice(0, -1).includes('\n')) {
    fail(`${label} is not one LF-terminated JSON record`);
  }
  const record = JSON.parse(output);
  if (JSON.stringify(record) !== output.slice(0, -1)) {
    fail(`${label} is not compact canonical JSON`);
  }
  return record;
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function checkSurfaceSourceCoverage(features) {
  const source = readFileSync(CANONICAL_V3_SOURCE, 'utf8');
  const dependencyFamilies = new Set([
    'Constant.constant',
    'Number.int_literal_kind',
    'Number.real_literal_kind',
    'Dterm.dbinop',
    'Dterm.dquant',
    'Expr.rs_kind',
    'Expr.assertion_kind',
    'Expr.for_direction',
    'Ity.mask',
    'Decl.ind_sign',
    'Decl.prop_kind',
  ]);
  const variants = features.variants.filter(entry =>
    entry.migrationPhase === 1 ||
    dependencyFamilies.has(`${entry.owner}.${entry.type}`));
  const records = features.records.filter(entry =>
    entry.migrationPhase === 1 ||
    entry.owner === 'Number');
  for (const entry of [...variants, ...records]) {
    if (!source.includes(`"${entry.id}"`)) {
      fail(`canonical_v3.ml omits required surface tag ${entry.id}`);
    }
  }
  return {
    variants: variants.length,
    records: records.length,
  };
}

function validateCanonicalNode(value, schema, seenTags, visit) {
  if (!Array.isArray(value) || typeof value[0] !== 'string') {
    fail(`canonical v3 value is not a tagged node: ${JSON.stringify(value)}`);
  }
  const tag = value[0];
  const fields = schema.nodeFieldOrder[tag];
  if (fields === undefined) fail(`canonical v3 uses unknown tag ${tag}`);
  if (value.length !== fields.length + 1) {
    fail(
      `${tag} has ${value.length - 1} fields; expected ${fields.length}`,
    );
  }
  seenTags.add(tag);
  visit?.(value);
  const children = value.slice(1);
  switch (tag) {
    case 'Boolean':
      if (typeof children[0] !== 'boolean') fail('Boolean payload is invalid');
      return;
    case 'Bytes':
      if (!/^(?:[0-9a-f]{2})*$/u.test(children[0])) {
        fail('Bytes payload is not lowercase hexadecimal');
      }
      return;
    case 'Integer':
      if (!/^(?:0|-[1-9][0-9]*|[1-9][0-9]*)$/u.test(children[0])) {
        fail('Integer payload is not canonical decimal');
      }
      return;
    case 'SourceSpan': {
      if (!/^(?:[0-9a-f]{2})*$/u.test(children[0]) ||
          children.slice(1).some(item =>
            !Number.isInteger(item) || item < 0)) {
        fail('SourceSpan payload is invalid');
      }
      return;
    }
    case 'Unit':
    case 'Option.None':
      return;
    case 'Sequence':
    case 'Product':
    case 'Set':
      if (!Array.isArray(children[0])) fail(`${tag} payload is not an array`);
      for (const child of children[0]) {
        validateCanonicalNode(child, schema, seenTags, visit);
      }
      return;
    case 'Map':
      if (!Array.isArray(children[0])) fail('Map payload is not an array');
      for (const entry of children[0]) {
        if (!Array.isArray(entry) || entry.length !== 2) {
          fail('Map entry is not a pair');
        }
        validateCanonicalNode(entry[0], schema, seenTags, visit);
        validateCanonicalNode(entry[1], schema, seenTags, visit);
      }
      return;
    case 'Definition':
      if (typeof children[0] !== 'string' ||
          !Number.isInteger(children[1]) || children[1] < 0) {
        fail('Definition identity is invalid');
      }
      validateCanonicalNode(children[2], schema, seenTags, visit);
      return;
    case 'Reference':
      if (typeof children[0] !== 'string' ||
          !Number.isInteger(children[1]) || children[1] < 0) {
        fail('Reference identity is invalid');
      }
      return;
    case 'DeBruijn':
      if (!Number.isInteger(children[0]) || children[0] < 0) {
        fail('DeBruijn index is invalid');
      }
      return;
    case 'GraphV3':
      for (const collection of children) {
        if (!Array.isArray(collection)) fail('GraphV3 field is not an array');
        for (const child of collection) {
          validateCanonicalNode(child, schema, seenTags, visit);
        }
      }
      return;
    default:
      for (const child of children) {
        validateCanonicalNode(child, schema, seenTags, visit);
      }
  }
}

function validateSurfaceRecord(
  record,
  relativePath,
  fixture,
  schema,
  profile,
  diagnostics,
) {
  const expectedKeys = [
    'schema',
    'semantic_profile_sha256',
    'diagnostic_contract_sha256',
    'fixture',
    'source_sha256',
    'scope',
    'stage',
    'canonical_sha256',
    'canonical',
  ];
  if (JSON.stringify(Object.keys(record)) !== JSON.stringify(expectedKeys)) {
    fail(`canonical v3 file record fields drift for ${relativePath}`);
  }
  const source = readFileSync(fixture);
  const expectedHeader = {
    schema: 3,
    semantic_profile_sha256: profile.semanticProfileSha256,
    diagnostic_contract_sha256: diagnostics.diagnosticContractSha256,
    fixture: relativePath,
    source_sha256: sha256(source),
    scope: 'file',
    stage: 'parsed-surface',
  };
  for (const [field, expected] of Object.entries(expectedHeader)) {
    if (record[field] !== expected) {
      fail(
        `${relativePath} ${field}: expected ${expected}, got ${record[field]}`,
      );
    }
  }
  const canonicalBytes = `${JSON.stringify(record.canonical)}\n`;
  if (record.canonical_sha256 !== sha256(canonicalBytes)) {
    fail(`${relativePath} canonical_sha256 does not bind its canonical value`);
  }
  const seenTags = new Set();
  let interfaceCount = 0;
  validateCanonicalNode(record.canonical, schema, seenTags, node => {
    if (node[0] === 'PtreeFull.full_unit_kind.FullModule' &&
        node[1]?.[0] === 'Option.Some') {
      interfaceCount += 1;
    }
  });
  if (record.canonical[0] !== 'PtreeFull.full_mlw_file.FullModules') {
    fail(`${relativePath} did not preserve its full module envelope`);
  }
  if (interfaceCount === 0) {
    fail(`${relativePath} did not preserve a module interface`);
  }
  return seenTags;
}

function sourceOffset(source, line, column) {
  let currentLine = 1;
  let offset = 0;
  while (currentLine < line) {
    const next = source.indexOf(0x0a, offset);
    if (next < 0) fail(`source has no line ${line}`);
    offset = next + 1;
    currentLine += 1;
  }
  return offset + column;
}

function validateDiagnostic(record, relativePath, entry, categoryByMoonKind) {
  const category = categoryByMoonKind.get(entry.moonbitKind);
  if (category === undefined) {
    fail(`diagnostic contract has no mapping for ${entry.moonbitKind}`);
  }
  const source = readFileSync(
    join(PROJECT_ROOT, 'fixtures', 'why3-1.7.2', relativePath),
  );
  const position = entry.why3Position;
  const location = position === null
    ? {
        start_byte: null,
        end_byte: null,
        start_line: null,
        start_column: null,
        end_line: null,
        end_column: null,
      }
    : {
        start_byte: sourceOffset(source, position[0], position[1]),
        end_byte: sourceOffset(source, position[0], position[2]),
        start_line: position[0],
        start_column: position[1],
        end_line: position[0],
        end_column: position[2],
      };
  const expected = {
    schema: 1,
    accepted: false,
    stage: 'parsing',
    severity: 'error',
    category,
    warning_code: null,
    relative_path_hex: Buffer.from(relativePath).toString('hex'),
    ...location,
  };
  if (JSON.stringify(record) !== JSON.stringify(expected)) {
    fail(
      `structured diagnostic mismatch for ${relativePath}\n` +
      `expected: ${JSON.stringify(expected)}\n` +
      `actual:   ${JSON.stringify(record)}`,
    );
  }
}

export function checkFullWhymlReference(options) {
  const targetFeatures = JSON.parse(readFileSync(TARGET_FEATURES_PATH, 'utf8'));
  const surfaceCoverage = checkSurfaceSourceCoverage(targetFeatures);
  const canonicalSchema = JSON.parse(
    readFileSync(CANONICAL_SCHEMA_V3_PATH, 'utf8'),
  );
  const semanticProfile = JSON.parse(
    readFileSync(SEMANTIC_PROFILE_V3_PATH, 'utf8'),
  );
  const runtime = prepareReferenceRuntime(options);
  const directory = mkdtempSync(join(tmpdir(), 'why3-full-reference-'));
  try {
    const source = join(directory, 'export_full_mlw.ml');
    const executable = join(directory, 'export-full-mlw');
    copyFileSync(
      CANONICAL_V3_PROFILE_SOURCE,
      join(directory, 'canonical_v3_profile.ml'),
    );
    copyFileSync(CANONICAL_V3_SOURCE, join(directory, 'canonical_v3.ml'));
    copyFileSync(EXPORTER_SOURCE, source);
    const referenceEnvironment = referenceRuntimeEnvironment(runtime);
    run('ocamlfind', [
      'ocamlopt',
      '-linkpkg',
      '-package',
      'why3,yojson,digestif.ocaml',
      '-o',
      executable,
      'canonical_v3_profile.ml',
      'canonical_v3.ml',
      'export_full_mlw.ml',
    ], { cwd: directory, env: referenceEnvironment });
    run('moon', ['build', '--target', 'native', 'cmd/pprint_whyml_sexp']);
    const manifestEntries = parserManifestEntries();
    const fixtures = manifestEntries.filter(item =>
      item.entry.lane === 'exact-main');
    const rejects = manifestEntries.filter(item => item.entry.lane === 'reject');
    if (fixtures.length !== 2) {
      fail(`expected 2 exact-main fixtures, got ${fixtures.length}`);
    }
    if (rejects.length !== 58) {
      fail(`expected 58 reject fixtures, got ${rejects.length}`);
    }
    const diagnosticContract = JSON.parse(
      readFileSync(DIAGNOSTIC_CONTRACT_PATH, 'utf8'),
    );
    const categoryByMoonKind = new Map(
      diagnosticContract.activeParserMappings.map(mapping => [
        mapping.moonbitKind,
        mapping.category,
      ]),
    );
    let comparedBytes = 0;
    let canonicalBytes = 0;
    const canonicalTags = new Set();
    for (const { fixture, relativePath } of fixtures) {
      const reference = run(executable, [
        '--stdlib',
        join(runtime.sourceRoot, 'stdlib'),
        '--file',
        fixture,
      ], { env: referenceEnvironment });
      const moon = run(PPRINT_WHYML_SEXP, ['--full', fixture]);
      compareExact(reference, moon, fixture);
      comparedBytes += Buffer.byteLength(reference);
      const accepted = parseCompactRecord(
        run(executable, [
          '--diagnostic',
          '--relative-path',
          relativePath,
          '--file',
          fixture,
        ], { env: referenceEnvironment }),
        `${relativePath} acceptance`,
      );
      if (JSON.stringify(accepted) !== '{"schema":1,"accepted":true}') {
        fail(`invalid structured acceptance for ${relativePath}`);
      }
      const canonicalOutput = run(executable, [
        '--canonical-v3',
        '--relative-path',
        relativePath,
        '--file',
        fixture,
      ], { env: referenceEnvironment });
      const repeatedCanonicalOutput = run(executable, [
        '--canonical-v3',
        '--relative-path',
        relativePath,
        '--file',
        fixture,
      ], { env: referenceEnvironment });
      if (canonicalOutput !== repeatedCanonicalOutput) {
        fail(`canonical v3 output is nondeterministic for ${relativePath}`);
      }
      const record = parseCompactRecord(
        canonicalOutput,
        `${relativePath} canonical v3 surface record`,
      );
      for (const tag of validateSurfaceRecord(
        record,
        relativePath,
        fixture,
        canonicalSchema,
        semanticProfile,
        diagnosticContract,
      )) {
        canonicalTags.add(tag);
      }
      canonicalBytes += Buffer.byteLength(canonicalOutput);
    }
    for (const { fixture, relativePath, entry } of rejects) {
      const diagnostic = parseCompactRecord(
        run(executable, [
          '--diagnostic',
          '--relative-path',
          relativePath,
          '--file',
          fixture,
        ], { env: referenceEnvironment }),
        `${relativePath} diagnostic`,
      );
      validateDiagnostic(
        diagnostic,
        relativePath,
        entry,
        categoryByMoonKind,
      );
    }
    process.stdout.write(
      `lossless WhyML reference: ${fixtures.length} exact-main fixtures, ` +
      `${comparedBytes} bytes exact; structured parser diagnostics ` +
      `${rejects.length}/${rejects.length}; canonical v3 surface ` +
      `${surfaceCoverage.variants} variants/${surfaceCoverage.records} ` +
      `records source-covered, ${canonicalTags.size} tags exercised, ` +
      `${canonicalBytes} bytes deterministic\n`,
    );
    return {
      fixtures: fixtures.length,
      bytes: comparedBytes,
      diagnostics: rejects.length,
      canonicalBytes,
      canonicalTags: canonicalTags.size,
    };
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

const isMain = process.argv[1] !== undefined &&
  pathToFileURL(resolve(process.argv[1])).href === import.meta.url;

if (isMain) {
  try {
    checkFullWhymlReference(parseArguments(process.argv.slice(2)));
  } catch (error) {
    process.stderr.write(`check_full_whyml_reference: ${error.message}\n`);
    process.exitCode = 1;
  }
}
