// SPDX-License-Identifier: LGPL-2.1-only WITH OCAML-LGPL-linking-exception

import { spawnSync } from 'node:child_process';
import {
  mkdirSync,
  mkdtempSync,
  readFileSync,
  realpathSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  EXPECTED_WHY3_COMMIT,
  EXPECTED_WHY3_TREE,
  PROGRAM_ROOTS,
  WHY3_SOURCE_ARCHIVE,
  canonicalSha,
  runChecked,
  sha256,
} from './export_driver_inventory.mjs';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const DRIVER_CONTRACT = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'driver-closure-v1.json',
);
const SEMANTIC_PROFILE = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'semantic-profile-v1.json',
);
const Z3_PROFILE = join(
  PROJECT_ROOT,
  'prover',
  'z3',
  'z3-static-profile-v1.json',
);
const TRACE_PATCH = join(SCRIPT_DIRECTORY, 'patches', 'driver-trace.patch');
const WHY3_VERSION = '1.7.2';
const Z3_VERSION_LINE = 'Z3 version 4.8.12 - 64 bit';

const FIXTURES = [
  {
    label: 'tools/why3_oracle/fixtures/mvp.mlw',
    units: [
      'LogicCore',
      'LogicReal',
      'LogicPolymorphism',
      'LogicQuantifiers',
      'UnitMvp',
      'NamespaceMvp',
      'MultiFirst',
      'MultiSecond',
      'Abs',
      'RoutineCall',
      'AssertAssume',
      'ProgramReal',
    ],
    goalCount: 16,
  },
  {
    label: 'tests/vc/false-post.mlw',
    units: ['FalsePost'],
    goalCount: 1,
  },
  {
    label: 'tools/why3_oracle/fixtures/transform-polymorphism.mlw',
    units: ['LogicPolymorphism'],
    goalCount: 1,
  },
  {
    label: 'tools/why3_oracle/fixtures/transform-polymorphic-definition.mlw',
    units: ['LogicPolymorphicDefinition'],
    goalCount: 1,
  },
  {
    label: 'tools/why3_oracle/fixtures/transform-inductive.mlw',
    units: ['InductiveSnapshot'],
    goalCount: 1,
  },
  {
    label: 'tools/why3_oracle/fixtures/smt-identifiers.mlw',
    units: ['SmtIdentifiers'],
    goalCount: 1,
    identifierSafety: true,
  },
  {
    label: 'tools/why3_oracle/fixtures/solver-outcomes.mlw',
    units: ['SolverOutcomes'],
    goalCount: 3,
  },
];

function fail(message) {
  throw new Error(message);
}

function readJson(path) {
  return JSON.parse(readFileSync(path, 'utf8'));
}

function parseArguments(argv) {
  let why3Root = resolve(PROJECT_ROOT, '..', 'why3');
  let why3Archive = null;
  let explicitRoot = false;
  for (let index = 0; index < argv.length; index += 1) {
    if ((argv[index] !== '--why3-root' && argv[index] !== '--why3-archive') ||
        argv[index + 1] === undefined) {
      fail(`unknown or incomplete argument: ${argv[index]}`);
    }
    if (argv[index] === '--why3-root') {
      why3Root = resolve(argv[index + 1]);
      explicitRoot = true;
    } else {
      why3Archive = resolve(argv[index + 1]);
    }
    index += 1;
  }
  if (explicitRoot && why3Archive !== null) {
    fail('--why3-root and --why3-archive are mutually exclusive');
  }
  return { why3Root, why3Archive };
}

function verifyWhy3(options, profile, buildDirectory) {
  let root;
  if (options.why3Archive === null) {
    root = realpathSync(options.why3Root);
    const commit = runChecked('git', ['-C', root, 'rev-parse', 'HEAD']).trim();
    const tree = runChecked(
      'git',
      ['-C', root, 'rev-parse', 'HEAD^{tree}'],
    ).trim();
    if (commit !== EXPECTED_WHY3_COMMIT || tree !== EXPECTED_WHY3_TREE) {
      fail(
        `expected ../why3 ${EXPECTED_WHY3_COMMIT}/${EXPECTED_WHY3_TREE}, ` +
        `got ${commit}/${tree}`,
      );
    }
  } else {
    const archive = realpathSync(options.why3Archive);
    const actualSha256 = sha256(readFileSync(archive));
    if (actualSha256 !== WHY3_SOURCE_ARCHIVE.sha256) {
      fail(
        `expected Why3 archive ${WHY3_SOURCE_ARCHIVE.sha256}, ` +
        `got ${actualSha256}`,
      );
    }
    root = join(buildDirectory, 'why3-source');
    mkdirSync(root);
    runChecked('tar', [
      '-xzf',
      archive,
      '--strip-components=1',
      '-C',
      root,
    ]);
  }
  runChecked('git', ['-C', root, 'apply', '--check', TRACE_PATCH]);
  const patchSha256 = sha256(readFileSync(TRACE_PATCH));
  if (profile.why3?.commit !== EXPECTED_WHY3_COMMIT ||
      profile.why3?.tree !== EXPECTED_WHY3_TREE ||
      profile.tracePatch?.targetWhy3Commit !== EXPECTED_WHY3_COMMIT ||
      profile.evidence?.tracePatchSha256 !== patchSha256) {
    fail('z3-static-profile-v1.json does not bind the source and trace patch');
  }
  const packageVersion = runChecked(
    'ocamlfind',
    ['query', '-format', '%v', 'why3'],
  ).trim();
  if (packageVersion !== WHY3_VERSION) {
    fail(`expected OCaml Why3 ${WHY3_VERSION}, got ${packageVersion}`);
  }
  const z3Version = runChecked('z3', ['--version']).trim();
  if (z3Version !== Z3_VERSION_LINE) {
    fail(`expected ${Z3_VERSION_LINE}, got ${z3Version}`);
  }
  return root;
}

function copyOracleSource(buildDirectory, name) {
  writeFileSync(
    join(buildDirectory, name),
    readFileSync(join(SCRIPT_DIRECTORY, name)),
  );
}

function compileOracles(buildDirectory) {
  for (const name of [
    'export_snapshot.ml',
    'canonical_v2.ml',
    'export_smt_trace.ml',
  ]) {
    copyOracleSource(buildDirectory, name);
  }
  const snapshot = join(buildDirectory, 'export-snapshot');
  const smtTrace = join(buildDirectory, 'export-smt-trace');
  runChecked('ocamlfind', [
    'ocamlopt',
    '-linkpkg',
    '-package',
    'why3,yojson,unix',
    '-o',
    snapshot,
    'export_snapshot.ml',
  ], { cwd: buildDirectory });
  runChecked('ocamlfind', [
    'ocamlopt',
    '-package',
    'why3,yojson,digestif.ocaml,unix',
    '-c',
    'canonical_v2.ml',
  ], { cwd: buildDirectory });
  runChecked('ocamlfind', [
    'ocamlopt',
    '-linkpkg',
    '-package',
    'why3,yojson,digestif.ocaml,unix',
    '-o',
    smtTrace,
    'canonical_v2.cmx',
    'export_smt_trace.ml',
  ], { cwd: buildDirectory });
  return { snapshot, smtTrace };
}

function exportSnapshot(executable, outputPath, why3Root, driver) {
  const argv = ['--stdlib', join(why3Root, 'stdlib')];
  for (const theory of driver.driver.theoryRoots) {
    argv.push('--theory', theory);
  }
  for (const pmodule of PROGRAM_ROOTS) argv.push('--module', pmodule);
  const output = runChecked(executable, argv, {
    cwd: PROJECT_ROOT,
    env: { ...process.env, LC_ALL: 'C' },
    maxBuffer: 128 * 1024 * 1024,
  });
  if (!output.endsWith('\n')) fail('snapshot exporter output has no final LF');
  writeFileSync(outputPath, output);
}

function runOracle(executable, why3Root, snapshot, fixture) {
  const argv = [
    '--why3-root',
    why3Root,
    '--snapshot',
    snapshot,
    '--fixture',
    fixture.label,
    '--file',
    join(PROJECT_ROOT, fixture.label),
  ];
  for (const unit of fixture.units) argv.push('--unit', unit);
  return runChecked(executable, argv, {
    cwd: PROJECT_ROOT,
    env: { ...process.env, LC_ALL: 'C' },
    maxBuffer: 256 * 1024 * 1024,
  });
}

function runMoon(stage, fixture) {
  return runChecked('moon', [
    'run',
    '--target',
    'native',
    'cmd/elab_canonical',
    '--',
    '--stage',
    stage,
    fixture.label,
  ], {
    cwd: PROJECT_ROOT,
    env: { ...process.env, LC_ALL: 'C' },
    maxBuffer: 256 * 1024 * 1024,
  });
}

function parseCanonicalRecords(output, label, fixture, semanticProfileSha256) {
  if (!output.endsWith('\n')) fail(`${label} output has no final LF`);
  const lines = output.slice(0, -1).split('\n');
  if (lines.length !== fixture.goalCount) {
    fail(`${label}: expected ${fixture.goalCount} records, got ${lines.length}`);
  }
  const sourceSha256 = sha256(readFileSync(join(PROJECT_ROOT, fixture.label)));
  const records = lines.map((line, index) => {
    let record;
    try {
      record = JSON.parse(line);
    } catch (error) {
      fail(`${label} record ${index} is not JSON: ${error.message}`);
    }
    if (JSON.stringify(record) !== line) {
      fail(`${label} record ${index} is not compact canonical JSON`);
    }
    if (record.schema !== 2 ||
        record.semantic_profile_sha256 !== semanticProfileSha256 ||
        record.fixture !== fixture.label ||
        record.source_sha256 !== sourceSha256 ||
        record.scope !== 'goal' ||
        record.unit_kind !== 'theory' ||
        record.stage !== 'smt-token-stream' ||
        record.canonical_sha256 !== canonicalSha(record.canonical)) {
      fail(`${label} record ${index} has invalid portable metadata or hash`);
    }
    return record;
  });
  return { lines, records };
}

function parseQueryRecords(output, fixture, oracleRecords) {
  if (!output.endsWith('\n')) {
    fail(`${fixture.label} smt-query output has no final LF`);
  }
  const lines = output.slice(0, -1).split('\n');
  if (lines.length !== fixture.goalCount) {
    fail(
      `${fixture.label}: expected ${fixture.goalCount} raw queries, ` +
      `got ${lines.length}`,
    );
  }
  return lines.map((line, index) => {
    let record;
    try {
      record = JSON.parse(line);
    } catch (error) {
      fail(`${fixture.label} raw query ${index} is not JSON: ${error.message}`);
    }
    if (JSON.stringify(record) !== line ||
        !/^[0-9a-f]*$/.test(record.smt_hex) ||
        record.smt_hex.length % 2 !== 0) {
      fail(`${fixture.label} raw query ${index} is not compact valid hex JSON`);
    }
    const oracle = oracleRecords[index];
    if (record.unit_name_hex !== oracle.unit_name_hex ||
        record.goal_name_hex !== oracle.goal_name_hex ||
        record.goal_ordinal !== oracle.goal_ordinal) {
      fail(`${fixture.label} raw query ${index} goal identity mismatch`);
    }
    return Buffer.from(record.smt_hex, 'hex');
  });
}

function firstByteDifference(left, right) {
  const leftBytes = Buffer.from(left, 'utf8');
  const rightBytes = Buffer.from(right, 'utf8');
  const limit = Math.min(leftBytes.length, rightBytes.length);
  let offset = 0;
  while (offset < limit && leftBytes[offset] === rightBytes[offset]) offset += 1;
  return offset;
}

function assertSameOutput(actual, expected, label) {
  if (actual === expected) return;
  const offset = firstByteDifference(actual, expected);
  const line = Buffer.from(expected.slice(0, offset), 'utf8')
    .toString('utf8')
    .split('\n').length;
  fail(
    `${label} differs at byte ${offset}, line ${line}; ` +
    `expected ${Buffer.byteLength(expected)} bytes, ` +
    `got ${Buffer.byteLength(actual)}`,
  );
}

function decodeTokens(record) {
  if (record.canonical?.[0] !== 'SmtTokenStreamV1' ||
      !Array.isArray(record.canonical?.[1])) {
    fail('SMT canonical payload is not SmtTokenStreamV1');
  }
  return record.canonical[1].map(token => Buffer.from(token, 'hex').toString());
}

function validateIdentifierSafety(record) {
  const tokens = decodeTokens(record);
  for (const expected of [
    'probe',
    'select1',
    'store1',
    'sort1',
    'witness1',
    'generated_0',
    'generated_1',
  ]) {
    if (!tokens.includes(expected)) {
      fail(`identifier-safety stream lost exact user token ${expected}`);
    }
  }
  const generated = tokens.filter(token => token.startsWith('$generated['));
  if (generated.length === 0 ||
      !generated.some(token => token.startsWith('$generated[encoding_smt_if_poly:guards]')) ||
      !generated.some(token => token.startsWith('$generated[discriminate_if_poly]'))) {
    fail('identifier-safety stream did not exercise generated-name stages');
  }
  if (tokens.includes('select') || tokens.includes('store') ||
      tokens.includes('sort') || tokens.includes('witness')) {
    fail('reserved/colliding user identifiers were not allocated deterministically');
  }
}

function parseOnlyWithZ3(query, label) {
  const terminal = Buffer.from('(check-sat)\n');
  if (query.length < terminal.length ||
      !query.subarray(query.length - terminal.length).equals(terminal)) {
    fail(`${label}: query does not end in one check-sat command`);
  }
  const parseOnly = Buffer.concat([
    query.subarray(0, query.length - terminal.length),
    Buffer.from('(exit)\n'),
  ]);
  const result = spawnSync('z3', ['-smt2', '-in'], {
    cwd: PROJECT_ROOT,
    env: { ...process.env, LC_ALL: 'C' },
    input: parseOnly,
    encoding: 'utf8',
    timeout: 10_000,
    maxBuffer: 16 * 1024 * 1024,
  });
  if (result.error !== undefined || result.status !== 0 ||
      result.signal !== null ||
      result.stdout.includes('(error') || result.stderr.includes('(error')) {
    fail(
      `${label}: fixed Z3 parse failed: ` +
      `${result.error?.message ?? ''}${result.stdout}${result.stderr}`,
    );
  }
}

function main(argv = process.argv.slice(2)) {
  const options = parseArguments(argv);
  const driver = readJson(DRIVER_CONTRACT);
  const semanticProfile = readJson(SEMANTIC_PROFILE);
  const z3Profile = readJson(Z3_PROFILE);
  if (semanticProfile.semanticProfileSha256 === undefined) {
    fail('semantic-profile-v1.json has no semantic profile hash');
  }
  const buildDirectory = mkdtempSync(join(tmpdir(), 'why3-smt-differential-'));
  try {
    const why3Root = verifyWhy3(options, z3Profile, buildDirectory);
    const executables = compileOracles(buildDirectory);
    const snapshot = join(buildDirectory, 'snapshot.json');
    exportSnapshot(executables.snapshot, snapshot, why3Root, driver);
    let queryCount = 0;
    for (const fixture of FIXTURES) {
      const oracleOutput = runOracle(
        executables.smtTrace,
        why3Root,
        snapshot,
        fixture,
      );
      const oracle = parseCanonicalRecords(
        oracleOutput,
        `Why3 ${fixture.label}`,
        fixture,
        semanticProfile.semanticProfileSha256,
      );
      const moonOutput = runMoon('smt-token-stream', fixture);
      parseCanonicalRecords(
        moonOutput,
        `MoonBit ${fixture.label}`,
        fixture,
        semanticProfile.semanticProfileSha256,
      );
      assertSameOutput(
        moonOutput,
        oracleOutput,
        `${fixture.label} normalized SMT token stream`,
      );
      if (fixture.identifierSafety) validateIdentifierSafety(oracle.records[0]);
      const queries = parseQueryRecords(
        runMoon('smt-query', fixture),
        fixture,
        oracle.records,
      );
      queries.forEach((query, index) => {
        parseOnlyWithZ3(query, `${fixture.label} goal ${index}`);
      });
      queryCount += queries.length;
      process.stdout.write(
        `run_smt_differential: ${fixture.label} ` +
        `${queries.length} query token stream(s) exact and Z3-parseable\n`,
      );
    }
    process.stdout.write(
      `run_smt_differential: ${queryCount} query token stream(s) exact; ` +
      `Why3 ${WHY3_VERSION} ${EXPECTED_WHY3_COMMIT}; Z3 4.8.12\n`,
    );
  } finally {
    rmSync(buildDirectory, { recursive: true, force: true });
  }
}

try {
  main();
} catch (error) {
  process.stderr.write(`run_smt_differential: ${error.message}\n`);
  process.exitCode = 1;
}
