// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

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
    polymorphic: false,
  },
  {
    label: 'tests/vc/false-post.mlw',
    units: ['FalsePost'],
    goalCount: 1,
    polymorphic: false,
  },
  {
    label: 'tools/why3_oracle/fixtures/transform-polymorphism.mlw',
    units: ['LogicPolymorphism'],
    goalCount: 1,
    polymorphic: true,
  },
  {
    label: 'tools/why3_oracle/fixtures/transform-polymorphic-definition.mlw',
    units: ['LogicPolymorphicDefinition'],
    goalCount: 1,
    polymorphic: true,
  },
  {
    label: 'tools/why3_oracle/fixtures/transform-inductive.mlw',
    units: ['InductiveSnapshot'],
    goalCount: 1,
    polymorphic: true,
  },
  {
    label: 'tools/why3_oracle/fixtures/smt-identifiers.mlw',
    units: ['SmtIdentifiers'],
    goalCount: 1,
    polymorphic: true,
  },
  {
    label: 'tools/why3_oracle/fixtures/solver-outcomes.mlw',
    units: ['SolverOutcomes'],
    goalCount: 3,
    polymorphic: false,
  },
];

function fail(message) {
  throw new Error(message);
}

function readJson(path) {
  return JSON.parse(readFileSync(path, 'utf8'));
}

function assertEqual(actual, expected, label) {
  if (JSON.stringify(actual) !== JSON.stringify(expected)) {
    fail(
      `${label} mismatch:\nexpected ${JSON.stringify(expected)}\nactual   ${JSON.stringify(actual)}`,
    );
  }
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
    const tree = runChecked('git', ['-C', root, 'rev-parse', 'HEAD^{tree}']).trim();
    if (commit !== EXPECTED_WHY3_COMMIT || tree !== EXPECTED_WHY3_TREE) {
      fail(
        `expected ../why3 ${EXPECTED_WHY3_COMMIT}/${EXPECTED_WHY3_TREE}, got ${commit}/${tree}`,
      );
    }
  } else {
    const archive = realpathSync(options.why3Archive);
    const actualSha256 = sha256(readFileSync(archive));
    if (actualSha256 !== WHY3_SOURCE_ARCHIVE.sha256) {
      fail(
        `expected Why3 archive ${WHY3_SOURCE_ARCHIVE.sha256}, got ${actualSha256}`,
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
    fail('z3-static-profile-v1.json does not bind the selected source and trace patch');
  }
  const packageVersion = runChecked(
    'ocamlfind',
    ['query', '-format', '%v', 'why3'],
  ).trim();
  if (packageVersion !== WHY3_VERSION) {
    fail(`expected OCaml Why3 ${WHY3_VERSION}, got ${packageVersion}`);
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
    'export_z3_profile.ml',
    'export_transform_trace.ml',
  ]) {
    copyOracleSource(buildDirectory, name);
  }
  const snapshot = join(buildDirectory, 'export-snapshot');
  const z3Profile = join(buildDirectory, 'export-z3-profile');
  const trace = join(buildDirectory, 'export-transform-trace');
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
    z3Profile,
    'canonical_v2.cmx',
    'export_z3_profile.ml',
  ], { cwd: buildDirectory });
  runChecked('ocamlfind', [
    'ocamlopt',
    '-linkpkg',
    '-package',
    'why3,yojson,digestif.ocaml,unix',
    '-o',
    trace,
    'canonical_v2.cmx',
    'export_transform_trace.ml',
  ], { cwd: buildDirectory });
  return { snapshot, z3Profile, trace };
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

function runTrace(executable, why3Root, snapshot, fixture) {
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

function validateRawZ3Profile(executable, why3Root, snapshot, expected) {
  const output = runChecked(executable, [
    '--stdlib',
    join(why3Root, 'stdlib'),
    '--snapshot',
    snapshot,
  ], {
    cwd: PROJECT_ROOT,
    env: { ...process.env, LC_ALL: 'C' },
    maxBuffer: 128 * 1024 * 1024,
  });
  if (!output.endsWith('\n')) fail('Z3 profile exporter output has no final LF');
  const raw = JSON.parse(output);
  if (raw.schemaVersion !== 1) fail('raw Z3 profile schema version mismatch');
  for (const [key, value] of Object.entries(raw)) {
    if (key !== 'schemaVersion') {
      assertEqual(expected[key], value, `raw Z3 profile field ${key}`);
    }
  }
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
    fixture,
  ], {
    cwd: PROJECT_ROOT,
    env: { ...process.env, LC_ALL: 'C' },
    maxBuffer: 256 * 1024 * 1024,
  });
}

function parseRecords(output, label, fixture, semanticProfileSha256) {
  if (!output.endsWith('\n')) fail(`${label} output has no final LF`);
  const lines = output.slice(0, -1).split('\n');
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
        record.canonical_sha256 !== canonicalSha(record.canonical)) {
      fail(`${label} record ${index} has invalid portable metadata or hash`);
    }
    return record;
  });
  return { lines, records };
}

function sameGoal(left, right) {
  return left.unit_name_hex === right.unit_name_hex &&
    left.goal_name_hex === right.goal_name_hex &&
    left.goal_ordinal === right.goal_ordinal;
}

function validateTrace(trace, fixture, checkpointSequence) {
  const stride = checkpointSequence.length + 2;
  if (trace.records.length !== fixture.goalCount * stride) {
    fail(
      `${fixture.label}: expected ${fixture.goalCount * stride} oracle records, got ${trace.records.length}`,
    );
  }
  const rawLines = [];
  const checkpointLines = [];
  const preparedLines = [];
  for (let goal = 0; goal < fixture.goalCount; goal += 1) {
    const offset = goal * stride;
    const raw = trace.records[offset];
    if (raw.stage !== 'raw-task') {
      fail(`${fixture.label} goal ${goal}: trace does not start with raw-task`);
    }
    rawLines.push(trace.lines[offset]);
    for (let index = 0; index < checkpointSequence.length; index += 1) {
      const record = trace.records[offset + index + 1];
      if (!sameGoal(raw, record) || record.stage !== checkpointSequence[index]) {
        fail(
          `${fixture.label} goal ${goal}: expected checkpoint ${checkpointSequence[index]} at index ${index}`,
        );
      }
      checkpointLines.push(trace.lines[offset + index + 1]);
    }
    const finalCheckpoint = trace.records[offset + checkpointSequence.length];
    const prepared = trace.records[offset + checkpointSequence.length + 1];
    if (!sameGoal(raw, prepared) || prepared.stage !== 'prepared-task' ||
        finalCheckpoint.stage !== 'encoding_smt_if_poly' ||
        finalCheckpoint.canonical_sha256 !== prepared.canonical_sha256 ||
        JSON.stringify(finalCheckpoint.canonical) !== JSON.stringify(prepared.canonical)) {
      fail(`${fixture.label} goal ${goal}: traced and ordinary prepared tasks differ`);
    }
    preparedLines.push(trace.lines[offset + checkpointSequence.length + 1]);
  }
  return {
    raw: `${rawLines.join('\n')}\n`,
    checkpoints: `${checkpointLines.join('\n')}\n`,
    prepared: `${preparedLines.join('\n')}\n`,
  };
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
  let debugHint = '';
  const debugDirectory = process.env.WHY3_DIFFERENTIAL_DEBUG_DIR;
  if (debugDirectory !== undefined && debugDirectory !== '') {
    mkdirSync(debugDirectory, { recursive: true });
    const stem = sha256(label).slice(0, 16);
    const expectedPath = join(debugDirectory, `${stem}.expected.ndjson`);
    const actualPath = join(debugDirectory, `${stem}.actual.ndjson`);
    writeFileSync(expectedPath, expected);
    writeFileSync(actualPath, actual);
    debugHint = `; wrote ${expectedPath} and ${actualPath}`;
  }
  fail(
    `${label} differs at byte ${offset}, line ${line}; expected ${Buffer.byteLength(expected)} bytes, got ${Buffer.byteLength(actual)}${debugHint}`,
  );
}

function main(argv = process.argv.slice(2)) {
  const options = parseArguments(argv);
  const driver = readJson(DRIVER_CONTRACT);
  const semanticProfile = readJson(SEMANTIC_PROFILE);
  const z3Profile = readJson(Z3_PROFILE);
  if (semanticProfile.semanticProfileSha256 === undefined) {
    fail('semantic-profile-v1.json has no semantic profile hash');
  }
  const buildDirectory = mkdtempSync(join(tmpdir(), 'why3-transform-differential-'));
  try {
    const why3Root = verifyWhy3(options, z3Profile, buildDirectory);
    const executables = compileOracles(buildDirectory);
    const snapshot = join(buildDirectory, 'snapshot.json');
    exportSnapshot(executables.snapshot, snapshot, why3Root, driver);
    validateRawZ3Profile(
      executables.z3Profile,
      why3Root,
      snapshot,
      z3Profile,
    );
    let checkpointRecords = 0;
    for (const fixture of FIXTURES) {
      const checkpointSequence = fixture.polymorphic
        ? z3Profile.tracePatch.checkpointSequences.polymorphic
        : z3Profile.tracePatch.checkpointSequences.monomorphic;
      const oracle = parseRecords(
        runTrace(executables.trace, why3Root, snapshot, fixture),
        `Why3 ${fixture.label}`,
        fixture,
        semanticProfile.semanticProfileSha256,
      );
      const expected = validateTrace(oracle, fixture, checkpointSequence);
      assertSameOutput(
        runMoon('raw-task', fixture.label),
        expected.raw,
        `${fixture.label} raw-task`,
      );
      assertSameOutput(
        runMoon('transform-checkpoints', fixture.label),
        expected.checkpoints,
        `${fixture.label} transform checkpoints`,
      );
      assertSameOutput(
        runMoon('prepared-task', fixture.label),
        expected.prepared,
        `${fixture.label} prepared tasks`,
      );
      checkpointRecords += fixture.goalCount * checkpointSequence.length;
      process.stdout.write(
        `run_transform_differential: ${fixture.label} ` +
        `${fixture.goalCount} goal(s), ${checkpointSequence.length} checkpoints and prepared tasks exact\n`,
      );
    }
    process.stdout.write(
      `run_transform_differential: ${checkpointRecords} checkpoint records exact; ` +
      `Why3 ${WHY3_VERSION} ${EXPECTED_WHY3_COMMIT}\n`,
    );
  } finally {
    rmSync(buildDirectory, { recursive: true, force: true });
  }
}

try {
  main();
} catch (error) {
  process.stderr.write(`run_transform_differential: ${error.message}\n`);
  process.exitCode = 1;
}
