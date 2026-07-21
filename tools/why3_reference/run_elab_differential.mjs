// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { spawnSync } from 'node:child_process';
import {
  mkdirSync,
  mkdtempSync,
  readFileSync,
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
  canonicalSha,
  runChecked,
  sha256,
} from './export_driver_inventory.mjs';
import {
  prepareReferenceRuntime,
  referenceRuntimeEnvironment,
} from './reference_runtime.mjs';

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
const PR_CORPUS = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'pr-corpus-v1.json',
);
const WHY3_VERSION = '1.7.2';

const PURE_UNITS = [
  ['LogicCore', ['implication_identity', 'ordinary_attribute', 'bool_int_real']],
  ['LogicReal', ['real_order']],
  ['LogicPolymorphism', ['identity_int', 'identity_bool']],
  ['LogicQuantifiers', ['quantified_trigger']],
  ['UnitMvp', ['unit_roundtrip']],
  ['NamespaceMvp', ['qualified_lookup']],
  ['MultiFirst', ['first_goal']],
  ['MultiSecond', ['second_goal']],
];

const PROGRAM_GOALS = [
  ['Abs', ["abs'vc"]],
  ['RoutineCall', ["increment'vc", "increment_twice'vc"]],
  ['AssertAssume', ["checked_identity'vc"]],
  ['ProgramReal', ["add_zero'vc"]],
];

const FIXTURES = [
  {
    label: 'tools/why3_reference/fixtures/mvp.mlw',
    theories: PURE_UNITS,
    modules: PROGRAM_GOALS,
  },
  {
    label: 'tests/vc/false-post.mlw',
    theories: [],
    modules: [['FalsePost', ["identity'vc"]]],
  },
  {
    label: 'tools/why3_reference/fixtures/transform-polymorphism.mlw',
    theories: [['LogicPolymorphism', ['free_type_variable']]],
    modules: [],
  },
  {
    label: 'tools/why3_reference/fixtures/transform-polymorphic-definition.mlw',
    theories: [['LogicPolymorphicDefinition', ['reflexive_goal']]],
    modules: [],
  },
  {
    label: 'tools/why3_reference/fixtures/transform-inductive.mlw',
    theories: [['InductiveSnapshot', ['well_founded_smoke']]],
    modules: [],
  },
  {
    label: 'tools/why3_reference/fixtures/smt-identifiers.mlw',
    theories: [['SmtIdentifiers', ['reserved_and_collision']]],
    modules: [],
  },
  {
    label: 'tools/why3_reference/fixtures/solver-outcomes.mlw',
    theories: [[
      'SolverOutcomes',
      ['unsat_valid', 'sat_unknown', 'solver_unknown'],
    ]],
    modules: [],
  },
];

const NEGATIVE_IDS = [
  'typing.arity-mismatch',
  'typing.occurs-check',
  'typing.type-mismatch',
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

function hex(value) {
  return Buffer.from(value, 'utf8').toString('hex');
}

function observedProcess(command, argv, options = {}) {
  const result = spawnSync(command, argv, {
    cwd: options.cwd ?? PROJECT_ROOT,
    encoding: 'utf8',
    env: options.env ?? process.env,
    maxBuffer: options.maxBuffer ?? 64 * 1024 * 1024,
    shell: false,
  });
  if (result.error && result.error.code !== 'EPERM') throw result.error;
  if (result.signal !== null) {
    fail(`${command} terminated by ${result.signal}`);
  }
  return {
    status: result.status,
    stdout: result.stdout ?? '',
    stderr: result.stderr ?? '',
  };
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

function verifyWhy3SourceAndTools(driver, options) {
  const runtime = prepareReferenceRuntime(options);
  if (driver.why3.commit !== EXPECTED_WHY3_COMMIT ||
      driver.why3.tree !== EXPECTED_WHY3_TREE) {
    fail('driver-closure-v1.json does not describe the selected ../why3 tree');
  }
  const ocamlVersion = runChecked(
    'ocamlfind',
    ['query', '-format', '%v', 'why3'],
    { env: referenceRuntimeEnvironment(runtime) },
  ).trim();
  if (ocamlVersion !== WHY3_VERSION) {
    fail(`expected OCaml Why3 ${WHY3_VERSION}, got ${ocamlVersion}`);
  }
  const cliVersion = runChecked('why3', ['--version']).trim();
  if (!new RegExp(`(?:^|[^0-9])${WHY3_VERSION.replaceAll('.', '\\.')}(?:$|[^0-9])`, 'u')
    .test(cliVersion)) {
    fail(`expected Why3 CLI ${WHY3_VERSION}, got ${JSON.stringify(cliVersion)}`);
  }
  return runtime;
}

function copyReferenceSource(buildDirectory, name) {
  writeFileSync(
    join(buildDirectory, name),
    readFileSync(join(SCRIPT_DIRECTORY, name)),
  );
}

function compileReferences(buildDirectory, runtime) {
  const env = referenceRuntimeEnvironment(runtime);
  for (const name of [
    'export_snapshot.ml',
    'canonical_v2.ml',
    'export_elab_typed.ml',
    'export_elab_raw.ml',
  ]) {
    copyReferenceSource(buildDirectory, name);
  }

  const snapshot = join(buildDirectory, 'export-snapshot');
  const typed = join(buildDirectory, 'export-elab-typed');
  const raw = join(buildDirectory, 'export-elab-raw');
  runChecked('ocamlfind', [
    'ocamlopt',
    '-linkpkg',
    '-package',
    'why3,yojson,unix',
    '-o',
    snapshot,
    'export_snapshot.ml',
  ], { cwd: buildDirectory, env });
  runChecked('ocamlfind', [
    'ocamlopt',
    '-package',
    'why3,yojson,digestif.ocaml,unix',
    '-c',
    'canonical_v2.ml',
  ], { cwd: buildDirectory, env });
  for (const [output, source] of [
    [typed, 'export_elab_typed.ml'],
    [raw, 'export_elab_raw.ml'],
  ]) {
    runChecked('ocamlfind', [
      'ocamlopt',
      '-linkpkg',
      '-package',
      'why3,yojson,digestif.ocaml,unix',
      '-o',
      output,
      'canonical_v2.cmx',
      source,
    ], { cwd: buildDirectory, env });
  }
  return { snapshot, typed, raw };
}

function exportSnapshot(executable, outputPath, why3Root, driver) {
  assertEqual(
    driver.semanticSnapshot.userVisibleProgramRoots,
    PROGRAM_ROOTS,
    'program roots',
  );
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
  const snapshot = JSON.parse(output);
  assertEqual(
    snapshot.roots.theories.map(entry => entry.requested),
    driver.driver.theoryRoots,
    'snapshot theory roots',
  );
  assertEqual(
    snapshot.roots.modules.map(entry => entry.requested),
    PROGRAM_ROOTS,
    'snapshot program roots',
  );
  writeFileSync(outputPath, output);
}

function referenceArguments(why3Root, snapshot, fixture, file) {
  const argv = [
    '--stdlib',
    join(why3Root, 'stdlib'),
    '--snapshot',
    snapshot,
    '--fixture',
    fixture.label,
    '--file',
    file,
  ];
  for (const [unit] of fixture.theories) argv.push('--unit', unit);
  for (const [unit] of fixture.modules) argv.push('--module', unit);
  return argv;
}

function runReference(executable, why3Root, snapshot, fixture, file) {
  return runChecked(
    executable,
    referenceArguments(why3Root, snapshot, fixture, file),
    {
      cwd: PROJECT_ROOT,
      env: { ...process.env, LC_ALL: 'C' },
      maxBuffer: 128 * 1024 * 1024,
    },
  );
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
    maxBuffer: 128 * 1024 * 1024,
  });
}

function expectedRecords(stage, fixture) {
  if (stage === 'typed-semantic') {
    return [
      ...fixture.theories.map(([unit]) => ({
        unit,
        kind: 'theory',
        recordStage: 'typed-semantic',
        canonicalTag: 'Theory',
      })),
      ...fixture.modules.map(([unit]) => ({
        unit,
        kind: 'module',
        recordStage: 'typed-program',
        canonicalTag: 'Pmodule',
      })),
    ];
  }
  return [...fixture.theories, ...fixture.modules].flatMap(([unit, goals]) =>
    goals.map((goal, ordinal) => ({ unit, goal, ordinal })));
}

function validateRecords(
  output,
  stage,
  fixture,
  sourceSha256,
  semanticProfileSha256,
  producer,
) {
  if (!output.endsWith('\n')) fail(`${producer} ${stage} output has no final LF`);
  const lines = output.slice(0, -1).split('\n');
  const expected = expectedRecords(stage, fixture);
  if (lines.length !== expected.length) {
    fail(`${producer} ${stage}: expected ${expected.length} records, got ${lines.length}`);
  }
  const typedKeys = [
    'schema',
    'semantic_profile_sha256',
    'fixture',
    'source_sha256',
    'scope',
    'unit_kind',
    'unit_name_hex',
    'stage',
    'canonical_sha256',
    'canonical',
  ];
  const rawKeys = [
    'schema',
    'semantic_profile_sha256',
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
  ];
  return lines.map((line, index) => {
    let record;
    try {
      record = JSON.parse(line);
    } catch (error) {
      fail(`${producer} ${stage} record ${index} is not JSON: ${error.message}`);
    }
    if (JSON.stringify(record) !== line) {
      fail(`${producer} ${stage} record ${index} is not compact canonical JSON`);
    }
    assertEqual(
      Object.keys(record),
      stage === 'typed-semantic' ? typedKeys : rawKeys,
      `${producer} ${stage} record ${index} field order`,
    );
    const wanted = expected[index];
    if (record.schema !== 2 ||
        record.semantic_profile_sha256 !== semanticProfileSha256 ||
        record.fixture !== fixture.label ||
        record.source_sha256 !== sourceSha256 ||
        record.unit_kind !== (wanted.kind ?? 'theory') ||
        record.unit_name_hex !== hex(wanted.unit) ||
        record.stage !== (wanted.recordStage ?? stage)) {
      fail(`${producer} ${stage} record ${index} has invalid portable metadata`);
    }
    if (stage === 'typed-semantic') {
      if (record.scope !== 'unit' ||
          record.canonical?.[0] !== wanted.canonicalTag) {
        fail(`${producer} ${stage} record ${index} is not the expected typed unit`);
      }
    } else if (record.scope !== 'goal' ||
               record.goal_name_hex !== hex(wanted.goal) ||
               record.goal_ordinal !== wanted.ordinal ||
               record.canonical?.[0] !== 'Task') {
      fail(`${producer} ${stage} record ${index} is not the expected raw Task`);
    }
    const digest = canonicalSha(record.canonical);
    if (record.canonical_sha256 !== digest) {
      fail(
        `${producer} ${stage} record ${index} canonical hash: expected ${digest}, got ${record.canonical_sha256}`,
      );
    }
    return record;
  });
}

function structuralDifference(left, right, path = '$') {
  if (Object.is(left, right)) return null;
  if (Array.isArray(left) || Array.isArray(right)) {
    if (!Array.isArray(left) || !Array.isArray(right)) {
      return { path, left, right };
    }
    if (left.length !== right.length) {
      const childTags = values => values.map(value =>
        Array.isArray(value) && typeof value[0] === 'string'
          ? value[0]
          : typeof value,
      );
      return {
        path: `${path}.length`,
        left: { length: left.length, childTags: childTags(left) },
        right: { length: right.length, childTags: childTags(right) },
      };
    }
    for (let index = 0; index < left.length; index += 1) {
      const difference = structuralDifference(
        left[index],
        right[index],
        `${path}[${index}]`,
      );
      if (difference !== null) return difference;
    }
    return null;
  }
  if (left !== null && right !== null &&
      typeof left === 'object' && typeof right === 'object') {
    const leftKeys = Object.keys(left);
    const rightKeys = Object.keys(right);
    if (JSON.stringify(leftKeys) !== JSON.stringify(rightKeys)) {
      return { path: `${path}.[keys]`, left: leftKeys, right: rightKeys };
    }
    for (const key of leftKeys) {
      const difference = structuralDifference(
        left[key],
        right[key],
        `${path}.${key}`,
      );
      if (difference !== null) return difference;
    }
    return null;
  }
  return { path, left, right };
}

function firstByteDifference(left, right) {
  const leftBytes = Buffer.from(left, 'utf8');
  const rightBytes = Buffer.from(right, 'utf8');
  const limit = Math.min(leftBytes.length, rightBytes.length);
  let offset = 0;
  while (offset < limit && leftBytes[offset] === rightBytes[offset]) offset += 1;
  return offset;
}

function assertSameOutput(left, right, leftLabel, rightLabel) {
  if (left === right) return;
  const leftLines = left.trimEnd().split('\n');
  const rightLines = right.trimEnd().split('\n');
  const recordCount = Math.min(leftLines.length, rightLines.length);
  let record = 0;
  while (record < recordCount && leftLines[record] === rightLines[record]) {
    record += 1;
  }
  let detail = 'record counts differ';
  if (record < recordCount) {
    try {
      const leftRecord = JSON.parse(leftLines[record]);
      const rightRecord = JSON.parse(rightLines[record]);
      const canonicalDifference = structuralDifference(
        leftRecord.canonical,
        rightRecord.canonical,
        '$.canonical',
      );
      const difference = canonicalDifference ?? structuralDifference(
        leftRecord,
        rightRecord,
      );
      if (difference !== null) {
        detail = `${difference.path}: ${JSON.stringify(difference.left)} != ${JSON.stringify(difference.right)}`;
      }
    } catch {
      detail = 'the first differing record is not valid JSON';
    }
  }
  fail(
    `${leftLabel} and ${rightLabel} differ at byte ${firstByteDifference(left, right)}, record ${record}, ${detail}`,
  );
}

function why3Command(why3Root, config, mode, fixture) {
  return observedProcess('why3', [
    '-C',
    config,
    '--no-load-default-plugins',
    '--no-stdlib',
    '-L',
    join(why3Root, 'stdlib'),
    'prove',
    mode,
    fixture,
  ], {
    cwd: PROJECT_ROOT,
    env: { ...process.env, LC_ALL: 'C' },
  });
}

function requireSuccess(result, label) {
  if (result.status !== 0) {
    fail(`${label} failed (${result.status}): ${(result.stdout + result.stderr).trim()}`);
  }
}

function parseWhy3TypeDiagnostic(stderr, path) {
  const escaped = path.replace(/[.*+?^${}()|[\]\\]/gu, '\\$&');
  const pattern = new RegExp(
    `^File "${escaped}", line ([0-9]+), characters ([0-9]+)-([0-9]+):\\n` +
    'This term has type (.+), but is expected to have type (.+)\\n$',
    'u',
  );
  const match = stderr.match(pattern);
  if (match === null) fail(`unexpected Why3 typing diagnostic:\n${stderr}`);
  return {
    line: Number(match[1]),
    startColumn: Number(match[2]),
    endColumn: Number(match[3]),
    actualType: match[4],
    expectedType: match[5],
  };
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

function decodeOptionalHex(value, label) {
  if (typeof value !== 'string' || !/^(?:[0-9a-f]{2})+$/u.test(value)) {
    fail(`${label} must be present lowercase nonempty bytes hex`);
  }
  return Buffer.from(value, 'hex').toString('utf8');
}

function stripOuterParentheses(value) {
  let result = value.trim();
  while (result.startsWith('(') && result.endsWith(')')) {
    let depth = 0;
    let enclosesAll = true;
    for (let index = 0; index < result.length; index += 1) {
      if (result[index] === '(') depth += 1;
      if (result[index] === ')') depth -= 1;
      if (depth === 0 && index !== result.length - 1) {
        enclosesAll = false;
        break;
      }
    }
    if (!enclosesAll) break;
    result = result.slice(1, -1).trim();
  }
  return result;
}

function normalizeTypePair(actual, expected) {
  const variables = new Map();
  const normalize = value => stripOuterParentheses(value).replace(
    /\?[0-9]+|'[A-Za-z_][A-Za-z0-9_']*/gu,
    variable => {
      if (!variables.has(variable)) variables.set(variable, `$${variables.size}`);
      return variables.get(variable);
    },
  );
  return [normalize(actual), normalize(expected)];
}

function validateMoonDiagnostic(entry, reference, output) {
  const lines = output.trimEnd().split('\n');
  if (lines.length !== 1) fail(`${entry.id}: Moon diagnostic emitted ${lines.length} lines`);
  const diagnostic = JSON.parse(lines[0]);
  if (diagnostic.accepted !== false ||
      diagnostic.stage !== entry.expected.stage ||
      diagnostic.kind !== entry.expected.kind ||
      diagnostic.relative_path_hex !== hex(entry.source.path) ||
      diagnostic.start_line !== reference.line ||
      diagnostic.end_line !== reference.line ||
      diagnostic.start_column !== reference.startColumn ||
      diagnostic.end_column !== reference.endColumn) {
    fail(`${entry.id}: Moon diagnostic metadata does not match Why3`);
  }
  const source = readFileSync(join(PROJECT_ROOT, entry.source.path));
  const startByte = sourceOffset(source, reference.line, reference.startColumn);
  const endByte = sourceOffset(source, reference.line, reference.endColumn);
  if (diagnostic.start_byte !== startByte || diagnostic.end_byte !== endByte) {
    fail(`${entry.id}: Moon byte span does not match Why3 line/columns`);
  }
  const actual = decodeOptionalHex(
    diagnostic.actual_type_hex,
    `${entry.id} actual_type_hex`,
  );
  const expected = decodeOptionalHex(
    diagnostic.expected_type_hex,
    `${entry.id} expected_type_hex`,
  );
  assertEqual(
    normalizeTypePair(actual, expected),
    normalizeTypePair(reference.actualType, reference.expectedType),
    `${entry.id} actual/expected types`,
  );
}

function validateAcceptanceAndDiagnostics(why3Root, config, corpus) {
  for (const fixture of FIXTURES) {
    requireSuccess(
      why3Command(why3Root, config, '--parse-only', fixture.label),
      `Why3 ${fixture.label} parse-only`,
    );
    requireSuccess(
      why3Command(why3Root, config, '--type-only', fixture.label),
      `Why3 ${fixture.label} type-only`,
    );
    const moonAccepted = JSON.parse(
      runMoon('diagnostic', fixture.label).trim(),
    );
    assertEqual(
      moonAccepted,
      { accepted: true },
      `Moon ${fixture.label} acceptance`,
    );
  }

  for (const id of NEGATIVE_IDS) {
    const entry = corpus.entries.find(candidate => candidate.id === id);
    if (entry === undefined) fail(`pr-corpus-v1.json has no ${id}`);
    const fixture = entry.source.path;
    const sourceHash = sha256(readFileSync(join(PROJECT_ROOT, fixture)));
    if (sourceHash !== entry.source.sha256) fail(`${id}: source hash drift`);
    requireSuccess(
      why3Command(why3Root, config, '--parse-only', fixture),
      `Why3 ${id} parse-only`,
    );
    const rejected = why3Command(why3Root, config, '--type-only', fixture);
    if (rejected.status !== entry.referenceWhy3.exitCode ||
        rejected.stdout !== '' ||
        rejected.stderr !== entry.referenceWhy3.stderrUtf8 ||
        sha256(rejected.stderr) !== entry.referenceWhy3.stderrSha256) {
      fail(`${id}: Why3 rejection no longer matches pr-corpus-v1.json`);
    }
    const reference = parseWhy3TypeDiagnostic(rejected.stderr, fixture);
    validateMoonDiagnostic(
      entry,
      reference,
      runMoon('diagnostic', fixture),
    );
  }
}

function validatePortability(
  buildDirectory,
  executables,
  why3Root,
  snapshot,
  fixture,
  primaryTyped,
  primaryRaw,
) {
  const fixtureBytes = readFileSync(join(PROJECT_ROOT, fixture.label));
  const outputs = [];
  for (const name of ['absolute-root-a', 'absolute-root-b']) {
    const root = join(buildDirectory, name);
    mkdirSync(root, { recursive: true });
    const file = join(root, 'mvp.mlw');
    writeFileSync(file, fixtureBytes);
    outputs.push({
      typed: runReference(executables.typed, why3Root, snapshot, fixture, file),
      raw: runReference(executables.raw, why3Root, snapshot, fixture, file),
    });
  }
  assertSameOutput(
    primaryTyped,
    outputs[0].typed,
    'repository-path OCaml typed output',
    'absolute-root-a OCaml typed output',
  );
  assertSameOutput(
    outputs[0].typed,
    outputs[1].typed,
    'absolute-root-a OCaml typed output',
    'absolute-root-b OCaml typed output',
  );
  assertSameOutput(
    primaryRaw,
    outputs[0].raw,
    'repository-path OCaml raw output',
    'absolute-root-a OCaml raw output',
  );
  assertSameOutput(
    outputs[0].raw,
    outputs[1].raw,
    'absolute-root-a OCaml raw output',
    'absolute-root-b OCaml raw output',
  );
}

function validateFixtureContract(fixture, corpus) {
  const sourceSha256 = sha256(
    readFileSync(join(PROJECT_ROOT, fixture.label)),
  );
  const entries = corpus.entries.filter(entry =>
    entry.kind === 'whyml-semantic' && entry.source.path === fixture.label,
  );
  if (entries.length === 0 ||
      entries.some(entry => entry.source.sha256 !== sourceSha256)) {
    fail(`${fixture.label} does not match pr-corpus-v1.json`);
  }
  const configured = [...fixture.theories, ...fixture.modules]
    .flatMap(([unit, goals]) => goals.map(goal => `${unit}\u0000${goal}`))
    .sort();
  const contracted = entries
    .flatMap(entry => entry.units)
    .flatMap(unit => unit.goals.map(goal => `${unit.utf8}\u0000${goal.utf8}`))
    .sort();
  assertEqual(contracted, configured, `${fixture.label} goal inventory`);
  return sourceSha256;
}

function main(argv = process.argv.slice(2)) {
  const options = parseArguments(argv);
  const driver = readJson(DRIVER_CONTRACT);
  const profile = readJson(SEMANTIC_PROFILE);
  const corpus = readJson(PR_CORPUS);
  if (profile.why3Commit !== EXPECTED_WHY3_COMMIT ||
      profile.semanticProfileSha256 === undefined) {
    fail('semantic-profile-v1.json does not describe the selected Why3 source');
  }

  const buildDirectory = mkdtempSync(join(tmpdir(), 'why3-elab-differential-'));
  try {
    const runtime = verifyWhy3SourceAndTools(driver, options);
    const why3Root = runtime.sourceRoot;
    const executables = compileReferences(buildDirectory, runtime);
    const snapshot = join(buildDirectory, 'snapshot.json');
    const why3Config = join(buildDirectory, 'why3.conf');
    writeFileSync(why3Config, '');
    exportSnapshot(executables.snapshot, snapshot, why3Root, driver);

    let typedRecords = 0;
    let rawRecords = 0;
    for (const [index, fixture] of FIXTURES.entries()) {
      const sourceSha256 = validateFixtureContract(fixture, corpus);
      const fixturePath = join(PROJECT_ROOT, fixture.label);
      const ocamlTyped = runReference(
        executables.typed,
        why3Root,
        snapshot,
        fixture,
        fixturePath,
      );
      const ocamlRaw = runReference(
        executables.raw,
        why3Root,
        snapshot,
        fixture,
        fixturePath,
      );
      const moonTyped = runMoon('typed-semantic', fixture.label);
      const moonRaw = runMoon('raw-task', fixture.label);
      for (const [output, stage, producer] of [
        [ocamlTyped, 'typed-semantic', 'OCaml'],
        [moonTyped, 'typed-semantic', 'MoonBit'],
        [ocamlRaw, 'raw-task', 'OCaml'],
        [moonRaw, 'raw-task', 'MoonBit'],
      ]) {
        validateRecords(
          output,
          stage,
          fixture,
          sourceSha256,
          profile.semanticProfileSha256,
          producer,
        );
      }
      assertSameOutput(
        ocamlTyped,
        moonTyped,
        `OCaml ${fixture.label} typed output`,
        `MoonBit ${fixture.label} typed output`,
      );
      assertSameOutput(
        ocamlRaw,
        moonRaw,
        `OCaml ${fixture.label} raw output`,
        `MoonBit ${fixture.label} raw output`,
      );
      if (index === 0) {
        validatePortability(
          buildDirectory,
          executables,
          why3Root,
          snapshot,
          fixture,
          ocamlTyped,
          ocamlRaw,
        );
      }
      typedRecords += expectedRecords('typed-semantic', fixture).length;
      rawRecords += expectedRecords('raw-task', fixture).length;
    }
    validateAcceptanceAndDiagnostics(why3Root, why3Config, corpus);

    process.stdout.write(
      `run_elab_differential: Why3 ${WHY3_VERSION} ${EXPECTED_WHY3_COMMIT}\n` +
      `run_elab_differential: typed-semantic ${typedRecords}/${typedRecords} exact\n` +
      `run_elab_differential: raw-task ${rawRecords}/${rawRecords} exact\n` +
      `run_elab_differential: portability 2 roots, diagnostics ${NEGATIVE_IDS.length}/${NEGATIVE_IDS.length} exact\n`,
    );
  } finally {
    if (process.env.WHY3_REFERENCE_KEEP_TMP === '1') {
      process.stderr.write(`run_elab_differential: kept ${buildDirectory}\n`);
    } else {
      rmSync(buildDirectory, { recursive: true, force: true });
    }
  }
}

try {
  main();
} catch (error) {
  process.stderr.write(`run_elab_differential: ${error.message}\n`);
  process.exitCode = 1;
}
