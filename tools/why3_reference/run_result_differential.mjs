#!/usr/bin/env node
// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import referenceEnvironment from './reference_environment.cjs';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const RUN_FIXED = join(SCRIPT_DIRECTORY, 'run-fixed');
const MVP_FIXTURE = 'tools/why3_reference/fixtures/mvp.mlw';
const POLYMORPHISM_FIXTURE =
  'tools/why3_reference/fixtures/transform-polymorphism.mlw';
const POLYMORPHIC_DEFINITION_FIXTURE =
  'tools/why3_reference/fixtures/transform-polymorphic-definition.mlw';
const IDENTIFIER_FIXTURE = 'tools/why3_reference/fixtures/smt-identifiers.mlw';
const SOLVER_FIXTURE = 'tools/why3_reference/fixtures/solver-outcomes.mlw';
const FALSE_POST_FIXTURE = 'tests/vc/false-post.mlw';
const CORPUS_PATH = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'pr-corpus-v1.json',
);
const RESULT_BASELINE = join(
  SCRIPT_DIRECTORY,
  'baselines',
  'pr-v1',
  'prover-result.json',
);
const CLI = join(
  PROJECT_ROOT,
  '_build',
  'native',
  'debug',
  'build',
  'cmd',
  'why3',
  'why3.exe',
);
const LOCK = referenceEnvironment.readEnvironmentLock();
const CASES = [
  ...resultCases('mvp.logic-core', MVP_FIXTURE, 'LogicCore', [
    'implication_identity', 'ordinary_attribute', 'bool_int_real',
  ]),
  ...resultCases('mvp.logic-core', MVP_FIXTURE, 'LogicReal', ['real_order']),
  ...resultCases(
    'mvp.logic-polymorphism',
    MVP_FIXTURE,
    'LogicPolymorphism',
    ['identity_int', 'identity_bool'],
  ),
  ...resultCases(
    'mvp.logic-quantifiers',
    MVP_FIXTURE,
    'LogicQuantifiers',
    ['quantified_trigger'],
  ),
  ...resultCases('mvp.unit', MVP_FIXTURE, 'UnitMvp', ['unit_roundtrip']),
  ...resultCases(
    'mvp.namespace',
    MVP_FIXTURE,
    'NamespaceMvp',
    ['qualified_lookup'],
  ),
  ...resultCases('mvp.multiple-units', MVP_FIXTURE, 'MultiFirst', ['first_goal']),
  ...resultCases('mvp.multiple-units', MVP_FIXTURE, 'MultiSecond', ['second_goal']),
  ...resultCases('mvp.abs', MVP_FIXTURE, 'Abs', ["abs'vc"]),
  ...resultCases('mvp.routine-call', MVP_FIXTURE, 'RoutineCall', [
    "increment'vc", "increment_twice'vc",
  ]),
  ...resultCases('mvp.assert-assume', MVP_FIXTURE, 'AssertAssume', [
    "checked_identity'vc",
  ]),
  ...resultCases('mvp.program-real', MVP_FIXTURE, 'ProgramReal', ["add_zero'vc"]),
  ...resultCases(
    'mutation.false-postcondition',
    FALSE_POST_FIXTURE,
    'FalsePost',
    [["identity'vc", 'Unknown', 'sat', 'must-not-be-Valid']],
  ),
  ...resultCases(
    'transform.polymorphism',
    POLYMORPHISM_FIXTURE,
    'LogicPolymorphism',
    [['free_type_variable', 'Unknown', 'sat']],
  ),
  ...resultCases(
    'transform.polymorphic-definition',
    POLYMORPHIC_DEFINITION_FIXTURE,
    'LogicPolymorphicDefinition',
    ['reflexive_goal'],
  ),
  ...resultCases(
    'smt.identifier-safety',
    IDENTIFIER_FIXTURE,
    'SmtIdentifiers',
    [['reserved_and_collision', 'Unknown', 'sat']],
  ),
  ...resultCases('solver.outcomes', SOLVER_FIXTURE, 'SolverOutcomes', [
    'unsat_valid',
    ['sat_unknown', 'Unknown', 'sat'],
    ['solver_unknown', 'Unknown', 'unknown'],
  ]),
];

function resultCases(fixtureId, fixture, unit, goals) {
  return goals.map(specification => {
    const [goal, kind = 'Valid', reason = null, assertion = null] = Array.isArray(specification)
      ? specification
      : [specification];
    return {
      fixtureId,
      fixture,
      unit,
      goal,
      kind,
      reason,
      assertion,
      exitCode: kind === 'Valid' ? 0 : 2,
    };
  });
}

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function canonicalSha(value) {
  return sha256(`${JSON.stringify(value)}\n`);
}

function parseArguments(argv) {
  if (argv.length === 0 || (argv.length === 1 && argv[0] === '--check')) {
    return { mode: 'check', path: RESULT_BASELINE };
  }
  if (argv.length === 2 && argv[0] === '--candidate') {
    return { mode: 'candidate', path: resolve(argv[1]) };
  }
  if (argv.length === 2 && argv[0] === '--promote') {
    return { mode: 'promote', path: resolve(argv[1]) };
  }
  fail(
    'usage: run_result_differential.mjs [--check | --candidate PATH | --promote PATH]',
  );
}

function corpusCaseMap(corpus) {
  const cases = new Map();
  for (const entry of corpus.entries) {
    if (entry.kind !== 'whyml-semantic' ||
        !entry.expected.gateStages.includes('prover-result')) continue;
    for (const unit of entry.units) {
      for (const goal of unit.goals) {
        const key = `${entry.id}\u0000${unit.utf8}\u0000${goal.utf8}`;
        cases.set(key, {
          source: entry.source.path,
          sourceSha256: entry.source.sha256,
          unitNameHex: unit.bytesHex,
          goalNameHex: goal.bytesHex,
          goalOrdinal: goal.ordinal,
        });
      }
    }
  }
  return cases;
}

function bindCasesToCorpus(corpus) {
  const contracted = corpusCaseMap(corpus);
  const bound = CASES.map(testCase => {
    const key = `${testCase.fixtureId}\u0000${testCase.unit}\u0000${testCase.goal}`;
    const identity = contracted.get(key);
    if (identity === undefined) {
      fail(`result case is absent from PR corpus: ${key}`);
    }
    contracted.delete(key);
    if (identity.source !== testCase.fixture ||
        sha256(readFileSync(join(PROJECT_ROOT, testCase.fixture))) !==
          identity.sourceSha256) {
      fail(`${testCase.fixtureId}/${testCase.goal}: source contract drift`);
    }
    return { ...testCase, ...identity };
  });
  if (contracted.size !== 0) {
    fail(`PR corpus has ${contracted.size} prover-result goal(s) without a case`);
  }
  return bound;
}

function run(command, argv, expectedExitCodes, env = process.env) {
  const result = spawnSync(command, argv, {
    cwd: PROJECT_ROOT,
    encoding: 'utf8',
    env: { ...env, LC_ALL: 'C', LANG: 'C', TZ: 'UTC' },
    maxBuffer: 64 * 1024 * 1024,
    shell: false,
  });
  if (result.error &&
      !(result.error.code === 'EPERM' && result.signal === null &&
        result.status !== null)) {
    throw result.error;
  }
  if (result.signal !== null || !expectedExitCodes.includes(result.status)) {
    fail(
      `${command} ${argv.join(' ')} failed with ${result.status}/${result.signal}: ` +
      `${result.stderr.trim()}`,
    );
  }
  return result;
}

function runFixed(argv, expectedExitCodes) {
  return run(process.execPath, [RUN_FIXED, ...argv], expectedExitCodes);
}

function normalizeWhy3Answer(answer) {
  if (answer === 'Valid') return { kind: 'Valid', reason: null };
  const match = /^Unknown\n\((.*)\)$/su.exec(answer);
  if (match) return { kind: 'Unknown', reason: match[1] };
  fail(`unsupported Why3 answer in deterministic result lane: ${JSON.stringify(answer)}`);
}

function buildCli() {
  if (process.env.WHY3_RESULT_SKIP_BUILD !== '1') {
    run('moon', ['build', '--target', 'native', 'cmd/why3'], [0]);
  }
  if (!existsSync(CLI)) {
    fail(`native product CLI is missing: ${CLI}`);
  }
}

function normalizeMoonAnswer(record) {
  const result = record.result;
  if (!result || typeof result.kind !== 'string') fail('MoonBit result record is malformed');
  if (result.kind === 'Valid') return { kind: 'Valid', reason: null };
  if (result.kind === 'Unknown' && typeof result.reason_hex === 'string') {
    return {
      kind: 'Unknown',
      reason: Buffer.from(result.reason_hex, 'hex').toString('utf8'),
    };
  }
  fail(`unsupported MoonBit answer in deterministic result lane: ${JSON.stringify(result)}`);
}

function assertExpected(actual, testCase, implementation) {
  if (actual.kind !== testCase.kind || actual.reason !== testCase.reason) {
    fail(
      `${implementation} ${testCase.goal}: expected ` +
      `${JSON.stringify({ kind: testCase.kind, reason: testCase.reason })}, got ` +
      `${JSON.stringify(actual)}`,
    );
  }
}

function sectionLines(text, header) {
  return text
    .split(/(?=^\[[^\]]+\]\s*$)/mu)
    .filter(section => section.startsWith(`${header}\n`))
    .map(section => section.trimEnd().split('\n'));
}

function assertDetectedZ3Profile(configText) {
  const expectedCommand =
    `command = "'${LOCK.z3.runtime.executable}' -smt2 -T:%t ` +
    'sat.random_seed=42 nlsat.randomize=false smt.random_seed=42 -st %f"';
  const candidates = sectionLines(configText, '[prover]')
    .filter(lines => lines.includes('driver = "z3_487"'));
  if (candidates.length !== 1) {
    fail(`expected one detected z3_487 profile, found ${candidates.length}`);
  }
  const lines = candidates[0];
  for (const expected of [
    'name = "Z3"',
    `version = "${LOCK.z3.version}"`,
    'driver = "z3_487"',
    expectedCommand,
  ]) {
    if (!lines.includes(expected)) {
      fail(`detected z3_487 profile is missing ${JSON.stringify(expected)}`);
    }
  }
  if (lines.some(line => line.startsWith('alternative = '))) {
    fail('detected z3_487 profile unexpectedly names an alternative');
  }
}

function main() {
  const arguments_ = parseArguments(process.argv.slice(2));
  if (arguments_.mode !== 'check' && arguments_.path === RESULT_BASELINE) {
    fail('candidate path must be separate from the checked-in result baseline');
  }
  const corpusBytes = readFileSync(CORPUS_PATH);
  const corpus = JSON.parse(corpusBytes);
  const cases = bindCasesToCorpus(corpus);
  buildCli();
  const directory = mkdtempSync(join(tmpdir(), 'why3mbt-result-differential-'));
  try {
    const config = join(directory, 'why3.conf');
    const resolvedContext = join(directory, 'resolved_context.json');
    runFixed(
      [
        'solver.outcomes',
        '--config',
        config,
        '--resolved-context',
        resolvedContext,
        '--',
        'config',
        'detect',
      ],
      [0],
    );
    const detected = runFixed(
      [
        'solver.outcomes',
        '--config',
        config,
        '--resolved-context',
        resolvedContext,
        '--',
        'config',
        'show',
      ],
      [0],
    );
    assertDetectedZ3Profile(detected.stdout);
    const compared = [];
    for (const testCase of cases) {
      const upstream = runFixed(
        [
          testCase.fixtureId,
          '--config',
          config,
          '--resolved-context',
          resolvedContext,
          '--',
          'prove',
          testCase.fixture,
          '-T',
          testCase.unit,
          '-G',
          testCase.goal,
          '-P',
          'Z3,4.8.12',
          '-t',
          '10',
          '--json',
        ],
        [testCase.exitCode],
      );
      const upstreamRecord = JSON.parse(upstream.stdout);
      const upstreamAnswer = normalizeWhy3Answer(
        upstreamRecord['prover-result']?.answer,
      );
      assertExpected(upstreamAnswer, testCase, 'Why3');

      const moon = run(
        CLI,
        [
          'prove',
          testCase.fixture,
          '-T',
          testCase.unit,
          '-G',
          testCase.goal,
          '--z3',
          LOCK.z3.runtime.executable,
          '-t',
          '10',
          '--json',
        ],
        [testCase.exitCode],
      );
      const lines = moon.stdout.trimEnd().split('\n');
      if (lines.length !== 1) fail(`MoonBit emitted ${lines.length} result records`);
      const moonAnswer = normalizeMoonAnswer(JSON.parse(lines[0]));
      assertExpected(moonAnswer, testCase, 'MoonBit');
      if (JSON.stringify(upstreamAnswer) !== JSON.stringify(moonAnswer)) {
        fail(`${testCase.goal}: normalized Why3 and MoonBit answers differ`);
      }
      compared.push({
        fixtureId: testCase.fixtureId,
        source: testCase.source,
        sourceSha256: testCase.sourceSha256,
        unit: testCase.unit,
        unitNameHex: testCase.unitNameHex,
        goal: testCase.goal,
        goalNameHex: testCase.goalNameHex,
        goalOrdinal: testCase.goalOrdinal,
        answer: moonAnswer,
        ...(testCase.assertion === null ? {} : { assertion: testCase.assertion }),
        why3Transport: 'temporary-file-%f',
        moonbitTransport: 'stdin--in',
      });
    }
    const resultBase = {
      schemaVersion: 1,
      profile: 'why3-1.7.2-z3-4.8.12-pr-result-v1',
      prCorpusSha256: sha256(corpusBytes),
      comparisonTarget: {
        why3: {
          version: LOCK.why3.version,
          commit: LOCK.why3.commit,
        },
        z3: { version: LOCK.z3.version },
      },
      compared,
    };
    const result = {
      ...resultBase,
      resultSetSha256: canonicalSha(resultBase),
    };
    const rendered = `${JSON.stringify(result, null, 2)}\n`;
    if (arguments_.mode === 'candidate') {
      if (existsSync(arguments_.path)) {
        fail(`candidate already exists: ${arguments_.path}`);
      }
      mkdirSync(dirname(arguments_.path), { recursive: true });
      writeFileSync(arguments_.path, rendered);
      const before = existsSync(RESULT_BASELINE)
        ? sha256(readFileSync(RESULT_BASELINE))
        : null;
      process.stdout.write(`${JSON.stringify({
        candidate: arguments_.path,
        beforeSha256: before,
        candidateSha256: sha256(rendered),
        compared: compared.length,
      }, null, 2)}\n`);
    } else if (arguments_.mode === 'promote') {
      if (!existsSync(arguments_.path) ||
          readFileSync(arguments_.path, 'utf8') !== rendered) {
        fail('candidate does not match a fresh fixed-image result differential');
      }
      mkdirSync(dirname(RESULT_BASELINE), { recursive: true });
      writeFileSync(RESULT_BASELINE, rendered);
      process.stdout.write(
        `run_result_differential: promoted ${compared.length} result records\n`,
      );
    } else {
      if (!existsSync(RESULT_BASELINE) ||
          readFileSync(RESULT_BASELINE, 'utf8') !== rendered) {
        fail('checked-in prover-result baseline differs from fixed-image results');
      }
      process.stdout.write(
        `run_result_differential: ${compared.length}/${compared.length} ` +
        'fixed-image result records exact\n',
      );
    }
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

try {
  main();
} catch (error) {
  process.stderr.write(`run_result_differential: ${error.message}\n`);
  process.exitCode = 1;
}
