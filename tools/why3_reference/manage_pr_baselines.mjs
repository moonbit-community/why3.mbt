#!/usr/bin/env node
// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const BASELINE_ROOT = join(SCRIPT_DIRECTORY, 'baselines', 'pr-v1');
const CORPUS_PATH = join(PROJECT_ROOT, 'tools', 'contracts', 'pr-corpus-v1.json');
const SEMANTIC_PROFILE_PATH = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'semantic-profile-v1.json',
);
const TRANSFORM_PROFILE_PATH = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'transform-profile-v1.json',
);
const ELABORATOR = join(
  PROJECT_ROOT,
  '_build',
  'native',
  'debug',
  'build',
  'cmd',
  'elab_canonical',
  'elab_canonical.exe',
);
const FIXTURES = [
  { label: 'tools/why3_reference/fixtures/mvp.mlw', polymorphic: false },
  { label: 'tests/vc/false-post.mlw', polymorphic: false },
  {
    label: 'tools/why3_reference/fixtures/transform-polymorphism.mlw',
    polymorphic: true,
  },
  {
    label: 'tools/why3_reference/fixtures/transform-polymorphic-definition.mlw',
    polymorphic: true,
  },
  {
    label: 'tools/why3_reference/fixtures/transform-inductive.mlw',
    polymorphic: true,
  },
  {
    label: 'tools/why3_reference/fixtures/smt-identifiers.mlw',
    polymorphic: true,
  },
  {
    label: 'tools/why3_reference/fixtures/solver-outcomes.mlw',
    polymorphic: false,
  },
];
const STAGES = [
  ['typed-semantic', 'typed-semantic.ndjson'],
  ['raw-task', 'raw-task.ndjson'],
  ['transform-checkpoints', 'transform-checkpoints.ndjson'],
  ['prepared-task', 'prepared-task.ndjson'],
  ['smt-token-stream', 'smt-token-stream.ndjson'],
];

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function canonicalSha(value) {
  return sha256(`${JSON.stringify(value)}\n`);
}

function readJson(path) {
  return JSON.parse(readFileSync(path, 'utf8'));
}

function run(command, argv, options = {}) {
  const result = spawnSync(command, argv, {
    cwd: options.cwd ?? PROJECT_ROOT,
    encoding: 'utf8',
    env: { ...process.env, LC_ALL: 'C', LANG: 'C', TZ: 'UTC' },
    maxBuffer: 512 * 1024 * 1024,
    shell: false,
  });
  if (result.error) throw result.error;
  if (result.status !== 0 || result.signal !== null) {
    fail(
      `${command} ${argv.join(' ')} failed with ${result.status}/${result.signal}: ` +
      `${(result.stderr ?? '').trim()}`,
    );
  }
  if (!options.allowStderr && result.stderr !== '') {
    fail(`${command} ${argv.join(' ')} unexpectedly emitted stderr`);
  }
  return result.stdout;
}

function parseArguments(argv) {
  if (argv.length === 0 || (argv.length === 1 && argv[0] === '--check')) {
    return { mode: 'check', directory: BASELINE_ROOT };
  }
  if (argv.length === 2 && argv[0] === '--candidate') {
    return { mode: 'candidate', directory: resolve(argv[1]) };
  }
  if (argv.length === 2 && argv[0] === '--promote') {
    return { mode: 'promote', directory: resolve(argv[1]) };
  }
  fail(
    'usage: manage_pr_baselines.mjs [--check | --candidate DIR | --promote DIR]',
  );
}

function corpusFixture(corpus, fixture) {
  const source = readFileSync(join(PROJECT_ROOT, fixture.label));
  const sourceSha256 = sha256(source);
  const entries = corpus.entries.filter(entry =>
    entry.kind === 'whyml-semantic' && entry.source.path === fixture.label,
  );
  if (entries.length === 0 ||
      entries.some(entry => entry.source.sha256 !== sourceSha256)) {
    fail(`${fixture.label} is not bound to the current PR corpus`);
  }
  const units = new Map();
  const goals = new Map();
  for (const entry of entries) {
    for (const unit of entry.units) {
      units.set(unit.bytesHex, unit.utf8);
      for (const goal of unit.goals) {
        const key = `${unit.bytesHex}:${goal.ordinal}:${goal.bytesHex}`;
        goals.set(key, {
          unitNameHex: unit.bytesHex,
          goalOrdinal: goal.ordinal,
          goalNameHex: goal.bytesHex,
        });
      }
    }
  }
  return { ...fixture, source, sourceSha256, units, goals };
}

function copyFixtures(root, fixtures) {
  for (const fixture of fixtures) {
    const path = join(root, fixture.label);
    mkdirSync(dirname(path), { recursive: true });
    writeFileSync(path, fixture.source);
  }
}

function runElaborator(root, stage, fixture) {
  return run(
    ELABORATOR,
    ['--stage', stage, fixture.label],
    { cwd: root },
  );
}

function parseRecords(output, stage, fixture, semanticProfileSha256) {
  if (!output.endsWith('\n')) {
    fail(`${fixture.label} ${stage} output has no final LF`);
  }
  const lines = output.slice(0, -1).split('\n');
  return lines.map((line, index) => {
    let record;
    try {
      record = JSON.parse(line);
    } catch (error) {
      fail(`${fixture.label} ${stage} record ${index}: ${error.message}`);
    }
    if (JSON.stringify(record) !== line || record.schema !== 2 ||
        record.semantic_profile_sha256 !== semanticProfileSha256 ||
        record.fixture !== fixture.label ||
        record.source_sha256 !== fixture.sourceSha256 ||
        record.canonical_sha256 !== canonicalSha(record.canonical)) {
      fail(`${fixture.label} ${stage} record ${index} has invalid canonical metadata`);
    }
    return record;
  });
}

function goalKey(record) {
  return `${record.unit_name_hex}:${record.goal_ordinal}:${record.goal_name_hex}`;
}

function assertSameSet(actual, expected, label) {
  const left = [...actual].sort();
  const right = [...expected].sort();
  if (JSON.stringify(left) !== JSON.stringify(right)) {
    fail(`${label} inventory mismatch`);
  }
}

function validateFixtureRecords(
  recordsByStage,
  fixture,
  checkpointSequence,
) {
  const typed = recordsByStage.get('typed-semantic');
  if (typed.some(record =>
    record.scope !== 'unit' ||
    !['typed-semantic', 'typed-program'].includes(record.stage) ||
    !['theory', 'module'].includes(record.unit_kind))) {
    fail(`${fixture.label} typed records have invalid stage/scope/kind`);
  }
  assertSameSet(
    typed.map(record => record.unit_name_hex),
    fixture.units.keys(),
    `${fixture.label} typed-unit`,
  );

  const raw = recordsByStage.get('raw-task');
  if (raw.some(record =>
    record.scope !== 'goal' || record.stage !== 'raw-task' ||
    record.unit_kind !== 'theory')) {
    fail(`${fixture.label} raw records have invalid stage/scope/kind`);
  }
  assertSameSet(
    raw.map(goalKey),
    fixture.goals.keys(),
    `${fixture.label} raw-goal`,
  );
  const orderedGoals = raw.map(goalKey);

  for (const stage of ['prepared-task', 'smt-token-stream']) {
    const records = recordsByStage.get(stage);
    if (records.some(record =>
      record.scope !== 'goal' || record.stage !== stage ||
      record.unit_kind !== 'theory')) {
      fail(`${fixture.label} ${stage} records have invalid metadata`);
    }
    if (JSON.stringify(records.map(goalKey)) !== JSON.stringify(orderedGoals)) {
      fail(`${fixture.label} ${stage} goal order differs from raw-task`);
    }
  }

  const checkpoints = recordsByStage.get('transform-checkpoints');
  const expectedCheckpoints = orderedGoals.flatMap(key =>
    checkpointSequence.map(stage => `${key}:${stage}`));
  const actualCheckpoints = checkpoints.map(record => {
    if (record.scope !== 'goal' || record.unit_kind !== 'theory') {
      fail(`${fixture.label} checkpoint has invalid scope/kind`);
    }
    return `${goalKey(record)}:${record.stage}`;
  });
  if (JSON.stringify(actualCheckpoints) !== JSON.stringify(expectedCheckpoints)) {
    fail(`${fixture.label} checkpoint sequence differs from transform profile`);
  }
}

function buildArtifacts() {
  const corpusBytes = readFileSync(CORPUS_PATH);
  const corpus = JSON.parse(corpusBytes);
  const semanticProfile = readJson(SEMANTIC_PROFILE_PATH);
  const transformProfileBytes = readFileSync(TRANSFORM_PROFILE_PATH);
  const transformProfile = JSON.parse(transformProfileBytes);
  const fixtures = FIXTURES.map(fixture => corpusFixture(corpus, fixture));

  run(
    'moon',
    ['build', '--target', 'native', 'cmd/elab_canonical'],
    { allowStderr: true },
  );
  if (!existsSync(ELABORATOR)) fail('native elab_canonical executable is missing');

  const temporary = mkdtempSync(join(tmpdir(), 'why3mbt-pr-baseline-'));
  try {
    const roots = [join(temporary, 'absolute-root-a'), join(temporary, 'absolute-root-b')];
    for (const root of roots) copyFixtures(root, fixtures);
    const artifacts = new Map(STAGES.map(([stage]) => [stage, []]));
    for (const fixture of fixtures) {
      const recordsByStage = new Map();
      for (const [stage] of STAGES) {
        const first = runElaborator(roots[0], stage, fixture);
        const second = runElaborator(roots[1], stage, fixture);
        if (first !== second) {
          fail(`${fixture.label} ${stage} leaks its absolute fixture root`);
        }
        const records = parseRecords(
          first,
          stage,
          fixture,
          semanticProfile.semanticProfileSha256,
        );
        recordsByStage.set(stage, records);
        artifacts.get(stage).push(first);
      }
      const sequence = fixture.polymorphic
        ? transformProfile.tracePatch.checkpointSequences.polymorphic
        : transformProfile.tracePatch.checkpointSequences.monomorphic;
      validateFixtureRecords(recordsByStage, fixture, sequence);
    }

    const files = new Map();
    const manifestArtifacts = [];
    for (const [stage, name] of STAGES) {
      const content = artifacts.get(stage).join('');
      files.set(name, content);
      manifestArtifacts.push({
        stage,
        path: name,
        records: content === '' ? 0 : content.trimEnd().split('\n').length,
        sha256: sha256(content),
      });
    }
    const manifestBase = {
      schemaVersion: 1,
      profile: 'why3-1.7.2-pr-baseline-v1',
      prCorpusSha256: sha256(corpusBytes),
      semanticProfileSha256: semanticProfile.semanticProfileSha256,
      transformProfileSha256: sha256(transformProfileBytes),
      portabilityRoots: 2,
      fixtures: fixtures.map(fixture => ({
        path: fixture.label,
        sourceSha256: fixture.sourceSha256,
        typedUnits: fixture.units.size,
        goals: fixture.goals.size,
        checkpointProfile: fixture.polymorphic ? 'polymorphic' : 'monomorphic',
      })),
      artifacts: manifestArtifacts,
    };
    const manifest = {
      ...manifestBase,
      baselineSetSha256: canonicalSha(manifestBase),
    };
    files.set('manifest.json', `${JSON.stringify(manifest, null, 2)}\n`);
    return files;
  } finally {
    rmSync(temporary, { recursive: true, force: true });
  }
}

function firstDifference(left, right) {
  const limit = Math.min(left.length, right.length);
  let offset = 0;
  while (offset < limit && left[offset] === right[offset]) offset += 1;
  return offset;
}

function compareDirectory(directory, files) {
  for (const [name, expected] of files) {
    const path = join(directory, name);
    if (!existsSync(path)) fail(`${path} is missing`);
    const actual = readFileSync(path, 'utf8');
    if (actual !== expected) {
      fail(
        `${path} differs at byte ${firstDifference(actual, expected)}; ` +
        `checked-in ${sha256(actual)}, generated ${sha256(expected)}`,
      );
    }
  }
}

function writeCandidate(directory, files) {
  if (existsSync(directory) && readdirSync(directory).length !== 0) {
    fail(`candidate directory is not empty: ${directory}`);
  }
  mkdirSync(directory, { recursive: true });
  for (const [name, content] of files) writeFileSync(join(directory, name), content);
  const changes = [];
  for (const [name, content] of files) {
    const current = join(BASELINE_ROOT, name);
    const before = existsSync(current) ? readFileSync(current) : null;
    if (before === null || !before.equals(Buffer.from(content))) {
      changes.push({
        path: name,
        beforeSha256: before === null ? null : sha256(before),
        candidateSha256: sha256(content),
      });
    }
  }
  process.stdout.write(`${JSON.stringify({ candidate: directory, changes }, null, 2)}\n`);
}

function readCandidate(directory) {
  const files = new Map();
  for (const [, name] of STAGES) files.set(name, readFileSync(join(directory, name), 'utf8'));
  files.set('manifest.json', readFileSync(join(directory, 'manifest.json'), 'utf8'));
  return files;
}

function promoteCandidate(directory) {
  const candidate = readCandidate(directory);
  const generated = buildArtifacts();
  for (const [name, content] of generated) {
    if (candidate.get(name) !== content) {
      fail(`candidate ${name} does not match a fresh two-root generation`);
    }
  }
  mkdirSync(BASELINE_ROOT, { recursive: true });
  for (const [name, content] of candidate) {
    writeFileSync(join(BASELINE_ROOT, name), content);
  }
  process.stdout.write(
    `manage_pr_baselines: promoted ${candidate.size} files from ${directory}\n`,
  );
}

function main() {
  const arguments_ = parseArguments(process.argv.slice(2));
  if (arguments_.mode === 'promote') {
    promoteCandidate(arguments_.directory);
    return;
  }
  const generated = buildArtifacts();
  if (arguments_.mode === 'candidate') {
    writeCandidate(arguments_.directory, generated);
  } else {
    compareDirectory(arguments_.directory, generated);
    process.stdout.write(
      `manage_pr_baselines: ${generated.size} checked-in files exact across two roots\n`,
    );
  }
}

try {
  main();
} catch (error) {
  process.stderr.write(`manage_pr_baselines: ${error.message}\n`);
  process.exitCode = 1;
}
