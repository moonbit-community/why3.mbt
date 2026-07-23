// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, readdirSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const REFERENCE_ROOT = join(PROJECT_ROOT, 'tools', 'why3_reference');
const BASELINE_ROOT = join(REFERENCE_ROOT, 'baselines', 'pr-v1');
const STRUCTURAL_BASELINES = [
  'manifest.json',
  'typed-semantic.ndjson',
  'raw-task.ndjson',
  'transform-checkpoints.ndjson',
  'prepared-task.ndjson',
  'smt-token-stream.ndjson',
];

const SCRIPTS = {
  contracts: join(PROJECT_ROOT, 'tools', 'check_pr00_contracts.mjs'),
  elab: join(REFERENCE_ROOT, 'run_elab_differential.mjs'),
  transform: join(REFERENCE_ROOT, 'run_transform_differential.mjs'),
  smt: join(REFERENCE_ROOT, 'run_smt_differential.mjs'),
  unsupported: join(REFERENCE_ROOT, 'run_unsupported_gate.mjs'),
  result: join(REFERENCE_ROOT, 'run_result_differential.mjs'),
  baselines: join(REFERENCE_ROOT, 'manage_pr_baselines.mjs'),
  fixtures: join(PROJECT_ROOT, 'tools', 'check_why3_fixtures.mjs'),
};

function fail(message) {
  throw new Error(message);
}

function assertNoArguments(command, argv) {
  if (argv.length !== 0) fail(`${command} does not accept arguments`);
}

function displayCommand(command, argv) {
  return [command, ...argv].map(value => JSON.stringify(value)).join(' ');
}

function run(command, argv, { capture = false } = {}) {
  process.stderr.write(`==> ${displayCommand(command, argv)}\n`);
  const result = spawnSync(command, argv, {
    cwd: PROJECT_ROOT,
    env: process.env,
    shell: false,
    ...(capture ? { encoding: 'utf8' } : { stdio: 'inherit' }),
  });
  if (result.error !== undefined || result.signal !== null || result.status !== 0) {
    const detail = result.error?.message ??
      (capture ? (result.stderr ?? '').trim() : '') ?? '';
    fail(
      `${displayCommand(command, argv)} failed` +
      `${result.signal === null ? ` with status ${result.status}` : ` from signal ${result.signal}`}` +
      `${detail === '' ? '' : `: ${detail}`}`,
    );
  }
  return capture ? result.stdout : '';
}

function runNode(script, argv, options) {
  return run(process.execPath, [script, ...argv], options);
}

function requiredValue(argv, index, option) {
  const value = argv[index + 1];
  if (value === undefined || value.startsWith('--')) fail(`${option} requires a value`);
  return value;
}

export function parseReferenceOptions(argv, { quick = false } = {}) {
  const result = {
    why3Root: null,
    why3Archive: null,
    quick: false,
  };
  const seen = new Set();
  for (let index = 0; index < argv.length; index += 1) {
    const option = argv[index];
    if (seen.has(option)) fail(`duplicate option ${option}`);
    seen.add(option);
    if (option === '--why3-root' || option === '--why3-archive') {
      const value = resolve(requiredValue(argv, index, option));
      if (option === '--why3-root') result.why3Root = value;
      else result.why3Archive = value;
      index += 1;
    } else if (quick && option === '--quick') {
      result.quick = true;
    } else {
      fail(`unknown option ${option}`);
    }
  }
  if (result.why3Root !== null && result.why3Archive !== null) {
    fail('--why3-root and --why3-archive are mutually exclusive');
  }
  return result;
}

function sourceArguments(options) {
  if (options.why3Archive !== null) return ['--why3-archive', options.why3Archive];
  if (options.why3Root !== null) return ['--why3-root', options.why3Root];
  return [];
}

function contractArguments(options) {
  return [
    ...sourceArguments(options),
    ...(options.quick ? ['--quick'] : []),
  ];
}

function bootstrap() {
  run('moon', ['update']);
  run('moon', ['check']);
}

function checkContracts(options) {
  runNode(SCRIPTS.contracts, contractArguments(options));
}

function smokeFixedReference() {
  const contextRoot = resolve(
    process.env.WHY3_REFERENCE_CONTEXT_DIR ??
      join(PROJECT_ROOT, '_build', 'reference-context'),
  );
  mkdirSync(contextRoot, { recursive: true });
  run(join(REFERENCE_ROOT, 'run-fixed'), [
    'mvp.abs',
    '--config',
    join(contextRoot, 'why3.conf'),
    '--resolved-context',
    join(contextRoot, 'resolved_context.json'),
    '--',
    'prove',
    '--parse-only',
    'tools/why3_reference/fixtures/mvp.mlw',
  ]);
}

const LAYERS = ['elab', 'transform', 'smt', 'unsupported'];

function runLayers(options, layers = LAYERS) {
  const source = sourceArguments(options);
  for (const layer of layers) {
    if (!LAYERS.includes(layer)) fail(`unknown reference layer ${layer}`);
    runNode(SCRIPTS[layer], layer === 'unsupported' ? [] : source);
  }
}

export function parseBaselinesOptions(argv) {
  const mode = argv[0];
  if (!['check', 'candidate', 'promote'].includes(mode)) {
    fail('baselines requires check, candidate, or promote');
  }
  const result = {
    mode,
    records: null,
    result: null,
    compare: false,
  };
  const seen = new Set();
  for (let index = 1; index < argv.length; index += 1) {
    const option = argv[index];
    if (seen.has(option)) fail(`duplicate option ${option}`);
    seen.add(option);
    if (option === '--compare') {
      result.compare = true;
      continue;
    }
    if (!['--records', '--result'].includes(option)) {
      fail(`unknown option ${option}`);
    }
    const value = resolve(requiredValue(argv, index, option));
    if (option === '--records') result.records = value;
    else result.result = value;
    index += 1;
  }
  if (mode === 'check') {
    if (argv.length !== 1) fail('baselines check does not accept paths or --compare');
  } else if (result.records === null || result.result === null) {
    fail(`baselines ${mode} requires --records and --result`);
  }
  if (mode !== 'candidate' && result.compare) {
    fail('--compare is valid only for baselines candidate');
  }
  return result;
}

function assertSameFile(actualPath, expectedPath) {
  const actual = readFileSync(actualPath);
  const expected = readFileSync(expectedPath);
  if (!actual.equals(expected)) {
    fail(`${actualPath} differs from ${expectedPath}`);
  }
}

function compareBaselineCandidate(options) {
  for (const name of STRUCTURAL_BASELINES) {
    assertSameFile(join(options.records, name), join(BASELINE_ROOT, name));
  }
  assertSameFile(options.result, join(BASELINE_ROOT, 'prover-result.json'));
  process.stdout.write('baselines: candidate matches the checked-in baseline records\n');
}

function runBaselines(options) {
  if (options.mode === 'check') {
    runNode(SCRIPTS.baselines, ['--check']);
    runNode(SCRIPTS.result, []);
    return;
  }

  if (options.mode === 'candidate') {
    runNode(SCRIPTS.baselines, ['--candidate', options.records]);
    runNode(SCRIPTS.result, ['--candidate', options.result]);
    if (options.compare) compareBaselineCandidate(options);
    return;
  }

  runNode(SCRIPTS.baselines, ['--promote', options.records]);
  runNode(SCRIPTS.result, ['--promote', options.result]);
  runNode(SCRIPTS.contracts, ['--quick']);
}

function checkProject({ moonDiffOnly = false } = {}) {
  run('moon', ['check', '--target', 'all', '--warn-list', '+73']);
  run('moon', ['test', '--target', 'all', '--serial', '--release']);
  run('moon', ['test', '--target', 'all', '--serial']);
  run('sh', [join(PROJECT_ROOT, 'tools', 'check_native_runner_asan.sh')]);

  const nodeTests = readdirSync(join(PROJECT_ROOT, 'tools'))
    .filter(name => name.endsWith('.test.mjs'))
    .sort()
    .map(name => join('tools', name));
  if (nodeTests.length === 0) fail('no Node.js tool tests found');
  run(process.execPath, ['--test', ...nodeTests]);

  const diffArguments = [
    'diff',
    '--exit-code',
    ...(moonDiffOnly ? ['--', '*.mbt', '*.mbti'] : []),
  ];
  run('moon', ['info']);
  run('git', diffArguments);
  run('moon', ['fmt']);
  run('git', diffArguments);
}

function usage() {
  return [
    'usage: node tools/run.mjs COMMAND [OPTIONS]',
    '',
    'commands:',
    '  bootstrap',
    '  contracts [--why3-root PATH | --why3-archive PATH] [--quick]',
    '  fixtures',
    '  layers [all|elab|transform|smt|unsupported] [source options]',
    '  baselines check',
    '  baselines candidate --records DIR --result PATH [--compare]',
    '  baselines promote --records DIR --result PATH',
    '  reference [--why3-root PATH | --why3-archive PATH]',
    '  project [--moon-diff-only]',
    '',
  ].join('\n');
}

export function main(argv = process.argv.slice(2)) {
  const command = argv[0];
  const rest = argv.slice(1);
  if (command === undefined || command === '--help' || command === 'help') {
    process.stdout.write(usage());
    return;
  }
  if (command === 'bootstrap') {
    assertNoArguments(command, rest);
    bootstrap();
  } else if (command === 'contracts') {
    checkContracts(parseReferenceOptions(rest, { quick: true }));
  } else if (command === 'fixtures') {
    assertNoArguments(command, rest);
    runNode(SCRIPTS.fixtures, []);
  } else if (command === 'layers') {
    const layer = rest[0] !== undefined && !rest[0].startsWith('--')
      ? rest[0]
      : 'all';
    const options = parseReferenceOptions(layer === 'all' && rest[0] !== 'all' ? rest : rest.slice(1));
    runLayers(options, layer === 'all' ? LAYERS : [layer]);
  } else if (command === 'baselines') {
    runBaselines(parseBaselinesOptions(rest));
  } else if (command === 'reference') {
    const options = parseReferenceOptions(rest);
    smokeFixedReference();
    runNode(SCRIPTS.fixtures, []);
    checkContracts(options);
    runLayers(options);
    runBaselines(parseBaselinesOptions(['check']));
  } else if (command === 'project') {
    if (rest.length > 1 || (rest.length === 1 && rest[0] !== '--moon-diff-only')) {
      fail('project accepts only [--moon-diff-only]');
    }
    checkProject({ moonDiffOnly: rest[0] === '--moon-diff-only' });
  } else {
    fail(`unknown command ${command}\n\n${usage()}`);
  }
}

const isMain = process.argv[1] !== undefined &&
  pathToFileURL(resolve(process.argv[1])).href === import.meta.url;
if (isMain) {
  try {
    main();
  } catch (error) {
    process.stderr.write(`tools/run: ${error.message}\n`);
    process.exitCode = 1;
  }
}
