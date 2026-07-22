// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { existsSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const ORACLE_ROOT = join(PROJECT_ROOT, 'tools', 'why3_oracle');
const CONTRACT_ROOT = join(PROJECT_ROOT, 'tools', 'contracts');
const GOLDEN_ROOT = join(ORACLE_ROOT, 'goldens', 'pr-v1');
const TOOLCHAIN_LOCK = join(CONTRACT_ROOT, 'toolchain-lock.json');
const STRUCTURAL_GOLDENS = [
  'manifest.json',
  'typed-semantic.ndjson',
  'raw-task.ndjson',
  'transform-checkpoints.ndjson',
  'prepared-task.ndjson',
  'smt-token-stream.ndjson',
];

const SCRIPTS = {
  contracts: join(PROJECT_ROOT, 'tools', 'check_pr00_contracts.mjs'),
  elab: join(ORACLE_ROOT, 'run_elab_differential.mjs'),
  transform: join(ORACLE_ROOT, 'run_transform_differential.mjs'),
  smt: join(ORACLE_ROOT, 'run_smt_differential.mjs'),
  unsupported: join(ORACLE_ROOT, 'run_unsupported_gate.mjs'),
  result: join(ORACLE_ROOT, 'run_result_differential.mjs'),
  goldens: join(ORACLE_ROOT, 'manage_pr_goldens.mjs'),
  inspectToolchain: join(ORACLE_ROOT, 'inspect_toolchain.mjs'),
  generateToolchainLock: join(ORACLE_ROOT, 'generate_toolchain_lock.mjs'),
  promoteToolchainLock: join(ORACLE_ROOT, 'promote_toolchain_lock.mjs'),
  fixtures: join(PROJECT_ROOT, 'tools', 'check_why3_fixtures.mjs'),
};

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
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

export function parseOracleOptions(argv, { locks = false, quick = false } = {}) {
  const result = {
    why3Root: null,
    why3Archive: null,
    requireToolchainLock: false,
    skipToolchainLock: false,
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
    } else if (locks && option === '--require-toolchain-lock') {
      result.requireToolchainLock = true;
    } else if (locks && option === '--skip-toolchain-lock') {
      result.skipToolchainLock = true;
    } else if (quick && option === '--quick') {
      result.quick = true;
    } else {
      fail(`unknown option ${option}`);
    }
  }
  if (result.why3Root !== null && result.why3Archive !== null) {
    fail('--why3-root and --why3-archive are mutually exclusive');
  }
  if (result.requireToolchainLock && result.skipToolchainLock) {
    fail('--require-toolchain-lock and --skip-toolchain-lock are mutually exclusive');
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
    ...(options.requireToolchainLock ? ['--require-toolchain-lock'] : []),
    ...(options.skipToolchainLock ? ['--skip-toolchain-lock'] : []),
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

function smokeFixedOracle() {
  run(join(ORACLE_ROOT, 'run-fixed'), [
    'mvp.abs',
    '--',
    'prove',
    '--parse-only',
    'tools/why3_oracle/fixtures/mvp.mlw',
  ]);
}

const LAYERS = ['elab', 'transform', 'smt', 'unsupported'];

function runLayers(options, layers = LAYERS) {
  const source = sourceArguments(options);
  for (const layer of layers) {
    if (!LAYERS.includes(layer)) fail(`unknown oracle layer ${layer}`);
    runNode(SCRIPTS[layer], layer === 'unsupported' ? [] : source);
  }
}

export function parseGoldensOptions(argv) {
  const mode = argv[0];
  if (!['check', 'candidate', 'promote'].includes(mode)) {
    fail('goldens requires check, candidate, or promote');
  }
  const result = {
    mode,
    records: null,
    result: null,
    lock: null,
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
    if (!['--records', '--result', '--lock'].includes(option)) {
      fail(`unknown option ${option}`);
    }
    const value = resolve(requiredValue(argv, index, option));
    if (option === '--records') result.records = value;
    else if (option === '--result') result.result = value;
    else result.lock = value;
    index += 1;
  }
  if (mode === 'check') {
    if (argv.length !== 1) fail('goldens check does not accept paths or --compare');
  } else if (result.records === null || result.result === null) {
    fail(`goldens ${mode} requires --records and --result`);
  }
  if (mode !== 'candidate' && (result.lock !== null || result.compare)) {
    fail('--lock and --compare are valid only for goldens candidate');
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

function compareGoldenCandidate(options) {
  for (const name of STRUCTURAL_GOLDENS) {
    assertSameFile(join(options.records, name), join(GOLDEN_ROOT, name));
  }
  assertSameFile(options.result, join(GOLDEN_ROOT, 'prover-result.json'));
  process.stdout.write('goldens: candidate matches the checked-in oracle records\n');
}

export function renderGoldenLock(manifest, result) {
  const lock = JSON.parse(readFileSync(TOOLCHAIN_LOCK, 'utf8'));
  const updates = new Map([
    ['pr-golden-manifest-v1', sha256(manifest)],
    ['pr-prover-result-v1', sha256(result)],
  ]);
  for (const artifact of lock.contracts.artifacts) {
    const digest = updates.get(artifact.id);
    if (digest !== undefined) {
      artifact.sha256 = digest;
      updates.delete(artifact.id);
    }
  }
  if (updates.size !== 0) {
    fail(`toolchain lock is missing golden artifact(s): ${[...updates.keys()]}`);
  }
  delete lock.lockSha256;
  lock.lockSha256 = sha256(`${JSON.stringify(lock)}\n`);
  return `${JSON.stringify(lock, null, 2)}\n`;
}

function syncGoldenLock(mode, options = {}) {
  const records = options.records ?? GOLDEN_ROOT;
  const resultPath = options.result ?? join(GOLDEN_ROOT, 'prover-result.json');
  const output = options.lock ?? TOOLCHAIN_LOCK;
  const rendered = renderGoldenLock(
    readFileSync(join(records, 'manifest.json')),
    readFileSync(resultPath),
  );
  if (mode === 'check') {
    if (readFileSync(TOOLCHAIN_LOCK, 'utf8') !== rendered) {
      fail('repository toolchain lock does not bind the current PR goldens');
    }
    process.stdout.write('goldens: checked-in toolchain-lock hashes exact\n');
  } else if (mode === 'candidate') {
    if (existsSync(output)) fail(`candidate already exists: ${output}`);
    writeFileSync(output, rendered);
    process.stdout.write(`goldens: wrote toolchain-lock candidate ${output}\n`);
  } else {
    writeFileSync(TOOLCHAIN_LOCK, rendered);
    process.stdout.write('goldens: promoted hashes into the repository toolchain lock\n');
  }
}

function runGoldens(options) {
  if (options.mode === 'check') {
    runNode(SCRIPTS.goldens, ['--check']);
    syncGoldenLock('check');
    runNode(SCRIPTS.result, []);
    return;
  }

  if (options.mode === 'candidate') {
    runNode(SCRIPTS.goldens, ['--candidate', options.records]);
    runNode(SCRIPTS.result, ['--candidate', options.result]);
    if (options.lock !== null) {
      syncGoldenLock('candidate', options);
    }
    if (options.compare) compareGoldenCandidate(options);
    return;
  }

  runNode(SCRIPTS.goldens, ['--promote', options.records]);
  runNode(SCRIPTS.result, ['--promote', options.result]);
  syncGoldenLock('promote', options);
  runNode(SCRIPTS.contracts, ['--quick']);
}

function inspectToolchain({ output = null, print = false } = {}) {
  const report = runNode(SCRIPTS.inspectToolchain, [], { capture: true });
  JSON.parse(report);
  if (output !== null) writeFileSync(output, report);
  if (print) process.stdout.write(report);
  return report;
}

function runToolchain(argv) {
  const operation = argv[0];
  const rest = argv.slice(1);
  if (operation === 'inspect') {
    if (rest.length === 0) {
      inspectToolchain({ print: true });
      return;
    }
    if (rest.length !== 2 || rest[0] !== '--output') {
      fail('toolchain inspect accepts only [--output PATH]');
    }
    if (rest[1].startsWith('--')) fail('--output requires a path');
    inspectToolchain({ output: resolve(rest[1]) });
  } else if (operation === 'generate-lock') {
    runNode(SCRIPTS.generateToolchainLock, rest);
  } else if (operation === 'promote-lock') {
    runNode(SCRIPTS.promoteToolchainLock, rest);
  } else {
    fail('toolchain requires inspect, generate-lock, or promote-lock');
  }
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
  runNode(SCRIPTS.fixtures, []);

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
    '  contracts [--why3-root PATH | --why3-archive PATH] [lock options]',
    '  fixtures',
    '  layers [all|elab|transform|smt|unsupported] [source options]',
    '  goldens check',
    '  goldens candidate --records DIR --result PATH [--lock PATH] [--compare]',
    '  goldens promote --records DIR --result PATH',
    '  oracle [--why3-root PATH | --why3-archive PATH] [lock options]',
    '  project [--moon-diff-only]',
    '  toolchain inspect [--output PATH]',
    '  toolchain generate-lock OPTIONS...',
    '  toolchain promote-lock OPTIONS...',
    '',
    'lock options: --require-toolchain-lock | --skip-toolchain-lock',
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
    checkContracts(parseOracleOptions(rest, { locks: true, quick: true }));
  } else if (command === 'fixtures') {
    assertNoArguments(command, rest);
    runNode(SCRIPTS.fixtures, []);
  } else if (command === 'layers') {
    const layer = rest[0] !== undefined && !rest[0].startsWith('--')
      ? rest[0]
      : 'all';
    const options = parseOracleOptions(layer === 'all' && rest[0] !== 'all' ? rest : rest.slice(1));
    runLayers(options, layer === 'all' ? LAYERS : [layer]);
  } else if (command === 'goldens') {
    runGoldens(parseGoldensOptions(rest));
  } else if (command === 'oracle') {
    const options = parseOracleOptions(rest, { locks: true });
    inspectToolchain();
    checkContracts(options);
    smokeFixedOracle();
    runLayers(options);
    runGoldens(parseGoldensOptions(['check']));
  } else if (command === 'project') {
    if (rest.length > 1 || (rest.length === 1 && rest[0] !== '--moon-diff-only')) {
      fail('project accepts only [--moon-diff-only]');
    }
    checkProject({ moonDiffOnly: rest[0] === '--moon-diff-only' });
  } else if (command === 'toolchain') {
    runToolchain(rest);
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
