// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import {
  lstatSync,
  mkdirSync,
  readFileSync,
  readlinkSync,
  readdirSync,
} from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import {
  ensureRuntimeDependencies,
} from './why3_reference/reference_runtime.mjs';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const REFERENCE_ROOT = join(PROJECT_ROOT, 'tools', 'why3_reference');

const SCRIPTS = {
  contracts: join(PROJECT_ROOT, 'tools', 'check_contracts.mjs'),
  elab: join(REFERENCE_ROOT, 'run_elab_differential.mjs'),
  transform: join(REFERENCE_ROOT, 'run_transform_differential.mjs'),
  smt: join(REFERENCE_ROOT, 'run_smt_differential.mjs'),
  result: join(REFERENCE_ROOT, 'run_result_differential.mjs'),
  fixtures: join(PROJECT_ROOT, 'tools', 'check_whyml_parser.mjs'),
  upstream: join(REFERENCE_ROOT, 'check_upstream_corpus.mjs'),
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

export function parseCheckOptions(argv) {
  let moonDiffOnly = false;
  const referenceArguments = [];
  for (const option of argv) {
    if (option === '--moon-diff-only') {
      if (moonDiffOnly) fail(`duplicate option ${option}`);
      moonDiffOnly = true;
    } else {
      referenceArguments.push(option);
    }
  }
  return {
    ...parseReferenceOptions(referenceArguments),
    moonDiffOnly,
  };
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

function checkUpstreamCorpus(options) {
  runNode(SCRIPTS.upstream, sourceArguments(options));
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

const LAYERS = ['elab', 'transform', 'smt', 'result'];

function runLayers(options, layers = LAYERS) {
  const source = sourceArguments(options);
  for (const layer of layers) {
    if (!LAYERS.includes(layer)) fail(`unknown reference layer ${layer}`);
    runNode(SCRIPTS[layer], layer === 'result' ? [] : source);
  }
}

function projectPathNames({ moonDiffOnly = false } = {}) {
  const output = run('git', [
    'ls-files',
    '--cached',
    '--others',
    '--exclude-standard',
    '-z',
  ], { capture: true });
  return output
    .split('\0')
    .filter(name => name !== '')
    .filter(name => !moonDiffOnly || name.endsWith('.mbt') || name.endsWith('.mbti'))
    .sort();
}

function projectPathDigest(name) {
  const path = join(PROJECT_ROOT, name);
  let stat;
  try {
    stat = lstatSync(path);
  } catch (error) {
    if (error.code === 'ENOENT') return '<missing>';
    throw error;
  }
  if (stat.isSymbolicLink()) return `symlink:${readlinkSync(path)}`;
  if (!stat.isFile()) return `<${stat.isDirectory() ? 'directory' : 'special'}>`;
  return createHash('sha256').update(readFileSync(path)).digest('hex');
}

export function captureProjectState(options = {}) {
  return new Map(projectPathNames(options).map(name => [
    name,
    projectPathDigest(name),
  ]));
}

export function changedProjectPaths(before, after) {
  const names = new Set([...before.keys(), ...after.keys()]);
  return [...names]
    .filter(name => before.get(name) !== after.get(name))
    .sort();
}

function assertProjectUnchanged(before, options, operation) {
  const changed = changedProjectPaths(before, captureProjectState(options));
  if (changed.length !== 0) {
    fail(
      `${operation} changed project files:\n` +
      changed.map(name => `  ${name}`).join('\n'),
    );
  }
}

function checkProjectHygiene(options, initialState) {
  run('moon', ['check', '--target', 'all']);
  run('moon', ['info']);
  assertProjectUnchanged(initialState, options, 'moon info');
  run('moon', ['fmt']);
  assertProjectUnchanged(initialState, options, 'moon fmt');
}

function runQuickTests() {
  run('sh', [join(PROJECT_ROOT, 'tools', 'check_native_runner_asan.sh')]);

  const nodeTests = readdirSync(join(PROJECT_ROOT, 'tools'))
    .filter(name => name.endsWith('.test.mjs'))
    .sort()
    .map(name => join('tools', name));
  if (nodeTests.length === 0) fail('no Node.js tool tests found');
  run(process.execPath, ['--test', ...nodeTests]);
}

function runProjectTests() {
  run('moon', ['test', '--target', 'all', '--serial', '--release']);
  run('moon', ['test', '--target', 'all', '--serial']);
}

export function runCheckPipeline(options, actions) {
  const projectOptions = { moonDiffOnly: options.moonDiffOnly };
  actions.projectHygiene(projectOptions);
  actions.quickTests();
  actions.smoke();
  actions.projectTests();
  actions.fixtures();
  actions.preflight();
  actions.contracts(options);
  actions.upstream(options);
  actions.layers(options);
  actions.finalCleanliness(projectOptions);
}

function check(options) {
  const projectOptions = { moonDiffOnly: options.moonDiffOnly };
  const initialState = captureProjectState(projectOptions);
  runCheckPipeline(options, {
    projectHygiene: current => checkProjectHygiene(current, initialState),
    quickTests: runQuickTests,
    smoke: smokeFixedReference,
    projectTests: runProjectTests,
    fixtures: () => runNode(SCRIPTS.fixtures, []),
    preflight: ensureRuntimeDependencies,
    contracts: checkContracts,
    upstream: checkUpstreamCorpus,
    layers: runLayers,
    finalCleanliness: current =>
      assertProjectUnchanged(initialState, current, 'check pipeline'),
  });
}

function usage() {
  return [
    'usage: node tools/run.mjs COMMAND [OPTIONS]',
    '',
    'commands:',
    '  bootstrap',
    '  contracts [--why3-root PATH | --why3-archive PATH] [--quick]',
    '  fixtures',
    '  upstream [--why3-root PATH | --why3-archive PATH]',
    '  layers [all|elab|transform|smt|result] [source options]',
    '  check [--moon-diff-only] [--why3-root PATH | --why3-archive PATH]',
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
  } else if (command === 'upstream') {
    checkUpstreamCorpus(parseReferenceOptions(rest));
  } else if (command === 'layers') {
    const layer = rest[0] !== undefined && !rest[0].startsWith('--')
      ? rest[0]
      : 'all';
    const options = parseReferenceOptions(layer === 'all' && rest[0] !== 'all' ? rest : rest.slice(1));
    runLayers(options, layer === 'all' ? LAYERS : [layer]);
  } else if (command === 'check') {
    check(parseCheckOptions(rest));
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
