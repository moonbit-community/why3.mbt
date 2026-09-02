// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import { prepareReferenceRuntime } from './reference_runtime.mjs';
import { checkUpstreamSemantics } from './check_upstream_semantics.mjs';
import {
  acceptedResult,
  collectUpstreamCorpus,
  compareInventoryToContract,
  executeWithTimeout,
  mapConcurrent,
  typeOnlyArguments,
  validateUpstreamCorpusContract,
} from './upstream_corpus.mjs';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const DEFAULT_CONTRACT = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'upstream-corpus-v1.json',
);
const PRODUCT = join(
  PROJECT_ROOT,
  '_build',
  'native',
  'release',
  'build',
  'cmd',
  'why3',
  'why3.exe',
);

function fail(message) {
  throw new Error(message);
}

function requiredValue(argv, index, option) {
  const value = argv[index + 1];
  if (value === undefined || value.startsWith('--')) {
    fail(`${option} requires a value`);
  }
  return value;
}

export function parseCheckArguments(argv) {
  const result = {
    why3Root: null,
    why3Archive: null,
    contract: DEFAULT_CONTRACT,
  };
  const seen = new Set();
  for (let index = 0; index < argv.length; index += 1) {
    const option = argv[index];
    if (seen.has(option)) fail(`duplicate option ${option}`);
    seen.add(option);
    if (option !== '--why3-root' && option !== '--why3-archive' &&
        option !== '--contract') {
      fail(`unknown argument ${option}`);
    }
    const value = resolve(requiredValue(argv, index, option));
    if (option === '--why3-root') result.why3Root = value;
    else if (option === '--why3-archive') result.why3Archive = value;
    else result.contract = value;
    index += 1;
  }
  if (result.why3Root !== null && result.why3Archive !== null) {
    fail('--why3-root and --why3-archive are mutually exclusive');
  }
  return result;
}

function runChecked(command, argv) {
  const result = spawnSync(command, argv, {
    cwd: PROJECT_ROOT,
    encoding: 'utf8',
    env: process.env,
    maxBuffer: 128 * 1024 * 1024,
    shell: false,
  });
  if (result.status !== 0 || result.signal !== null ||
      (result.error && result.error.code !== 'EPERM')) {
    const detail =
      `${result.stdout ?? ''}${result.stderr ?? ''}${result.error?.message ?? ''}`
        .trim();
    fail(`${command} ${argv.join(' ')} failed: ${detail}`);
  }
}

function resultSummary(result) {
  return {
    status: result.status,
    signal: result.signal,
    timedOut: result.timedOut,
    durationMs: result.durationMs,
    stderr: result.stderr.slice(0, 1000),
    ...(result.error === null ? {} : { error: result.error }),
  };
}

export function productMismatch(entry, result) {
  if (result.timedOut || result.error !== null) return true;
  return acceptedResult(result) !== entry.accepted ||
    result.status !== entry.officialExitCode;
}

export async function checkUpstreamCorpus(options) {
  const contract = validateUpstreamCorpusContract(
    JSON.parse(readFileSync(options.contract, 'utf8')),
  );
  const runtime = prepareReferenceRuntime(options);
  const corpusRoot = options.why3Root ?? join(
    PROJECT_ROOT,
    'fixtures',
    'why3-1.7.2',
  );
  const inventory = collectUpstreamCorpus(corpusRoot);
  compareInventoryToContract(inventory, contract);
  runChecked('moon', ['build', '--target', 'native', '--release', 'cmd/why3']);

  const shortResults = await mapConcurrent(
    inventory.entries,
    6,
    entry => executeWithTimeout(
      PRODUCT,
      typeOnlyArguments(runtime.sourceRoot, entry.absolutePath),
      { cwd: PROJECT_ROOT, timeoutMs: 30_000 },
    ),
    { label: 'upstream-target-short' },
  );
  const retryIndices = shortResults
    .map((result, index) => result.timedOut ? index : -1)
    .filter(index => index >= 0);
  const retryResults = await mapConcurrent(
    retryIndices,
    3,
    index => executeWithTimeout(
      PRODUCT,
      typeOnlyArguments(
        runtime.sourceRoot,
        inventory.entries[index].absolutePath,
      ),
      { cwd: PROJECT_ROOT, timeoutMs: 1_200_000 },
    ),
    { label: 'upstream-target-long', progressEvery: 1 },
  );
  const finalResults = [...shortResults];
  retryIndices.forEach((index, retryIndex) => {
    finalResults[index] = retryResults[retryIndex];
  });

  const mismatches = contract.entries
    .map((entry, index) => ({
      entry,
      result: finalResults[index],
    }))
    .filter(({ entry, result }) => productMismatch(entry, result));
  if (mismatches.length !== 0) {
    const detail = mismatches.slice(0, 20).map(({ entry, result }) =>
      `${entry.path}: expected accepted=${entry.accepted}, ` +
      `exit=${entry.officialExitCode}; got ` +
      `${JSON.stringify(resultSummary(result))}`).join('\n');
    fail(
      `${mismatches.length}/${contract.entries.length} upstream type ` +
      `classification mismatch(es)\n${detail}`,
    );
  }
  process.stdout.write(
    `upstream type corpus: ${contract.counts.total}/${contract.counts.total} ` +
    `exact (${contract.counts.accepted} accepted / ` +
    `${contract.counts.rejected} rejected); ` +
    `${retryIndices.length} long-running target retries; ` +
    `set ${contract.entriesSha256}\n`,
  );
  const semantics = await checkUpstreamSemantics({
    runtime,
    inventory,
    contract,
  });
  return {
    total: contract.counts.total,
    accepted: contract.counts.accepted,
    rejected: contract.counts.rejected,
    retried: retryIndices.length,
    entriesSha256: contract.entriesSha256,
    semantics,
  };
}

export async function main(argv = process.argv.slice(2)) {
  return checkUpstreamCorpus(parseCheckArguments(argv));
}

const isMain = process.argv[1] !== undefined &&
  pathToFileURL(resolve(process.argv[1])).href === import.meta.url;

if (isMain) {
  main().catch(error => {
    process.stderr.write(`check_upstream_corpus: ${error.message}\n`);
    process.exitCode = 1;
  });
}
