// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import {
  readFileSync,
  writeFileSync,
} from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import referenceEnvironment from './reference_environment.cjs';
import { prepareReferenceRuntime } from './reference_runtime.mjs';
import {
  UPSTREAM_CORPUS_COUNTS,
  acceptedResult,
  canonicalSha,
  collectUpstreamCorpus,
  executeWithTimeout,
  mapConcurrent,
  typeOnlyArguments,
  validateUpstreamCorpusContract,
} from './upstream_corpus.mjs';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const DEFAULT_CONTRACT = resolve(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'upstream-corpus-v1.json',
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

export function parseGeneratorArguments(argv) {
  const result = {
    why3Root: null,
    why3Archive: null,
    output: DEFAULT_CONTRACT,
    check: false,
  };
  const seen = new Set();
  for (let index = 0; index < argv.length; index += 1) {
    const option = argv[index];
    if (seen.has(option)) fail(`duplicate option ${option}`);
    seen.add(option);
    if (option === '--why3-root' || option === '--why3-archive' ||
        option === '--output' || option === '--check') {
      const value = resolve(requiredValue(argv, index, option));
      if (option === '--why3-root') result.why3Root = value;
      else if (option === '--why3-archive') result.why3Archive = value;
      else {
        result.output = value;
        result.check = option === '--check';
      }
      index += 1;
    } else {
      fail(`unknown argument ${option}`);
    }
  }
  if (result.why3Root !== null && result.why3Archive !== null) {
    fail('--why3-root and --why3-archive are mutually exclusive');
  }
  if (seen.has('--output') && seen.has('--check')) {
    fail('--output and --check are mutually exclusive');
  }
  return result;
}

function renderedContract(contract) {
  return `${JSON.stringify(contract, null, 2)}\n`;
}

export async function generateUpstreamCorpus(options) {
  const runtime = prepareReferenceRuntime(options);
  referenceEnvironment.verifyReferenceEnvironment(runtime.lock);
  const corpusRoot = options.why3Root ?? join(
    PROJECT_ROOT,
    'fixtures',
    'why3-1.7.2',
  );
  const inventory = collectUpstreamCorpus(corpusRoot);
  const results = await mapConcurrent(
    inventory.entries,
    6,
    entry => executeWithTimeout(
      runtime.lock.why3.runtime.executable,
      typeOnlyArguments(runtime.sourceRoot, entry.absolutePath),
      { cwd: PROJECT_ROOT, timeoutMs: 30_000 },
    ),
    { label: 'upstream-reference' },
  );
  const failedToRun = results
    .map((result, index) => ({ result, entry: inventory.entries[index] }))
    .filter(({ result }) => result.timedOut || result.error !== null);
  if (failedToRun.length !== 0) {
    const { entry, result } = failedToRun[0];
    fail(
      `reference execution failed for ${entry.path}: ` +
      `${JSON.stringify(result)}`,
    );
  }
  const entries = inventory.entries.map((entry, index) => ({
    path: entry.path,
    kind: entry.kind,
    ...(entry.kind === 'symlink'
      ? { symlinkTarget: entry.symlinkTarget }
      : {}),
    sourceSha256: entry.sourceSha256,
    accepted: acceptedResult(results[index]),
    officialExitCode: results[index].status,
  }));
  const accepted = entries.filter(entry => entry.accepted).length;
  const counts = {
    ...inventory.counts,
    accepted,
    rejected: entries.length - accepted,
  };
  if (JSON.stringify(counts) !== JSON.stringify(UPSTREAM_CORPUS_COUNTS)) {
    fail(
      `reference acceptance count drift: expected ` +
      `${JSON.stringify(UPSTREAM_CORPUS_COUNTS)}, got ${JSON.stringify(counts)}`,
    );
  }
  return validateUpstreamCorpusContract({
    schemaVersion: 1,
    profile: 'why3-1.7.2-upstream-type-corpus-v1',
    why3: {
      version: runtime.lock.why3.version,
      commit: runtime.lock.why3.commit,
      tree: runtime.lock.why3.tree,
    },
    policy: {
      roots: ['examples', 'tests'],
      excludedRoot: 'examples_in_progress',
      extensions: ['.mlw', '.why'],
      entryOrder: 'root-relative path bytewise ascending',
      sourceHash: 'SHA-256 of exact source bytes after resolving a symlink',
      referenceCommand:
        'why3 prove --no-load-default-plugins --no-stdlib ' +
        '-L <stdlib> -L <source-directory> --type-only <source>',
      targetCommand:
        'why3mbt prove --no-load-default-plugins --no-stdlib ' +
        '-L <stdlib> -L <source-directory> --type-only <source>',
      comparison: 'exact accepted/rejected classification and process exit code',
      languageFeatureExemptions: 0,
    },
    counts,
    entries,
    entriesSha256: canonicalSha(entries),
  });
}

export async function main(argv = process.argv.slice(2)) {
  const options = parseGeneratorArguments(argv);
  const contract = await generateUpstreamCorpus(options);
  const rendered = renderedContract(contract);
  if (options.check) {
    const current = readFileSync(options.output, 'utf8');
    if (current !== rendered) {
      fail(`${options.output} is stale; regenerate the upstream corpus contract`);
    }
    process.stdout.write(
      `upstream corpus contract exact: ${contract.counts.total} files, ` +
      `${contract.counts.accepted} accepted / ` +
      `${contract.counts.rejected} rejected\n`,
    );
  } else {
    writeFileSync(options.output, rendered);
    process.stdout.write(`wrote ${options.output}\n`);
  }
}

const isMain = process.argv[1] !== undefined &&
  pathToFileURL(resolve(process.argv[1])).href === import.meta.url;

if (isMain) {
  main().catch(error => {
    process.stderr.write(`generate_upstream_corpus: ${error.message}\n`);
    process.exitCode = 1;
  });
}
