// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawn } from 'node:child_process';
import {
  lstatSync,
  readFileSync,
  readdirSync,
  readlinkSync,
} from 'node:fs';
import { dirname, join, relative, resolve, sep } from 'node:path';

export const UPSTREAM_CORPUS_COUNTS = Object.freeze({
  examples: 446,
  tests: 58,
  total: 504,
  accepted: 459,
  rejected: 45,
});

const SOURCE_EXTENSIONS = new Set(['.mlw', '.why']);

export function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

export function canonicalSha(value) {
  return sha256(`${JSON.stringify(value)}\n`);
}

export function compareUtf8(left, right) {
  return Buffer.compare(Buffer.from(left, 'utf8'), Buffer.from(right, 'utf8'));
}

function toPosix(path) {
  return path.split(sep).join('/');
}

function hasWhymlExtension(name) {
  for (const extension of SOURCE_EXTENSIONS) {
    if (name.endsWith(extension)) return true;
  }
  return false;
}

function collectFiles(root, directory, entries) {
  for (const child of readdirSync(directory, { withFileTypes: true })
    .sort((left, right) => compareUtf8(left.name, right.name))) {
    const absolutePath = join(directory, child.name);
    if (child.isDirectory()) {
      collectFiles(root, absolutePath, entries);
      continue;
    }
    if (!hasWhymlExtension(child.name)) continue;
    const metadata = lstatSync(absolutePath);
    const kind = metadata.isSymbolicLink() ? 'symlink' : 'regular';
    if (kind === 'regular' && !metadata.isFile()) {
      throw new Error(`unsupported upstream corpus entry ${absolutePath}`);
    }
    entries.push({
      path: toPosix(relative(root, absolutePath)),
      kind,
      ...(kind === 'symlink'
        ? { symlinkTarget: readlinkSync(absolutePath) }
        : {}),
      sourceSha256: sha256(readFileSync(absolutePath)),
      absolutePath,
    });
  }
}

export function collectUpstreamCorpus(why3Root) {
  const root = resolve(why3Root);
  const examples = [];
  const tests = [];
  collectFiles(root, join(root, 'examples'), examples);
  collectFiles(root, join(root, 'tests'), tests);
  const entries = [...examples, ...tests]
    .sort((left, right) => compareUtf8(left.path, right.path));
  const counts = {
    examples: examples.length,
    tests: tests.length,
    total: entries.length,
  };
  for (const field of ['examples', 'tests', 'total']) {
    if (counts[field] !== UPSTREAM_CORPUS_COUNTS[field]) {
      throw new Error(
        `upstream ${field} count drift: expected ` +
        `${UPSTREAM_CORPUS_COUNTS[field]}, got ${counts[field]}`,
      );
    }
  }
  return { root, counts, entries };
}

export function typeOnlyArguments(why3Root, sourcePath) {
  return [
    'prove',
    '--no-load-default-plugins',
    '--no-stdlib',
    '-L',
    join(resolve(why3Root), 'stdlib'),
    '-L',
    dirname(resolve(sourcePath)),
    '--type-only',
    resolve(sourcePath),
  ];
}

export function acceptedResult(result) {
  return result.status === 0 && !result.timedOut;
}

export function executeWithTimeout(
  command,
  argv,
  { cwd, timeoutMs, stderrLimit = 16 * 1024 } = {},
) {
  return new Promise(resolveResult => {
    const started = Date.now();
    const child = spawn(command, argv, {
      cwd,
      stdio: ['ignore', 'ignore', 'pipe'],
      shell: false,
    });
    let stderr = '';
    let timedOut = false;
    let settled = false;
    const finish = result => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      resolveResult({
        ...result,
        timedOut,
        durationMs: Date.now() - started,
        stderr: stderr.trim(),
      });
    };
    const timer = setTimeout(() => {
      timedOut = true;
      child.kill('SIGKILL');
    }, timeoutMs);
    child.stderr.setEncoding('utf8');
    child.stderr.on('data', chunk => {
      if (stderr.length < stderrLimit) {
        stderr += chunk.slice(0, stderrLimit - stderr.length);
      }
    });
    child.on('error', error => {
      finish({ status: -1, signal: null, error: error.message });
    });
    child.on('close', (status, signal) => {
      finish({ status: status ?? -1, signal, error: null });
    });
  });
}

export async function mapConcurrent(
  entries,
  concurrency,
  operation,
  { label, progressEvery = 25 } = {},
) {
  if (!Number.isInteger(concurrency) || concurrency < 1) {
    throw new Error('concurrency must be a positive integer');
  }
  const results = new Array(entries.length);
  let cursor = 0;
  let completed = 0;
  async function worker() {
    for (;;) {
      const index = cursor;
      cursor += 1;
      if (index >= entries.length) return;
      results[index] = await operation(entries[index], index);
      completed += 1;
      if (label !== undefined &&
          (completed % progressEvery === 0 || completed === entries.length)) {
        process.stdout.write(`[${label}] ${completed}/${entries.length}\n`);
      }
    }
  }
  await Promise.all(
    Array.from({ length: Math.min(concurrency, entries.length) }, worker),
  );
  return results;
}

function assertExactKeys(value, expected, label) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    throw new Error(`${label} must be an object`);
  }
  const actual = Object.keys(value).sort();
  const wanted = [...expected].sort();
  if (JSON.stringify(actual) !== JSON.stringify(wanted)) {
    throw new Error(
      `${label} keys: expected ${wanted.join(', ')}, got ${actual.join(', ')}`,
    );
  }
}

export function validateUpstreamCorpusContract(contract) {
  assertExactKeys(
    contract,
    [
      'schemaVersion',
      'profile',
      'why3',
      'policy',
      'counts',
      'entries',
      'entriesSha256',
    ],
    'upstream corpus contract',
  );
  if (contract.schemaVersion !== 1 ||
      contract.profile !== 'why3-1.7.2-upstream-type-corpus-v1') {
    throw new Error('unsupported upstream corpus contract');
  }
  assertExactKeys(contract.why3, ['version', 'commit', 'tree'], 'contract Why3');
  if (contract.why3.version !== '1.7.2' ||
      contract.why3.commit !== '1343338d3bb1941c0d4f134283bb0790816113c4' ||
      contract.why3.tree !== 'f5e82693620413d7d8e3ebcba69addcb6a65f877') {
    throw new Error('upstream corpus Why3 identity drift');
  }
  assertExactKeys(
    contract.policy,
    [
      'roots',
      'excludedRoot',
      'extensions',
      'entryOrder',
      'sourceHash',
      'referenceCommand',
      'targetCommand',
      'comparison',
      'languageFeatureExemptions',
    ],
    'upstream corpus policy',
  );
  if (JSON.stringify(contract.policy.roots) !==
        JSON.stringify(['examples', 'tests']) ||
      contract.policy.excludedRoot !== 'examples_in_progress' ||
      JSON.stringify(contract.policy.extensions) !==
        JSON.stringify(['.mlw', '.why']) ||
      contract.policy.languageFeatureExemptions !== 0) {
    throw new Error('upstream corpus policy drift');
  }
  assertExactKeys(
    contract.counts,
    ['examples', 'tests', 'total', 'accepted', 'rejected'],
    'upstream corpus counts',
  );
  if (JSON.stringify(contract.counts) !==
      JSON.stringify(UPSTREAM_CORPUS_COUNTS)) {
    throw new Error(
      `upstream corpus counts drift: ${JSON.stringify(contract.counts)}`,
    );
  }
  if (!Array.isArray(contract.entries) ||
      contract.entries.length !== UPSTREAM_CORPUS_COUNTS.total) {
    throw new Error('upstream corpus entries have the wrong length');
  }
  const paths = contract.entries.map(entry => entry.path);
  if (JSON.stringify(paths) !==
      JSON.stringify([...paths].sort(compareUtf8)) ||
      new Set(paths).size !== paths.length) {
    throw new Error('upstream corpus paths are not unique bytewise order');
  }
  for (const entry of contract.entries) {
    assertExactKeys(
      entry,
      [
        'path',
        'kind',
        ...(entry.kind === 'symlink' ? ['symlinkTarget'] : []),
        'sourceSha256',
        'accepted',
        'officialExitCode',
      ],
      `upstream entry ${entry.path}`,
    );
    if (!entry.path.startsWith('examples/') &&
        !entry.path.startsWith('tests/')) {
      throw new Error(`${entry.path} is outside the upstream corpus roots`);
    }
    if (entry.path.startsWith('examples_in_progress/')) {
      throw new Error(`${entry.path} includes examples_in_progress`);
    }
    if (entry.kind !== 'regular' && entry.kind !== 'symlink') {
      throw new Error(`${entry.path} has invalid source kind`);
    }
    if (!/^[0-9a-f]{64}$/u.test(entry.sourceSha256) ||
        typeof entry.accepted !== 'boolean' ||
        !Number.isInteger(entry.officialExitCode) ||
        entry.officialExitCode < 0) {
      throw new Error(`${entry.path} has invalid contract metadata`);
    }
    if (entry.accepted !== (entry.officialExitCode === 0)) {
      throw new Error(`${entry.path} acceptance and exit code disagree`);
    }
  }
  const accepted = contract.entries.filter(entry => entry.accepted).length;
  if (accepted !== contract.counts.accepted ||
      contract.entries.length - accepted !== contract.counts.rejected) {
    throw new Error('upstream corpus acceptance counts drift');
  }
  if (contract.entriesSha256 !== canonicalSha(contract.entries)) {
    throw new Error('upstream corpus entry hash drift');
  }
  return contract;
}

export function compareInventoryToContract(inventory, contract) {
  validateUpstreamCorpusContract(contract);
  const actual = inventory.entries.map(entry => ({
    path: entry.path,
    kind: entry.kind,
    ...(entry.kind === 'symlink'
      ? { symlinkTarget: entry.symlinkTarget }
      : {}),
    sourceSha256: entry.sourceSha256,
  }));
  const expected = contract.entries.map(entry => ({
    path: entry.path,
    kind: entry.kind,
    ...(entry.kind === 'symlink'
      ? { symlinkTarget: entry.symlinkTarget }
      : {}),
    sourceSha256: entry.sourceSha256,
  }));
  if (JSON.stringify(actual) !== JSON.stringify(expected)) {
    const mismatch = actual.findIndex(
      (entry, index) => JSON.stringify(entry) !== JSON.stringify(expected[index]),
    );
    throw new Error(
      `upstream corpus source inventory drift at entry ${mismatch}: ` +
      `expected ${JSON.stringify(expected[mismatch])}, ` +
      `got ${JSON.stringify(actual[mismatch])}`,
    );
  }
}
