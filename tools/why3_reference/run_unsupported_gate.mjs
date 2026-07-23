#!/usr/bin/env node
// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import {
  existsSync,
  mkdtempSync,
  readFileSync,
  rmSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const CORPUS_PATH = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'pr-corpus-v1.json',
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

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function run(command, argv, expectedStatus) {
  const result = spawnSync(command, argv, {
    cwd: PROJECT_ROOT,
    encoding: 'utf8',
    env: { ...process.env, LC_ALL: 'C', LANG: 'C', TZ: 'UTC' },
    maxBuffer: 64 * 1024 * 1024,
    shell: false,
  });
  // The managed workspace may report EPERM alongside a valid child status.
  // Preserve the real exit-status checks while ignoring that wrapper artifact.
  if (result.error && result.error.code !== 'EPERM') throw result.error;
  if (result.signal !== null || result.status !== expectedStatus) {
    fail(
      `${command} ${argv.join(' ')} returned ${result.status}/${result.signal}: ` +
      `${(result.stderr ?? '').trim()}`,
    );
  }
  return result;
}

function buildExecutables() {
  run('moon', ['build', '--target', 'native', 'cmd/elab_canonical'], 0);
  run('moon', ['build', '--target', 'native', 'cmd/why3'], 0);
  if (!existsSync(ELABORATOR) || !existsSync(CLI)) {
    fail('native reference/CLI executables were not produced');
  }
}

function parseDiagnostic(entry, output) {
  const lines = output.trimEnd().split('\n');
  if (lines.length !== 1) {
    fail(`${entry.id}: expected one diagnostic record, got ${lines.length}`);
  }
  let diagnostic;
  try {
    diagnostic = JSON.parse(lines[0]);
  } catch (error) {
    fail(`${entry.id}: malformed diagnostic JSON: ${error.message}`);
  }
  if (diagnostic.accepted !== false ||
      diagnostic.stage !== entry.expected.stage ||
      diagnostic.kind !== entry.expected.kind ||
      (diagnostic.relative_path_hex !== null &&
       diagnostic.relative_path_hex !== Buffer.from(entry.source.path, 'utf8').toString('hex'))) {
    fail(
      `${entry.id}: expected ${entry.expected.stage}/${entry.expected.kind}, got ` +
      `${JSON.stringify(diagnostic)}`,
    );
  }
  return diagnostic;
}

function expectedKindMarker(entry) {
  const match = /\(([^()]*)\)$/u.exec(entry.expected.kind);
  if (match === null || match[1] === '') {
    fail(`${entry.id}: expected kind has no stable marker`);
  }
  return match[1];
}

function assertRejectedBeforeOutput(entry, result, outputDirectory, operation) {
  if (result.stdout !== '') {
    fail(`${entry.id}: ${operation} unexpectedly emitted stdout`);
  }
  if (existsSync(outputDirectory)) {
    fail(`${entry.id}: ${operation} unexpectedly created ${outputDirectory}`);
  }
  const marker = expectedKindMarker(entry);
  if (!result.stderr.includes(marker)) {
    fail(
      `${entry.id}: ${operation} did not preserve rejection marker ${marker}: ` +
      `${result.stderr.trim()}`,
    );
  }
  for (const forbidden of [
    'ExecutableNotFound',
    'SpawnFailed',
    'MalformedProverOutput',
    'OutputLimitExceeded',
  ]) {
    if (result.stderr.includes(forbidden)) {
      fail(`${entry.id}: ${operation} reached prover infrastructure (${forbidden})`);
    }
  }
}

function main() {
  const corpus = JSON.parse(readFileSync(CORPUS_PATH, 'utf8'));
  const entries = corpus.entries.filter(entry => entry.id.startsWith('unsupported.'));
  if (entries.length === 0) fail('PR corpus has no unsupported entries');
  buildExecutables();
  const directory = mkdtempSync(join(tmpdir(), 'why3mbt-unsupported-gate-'));
  try {
    for (const entry of entries) {
      const source = join(PROJECT_ROOT, entry.source.path);
      const actualSourceSha256 = sha256(readFileSync(source));
      if (actualSourceSha256 !== entry.source.sha256) {
        fail(`${entry.id}: source hash drift`);
      }
      if (entry.expected.stage !== 'parser') {
        const diagnostic = run(
          ELABORATOR,
          ['--stage', 'diagnostic', entry.source.path],
          0,
        );
        if (diagnostic.stderr !== '') {
          fail(`${entry.id}: diagnostic command emitted stderr`);
        }
        parseDiagnostic(entry, diagnostic.stdout);
      }

      const emitDirectory = join(directory, `${entry.id}.emit`);
      const emitted = run(
        CLI,
        ['emit-smt', entry.source.path, '-o', emitDirectory, '--json'],
        1,
      );
      assertRejectedBeforeOutput(entry, emitted, emitDirectory, 'emit-smt');

      const proveDirectory = join(directory, `${entry.id}.prove`);
      const proved = run(
        CLI,
        [
          'prove',
          entry.source.path,
          '--z3',
          join(proveDirectory, 'must-not-run-z3'),
          '--json',
        ],
        1,
      );
      assertRejectedBeforeOutput(entry, proved, proveDirectory, 'prove');
    }
    process.stdout.write(
      `run_unsupported_gate: ${entries.length}/${entries.length} fixtures ` +
      'rejected before SMT output and prover resolution\n',
    );
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

try {
  main();
} catch (error) {
  process.stderr.write(`run_unsupported_gate: ${error.message}\n`);
  process.exitCode = 1;
}
