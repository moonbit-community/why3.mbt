// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash, randomBytes } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import {
  closeSync,
  existsSync,
  fsyncSync,
  openSync,
  readFileSync,
  renameSync,
  statSync,
  unlinkSync,
  writeFileSync,
} from 'node:fs';
import { basename, dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import { validateToolchainLock } from '../check_pr00_contracts.mjs';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const GENERATOR = join(SCRIPT_DIRECTORY, 'generate_toolchain_lock.mjs');
const LOCK_PATH = 'tools/contracts/toolchain-lock.json';
const CHECK_WORKFLOW_PATH = '.github/workflows/check.yml';
const CANDIDATE_IMAGE_LINE =
  '      image: ghcr.io/${{ github.repository }}-why3:1.7.2-z3-4.8.12';
const CANDIDATE_JOB_NAME = '    name: fixed oracle candidate';
const FIXED_JOB_NAME = '    name: fixed oracle';
const CANDIDATE_VERIFY_NAME = '      - name: Verify candidate image contents';
const FIXED_VERIFY_NAME = '      - name: Verify fixed image contents';
const CONTRACT_CHECK = [
  '          node tools/check_pr00_contracts.mjs \\',
  '            --why3-archive "$WHY3_REFERENCE_ARCHIVE"',
].join('\n');
const LOCKED_CONTRACT_CHECK = [
  `${CONTRACT_CHECK} \\`,
  '            --require-toolchain-lock',
].join('\n');
const RUNNER_CONTRACT_CHECK = [
  '          node tools/run.mjs contracts \\',
  '            --why3-archive "$WHY3_REFERENCE_ARCHIVE"',
].join('\n');
const RUNNER_ORACLE_CHECK = [
  '          node tools/run.mjs oracle \\',
  '            --why3-archive "$WHY3_REFERENCE_ARCHIVE" \\',
  '            --require-toolchain-lock',
].join('\n');
const SMOKE_STEP = [
  '      - name: Smoke fixed Why3 entrypoint',
  '        run: |',
  '          tools/why3_oracle/run-fixed mvp.abs -- \\',
  '            prove --parse-only tools/why3_oracle/fixtures/mvp.mlw',
  '',
].join('\n');
const DIGEST_PATTERN = /^sha256:[0-9a-f]{64}$/u;

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function literalCount(source, literal) {
  return source.split(literal).length - 1;
}

function replaceExactlyOnce(source, before, after, description) {
  const count = literalCount(source, before);
  if (count !== 1) fail(`expected exactly one ${description}, found ${count}`);
  return source.replace(before, after);
}

function assertLockImage(lock) {
  if (!DIGEST_PATTERN.test(lock?.image?.digest ?? '')) fail('candidate has an invalid image digest');
  if (lock.image.repository !== 'ghcr.io/moonbit-community/why3.mbt-why3') {
    fail('candidate has an unexpected image repository');
  }
  if (lock.image.reference !== `${lock.image.repository}@${lock.image.digest}`) {
    fail('candidate image reference does not match its repository and digest');
  }
}

function assertPromotedWorkflow(source, lock) {
  const required = [
    [FIXED_JOB_NAME, 'fixed job name'],
    [`      image: ${lock.image.reference}`, 'locked image reference'],
    [`      WHY3_ORACLE_IMAGE_DIGEST: ${lock.image.digest}`, 'locked digest environment'],
    ['            --require-toolchain-lock', 'required-lock contract argument'],
  ];
  for (const [literal, description] of required) {
    const count = literalCount(source, literal);
    if (count !== 1) fail(`promoted workflow must contain exactly one ${description}, found ${count}`);
  }
  const smokeCount = literalCount(
    source,
    '          tools/why3_oracle/run-fixed mvp.abs -- \\',
  ) + literalCount(source, '          node tools/run.mjs oracle \\');
  if (smokeCount !== 1) {
    fail(
      'promoted workflow must contain exactly one fixed-entrypoint smoke task, ' +
      `found ${smokeCount}`,
    );
  }
  for (const [literal, description] of [
    [CANDIDATE_JOB_NAME, 'candidate job name'],
    [CANDIDATE_IMAGE_LINE, 'moving candidate image'],
    [CANDIDATE_VERIFY_NAME, 'candidate verification step name'],
  ]) {
    if (source.includes(literal)) fail(`promoted workflow still contains the ${description}`);
  }
}

export function renderCheckWorkflow(source, lock, { previousLock = null } = {}) {
  assertLockImage(lock);
  if (source.includes('\r')) fail('check workflow must use LF line endings');

  const targetImageLine = `      image: ${lock.image.reference}`;
  if (source.includes(targetImageLine)) {
    assertPromotedWorkflow(source, lock);
    return source;
  }

  if (previousLock !== null) {
    assertLockImage(previousLock);
    assertPromotedWorkflow(source, previousLock);
    let rendered = replaceExactlyOnce(
      source,
      `      image: ${previousLock.image.reference}`,
      targetImageLine,
      'previous locked image reference',
    );
    rendered = replaceExactlyOnce(
      rendered,
      `      WHY3_ORACLE_IMAGE_DIGEST: ${previousLock.image.digest}`,
      `      WHY3_ORACLE_IMAGE_DIGEST: ${lock.image.digest}`,
      'previous locked digest environment',
    );
    assertPromotedWorkflow(rendered, lock);
    return rendered;
  }

  if (!source.includes(CANDIDATE_IMAGE_LINE)) {
    fail('check workflow is neither the exact candidate form nor the candidate lock form');
  }
  let rendered = replaceExactlyOnce(
    source,
    CANDIDATE_JOB_NAME,
    FIXED_JOB_NAME,
    'candidate job name',
  );
  rendered = replaceExactlyOnce(
    rendered,
    CANDIDATE_VERIFY_NAME,
    FIXED_VERIFY_NAME,
    'candidate verification step name',
  );
  rendered = replaceExactlyOnce(
    rendered,
    CANDIDATE_IMAGE_LINE,
    targetImageLine,
    'moving candidate image',
  );
  rendered = replaceExactlyOnce(
    rendered,
    '    runs-on: ubuntu-24.04\n    container:',
    `    runs-on: ubuntu-24.04\n    env:\n` +
      `      WHY3_ORACLE_IMAGE_DIGEST: ${lock.image.digest}\n    container:`,
    'oracle job runner/container boundary',
  );
  if (rendered.includes(RUNNER_CONTRACT_CHECK)) {
    rendered = replaceExactlyOnce(
      rendered,
      RUNNER_CONTRACT_CHECK,
      RUNNER_ORACLE_CHECK,
      'candidate consolidated oracle check',
    );
  } else {
    rendered = replaceExactlyOnce(
      rendered,
      CONTRACT_CHECK,
      LOCKED_CONTRACT_CHECK,
      'candidate contract check',
    );
    rendered = replaceExactlyOnce(
      rendered,
      '      - name: Check all targets\n',
      `${SMOKE_STEP}      - name: Check all targets\n`,
      'all-target check anchor',
    );
  }
  assertPromotedWorkflow(rendered, lock);
  return rendered;
}

function parseArguments(argv) {
  const result = {
    candidate: null,
    report: null,
    projectRoot: PROJECT_ROOT,
    promote: false,
    replaceExistingLock: false,
  };
  const seen = new Set();
  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index];
    if (seen.has(argument)) fail(`duplicate argument ${argument}`);
    seen.add(argument);
    if (argument === '--promote') result.promote = true;
    else if (argument === '--replace-existing-lock') result.replaceExistingLock = true;
    else if (argument === '--candidate' || argument === '--report' || argument === '--project-root') {
      const value = argv[index + 1];
      if (!value || value.startsWith('--')) fail(`${argument} requires a path`);
      if (argument === '--candidate') result.candidate = resolve(value);
      else if (argument === '--report') result.report = resolve(value);
      else result.projectRoot = resolve(value);
      index += 1;
    } else if (argument === '--help') {
      process.stdout.write(
        'usage: promote_toolchain_lock.mjs --candidate PATH --report PATH ' +
        '[--replace-existing-lock] [--promote]\n',
      );
      process.exit(0);
    } else fail(`unknown argument ${argument}`);
  }
  if (result.candidate === null || result.report === null) {
    fail('--candidate and --report are required');
  }
  return result;
}

function runGeneratorCheck(candidateBytes, reportPath, candidate) {
  const result = spawnSync(process.execPath, [
    GENERATOR,
    '--report',
    reportPath,
    '--image-digest',
    candidate.image.digest,
    '--build-recipe-commit',
    candidate.buildRecipe?.commit ?? '',
  ], {
    cwd: PROJECT_ROOT,
    encoding: 'utf8',
    env: { ...process.env, LC_ALL: 'C' },
    maxBuffer: 16 * 1024 * 1024,
    shell: false,
  });
  if (result.status !== 0 || result.signal !== null || result.error) {
    const detail = `${result.stdout ?? ''}${result.stderr ?? ''}${result.error?.message ?? ''}`.trim();
    fail(`candidate/report reproduction failed: ${detail}`);
  }
  if (result.stdout !== candidateBytes.toString('utf8')) {
    fail('candidate bytes do not match the lock reproduced from the report');
  }
}

function atomicWrite(path, bytes) {
  const mode = existsSync(path) ? statSync(path).mode : 0o644;
  const temporary = join(
    dirname(path),
    `.${basename(path)}.promote-${process.pid}-${randomBytes(8).toString('hex')}`,
  );
  let descriptor = null;
  try {
    descriptor = openSync(temporary, 'wx', mode);
    writeFileSync(descriptor, bytes);
    fsyncSync(descriptor);
    closeSync(descriptor);
    descriptor = null;
    renameSync(temporary, path);
  } catch (error) {
    if (descriptor !== null) closeSync(descriptor);
    if (existsSync(temporary)) unlinkSync(temporary);
    throw error;
  }
}

function restore(path, previousBytes) {
  if (previousBytes === null) {
    if (existsSync(path)) unlinkSync(path);
  } else atomicWrite(path, previousBytes);
}

export function preparePromotion({
  candidatePath,
  reportPath,
  projectRoot = PROJECT_ROOT,
  replaceExistingLock = false,
}) {
  const workflowPath = join(projectRoot, CHECK_WORKFLOW_PATH);
  const lockPath = join(projectRoot, LOCK_PATH);
  for (const path of [
    workflowPath,
    join(projectRoot, 'tools/contracts/toolchain-inputs-v1.json'),
  ]) {
    if (!existsSync(path)) fail(`${projectRoot} is not a PR-00 project root: missing ${path}`);
  }

  const candidateBytes = readFileSync(candidatePath);
  const candidate = JSON.parse(candidateBytes.toString('utf8'));
  assertLockImage(candidate);
  runGeneratorCheck(candidateBytes, reportPath, candidate);

  const previousLockBytes = existsSync(lockPath) ? readFileSync(lockPath) : null;
  const previousLock = previousLockBytes === null
    ? null
    : JSON.parse(previousLockBytes.toString('utf8'));
  const sameLock = previousLock !== null &&
    JSON.stringify(previousLock) === JSON.stringify(candidate);
  if (previousLock !== null && !sameLock && !replaceExistingLock) {
    fail('a different toolchain lock already exists; pass --replace-existing-lock explicitly');
  }
  if (previousLock === null && replaceExistingLock) {
    fail('--replace-existing-lock was requested but no promoted lock exists');
  }

  const workflowBefore = readFileSync(workflowPath, 'utf8');
  const workflowAfter = renderCheckWorkflow(workflowBefore, candidate, {
    previousLock: previousLock !== null && !sameLock ? previousLock : null,
  });
  validateToolchainLock(candidate, { projectRoot, checkWorkflowSource: workflowAfter });

  const lockChanged = previousLockBytes === null ||
    !previousLockBytes.equals(candidateBytes);
  const workflowChanged = workflowBefore !== workflowAfter;
  const summary = {
    schemaVersion: 1,
    image: candidate.image,
    buildRecipeCommit: candidate.buildRecipe.commit,
    lockSha256: candidate.lockSha256,
    validation: {
      reportReproducesCandidate: true,
      candidateMatchesContracts: true,
      renderedWorkflowMatchesCandidate: true,
    },
    changes: {
      toolchainLock: {
        path: LOCK_PATH,
        exists: previousLockBytes !== null,
        changed: lockChanged,
        beforeSha256: previousLockBytes === null ? null : sha256(previousLockBytes),
        afterSha256: sha256(candidateBytes),
      },
      checkWorkflow: {
        path: CHECK_WORKFLOW_PATH,
        changed: workflowChanged,
        beforeSha256: sha256(workflowBefore),
        afterSha256: sha256(workflowAfter),
      },
    },
  };
  return {
    candidate,
    candidateBytes,
    lockChanged,
    lockPath,
    previousLockBytes,
    projectRoot,
    summary,
    workflowAfter,
    workflowBefore,
    workflowChanged,
    workflowPath,
  };
}

export function applyPromotion(prepared) {
  let workflowWritten = false;
  let lockWritten = false;
  try {
    if (prepared.workflowChanged) {
      atomicWrite(prepared.workflowPath, prepared.workflowAfter);
      workflowWritten = true;
    }
    if (prepared.lockChanged) {
      atomicWrite(prepared.lockPath, prepared.candidateBytes);
      lockWritten = true;
    }
    const writtenLock = JSON.parse(readFileSync(prepared.lockPath, 'utf8'));
    const writtenWorkflow = readFileSync(prepared.workflowPath, 'utf8');
    validateToolchainLock(writtenLock, {
      projectRoot: prepared.projectRoot,
      checkWorkflowSource: writtenWorkflow,
    });
  } catch (error) {
    const rollbackErrors = [];
    if (lockWritten) {
      try {
        restore(prepared.lockPath, prepared.previousLockBytes);
      } catch (rollbackError) {
        rollbackErrors.push(`lock rollback failed: ${rollbackError.message}`);
      }
    }
    if (workflowWritten) {
      try {
        atomicWrite(prepared.workflowPath, prepared.workflowBefore);
      } catch (rollbackError) {
        rollbackErrors.push(`workflow rollback failed: ${rollbackError.message}`);
      }
    }
    const detail = rollbackErrors.length === 0 ? '' : `; ${rollbackErrors.join('; ')}`;
    fail(`${error.message}${detail}`);
  }
}

function main(argv) {
  const arguments_ = parseArguments(argv);
  const prepared = preparePromotion({
    candidatePath: arguments_.candidate,
    reportPath: arguments_.report,
    projectRoot: arguments_.projectRoot,
    replaceExistingLock: arguments_.replaceExistingLock,
  });
  if (arguments_.promote) applyPromotion(prepared);
  process.stdout.write(`${JSON.stringify({
    ...prepared.summary,
    mode: arguments_.promote ? 'promote' : 'dry-run',
    promoted: arguments_.promote,
  }, null, 2)}\n`);
}

const isMain = process.argv[1] !== undefined &&
  pathToFileURL(resolve(process.argv[1])).href === import.meta.url;
if (isMain) {
  try {
    main(process.argv.slice(2));
  } catch (error) {
    process.stderr.write(`promote_toolchain_lock: ${error.message}\n`);
    process.exitCode = 1;
  }
}
