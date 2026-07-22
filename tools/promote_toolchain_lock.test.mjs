// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import {
  cpSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';

import { validateToolchainLock } from './check_pr00_contracts.mjs';
import { renderCheckWorkflow } from './why3_oracle/promote_toolchain_lock.mjs';
import {
  generateCandidate,
  loadToolchainInputs,
  PROJECT_ROOT,
  reportFixture,
} from './toolchain_lock_test_helpers.mjs';

const PROMOTER = join(PROJECT_ROOT, 'tools', 'run.mjs');
const CANDIDATE_DIGEST = `sha256:${'a'.repeat(64)}`;
const CANDIDATE_REFERENCE =
  `ghcr.io/moonbit-community/why3.mbt-why3@${CANDIDATE_DIGEST}`;

function lockImage() {
  return {
    image: {
      repository: 'ghcr.io/moonbit-community/why3.mbt-why3',
      digest: CANDIDATE_DIGEST,
      reference: CANDIDATE_REFERENCE,
    },
  };
}

function lockImageWithDigest(character) {
  const digest = `sha256:${character.repeat(64)}`;
  return {
    image: {
      repository: 'ghcr.io/moonbit-community/why3.mbt-why3',
      digest,
      reference: `ghcr.io/moonbit-community/why3.mbt-why3@${digest}`,
    },
  };
}

function candidateWorkflowFixture() {
  return `name: check

jobs:
  oracle-build:
    name: fixed oracle candidate
    runs-on: ubuntu-24.04
    container:
      image: ghcr.io/\${{ github.repository }}-why3:1.7.2-z3-4.8.12
    steps:
      - name: Verify candidate image contents
        run: node tools/why3_oracle/inspect_toolchain.mjs

      - name: Check PR-00 contracts and inventories
        run: |
          node tools/check_pr00_contracts.mjs \\
            --why3-archive "$WHY3_REFERENCE_ARCHIVE"

      - name: Check all targets
        run: moon check --target all --warn-list +73
`;
}

function consolidatedCandidateWorkflowFixture() {
  return `name: check

jobs:
  oracle-build:
    name: fixed oracle candidate
    runs-on: ubuntu-24.04
    container:
      image: ghcr.io/\${{ github.repository }}-why3:1.7.2-z3-4.8.12
    steps:
      - name: Verify candidate image contents
        run: node tools/run.mjs toolchain inspect

      - name: Check the candidate oracle
        run: |
          node tools/run.mjs contracts \\
            --why3-archive "$WHY3_REFERENCE_ARCHIVE"

      - name: Check the project
        run: node tools/run.mjs project
`;
}

function runPromoter(candidatePath, reportPath, projectRoot, ...extra) {
  return spawnSync(process.execPath, [
    PROMOTER,
    'toolchain',
    'promote-lock',
    '--candidate',
    candidatePath,
    '--report',
    reportPath,
    '--project-root',
    projectRoot,
    ...extra,
  ], { cwd: PROJECT_ROOT, encoding: 'utf8', shell: false });
}

test('promotion renderer replaces every moving-oracle policy atom and is idempotent', () => {
  const rendered = renderCheckWorkflow(candidateWorkflowFixture(), lockImage());
  assert.match(rendered, new RegExp(`image: ${CANDIDATE_REFERENCE}`, 'u'));
  assert.match(rendered, new RegExp(`WHY3_ORACLE_IMAGE_DIGEST: ${CANDIDATE_DIGEST}`, 'u'));
  assert.match(rendered, /--require-toolchain-lock/u);
  assert.match(rendered, /tools\/why3_oracle\/run-fixed mvp\.abs --/u);
  assert.doesNotMatch(rendered, /fixed oracle candidate/u);
  assert.doesNotMatch(rendered, /github\.repository.*why3:1\.7\.2/u);
  assert.equal(renderCheckWorkflow(rendered, lockImage()), rendered);
});

test('promotion renderer fails closed on an unexpected workflow shape', () => {
  const changed = candidateWorkflowFixture().replace(
    'name: fixed oracle candidate',
    'name: oracle draft',
  );
  assert.throws(
    () => renderCheckWorkflow(changed, lockImage()),
    /expected exactly one candidate job name/u,
  );
});

test('promotion renderer upgrades the consolidated candidate task', () => {
  const rendered = renderCheckWorkflow(consolidatedCandidateWorkflowFixture(), lockImage());
  assert.match(rendered, /node tools\/run\.mjs oracle/u);
  assert.match(rendered, /--require-toolchain-lock/u);
  assert.doesNotMatch(rendered, /node tools\/run\.mjs contracts/u);
  assert.doesNotMatch(rendered, /tools\/why3_oracle\/run-fixed/u);
});

test('promotion renderer requires the previous lock when replacing a digest', () => {
  const previousLock = lockImageWithDigest('b');
  const nextLock = lockImageWithDigest('c');
  const previousWorkflow = renderCheckWorkflow(candidateWorkflowFixture(), previousLock);
  assert.throws(
    () => renderCheckWorkflow(previousWorkflow, nextLock),
    /neither the exact candidate form nor the candidate lock form/u,
  );
  const nextWorkflow = renderCheckWorkflow(previousWorkflow, nextLock, { previousLock });
  assert.match(nextWorkflow, new RegExp(nextLock.image.digest, 'u'));
  assert.doesNotMatch(nextWorkflow, new RegExp(previousLock.image.digest, 'u'));
});

test('promotion renderer preserves the consolidated CI task entrypoint', () => {
  const currentLock = JSON.parse(readFileSync(
    join(PROJECT_ROOT, 'tools', 'contracts', 'toolchain-lock.json'),
    'utf8',
  ));
  const currentWorkflow = readFileSync(
    join(PROJECT_ROOT, '.github', 'workflows', 'check.yml'),
    'utf8',
  );
  const nextLock = lockImageWithDigest('c');
  const rendered = renderCheckWorkflow(currentWorkflow, nextLock, {
    previousLock: currentLock,
  });
  assert.match(rendered, /node tools\/run\.mjs oracle/u);
  assert.match(rendered, new RegExp(nextLock.image.digest, 'u'));
  assert.doesNotMatch(rendered, new RegExp(currentLock.image.digest, 'u'));
});

test('promotion CLI dry-runs without writes, then promotes and revalidates atomically', () => {
  const directory = mkdtempSync(join(tmpdir(), 'why3-toolchain-promote-test-'));
  try {
    const projectRoot = join(directory, 'project');
    const artifactRoot = join(directory, 'artifact');
    mkdirSync(join(projectRoot, '.github', 'workflows'), { recursive: true });
    mkdirSync(join(projectRoot, 'tools'), { recursive: true });
    mkdirSync(join(projectRoot, 'prover', 'z3'), { recursive: true });
    mkdirSync(artifactRoot, { recursive: true });
    cpSync(
      join(PROJECT_ROOT, 'tools', 'contracts'),
      join(projectRoot, 'tools', 'contracts'),
      { recursive: true },
    );
    mkdirSync(join(projectRoot, 'tools', 'why3_oracle', 'goldens'), {
      recursive: true,
    });
    cpSync(
      join(PROJECT_ROOT, 'tools', 'why3_oracle', 'goldens', 'pr-v1'),
      join(projectRoot, 'tools', 'why3_oracle', 'goldens', 'pr-v1'),
      { recursive: true },
    );
    cpSync(
      join(PROJECT_ROOT, 'prover', 'z3', 'z3-static-profile-v1.json'),
      join(projectRoot, 'prover', 'z3', 'z3-static-profile-v1.json'),
    );
    const lockPath = join(projectRoot, 'tools', 'contracts', 'toolchain-lock.json');
    rmSync(lockPath, { force: true });
    const workflowPath = join(projectRoot, '.github', 'workflows', 'check.yml');
    const workflowBefore = candidateWorkflowFixture();
    writeFileSync(workflowPath, workflowBefore);

    const { inputBytes, inputs } = loadToolchainInputs();
    const generated = generateCandidate(
      reportFixture(inputs, inputBytes),
      artifactRoot,
    );
    assert.equal(generated.result.status, 0, generated.result.stderr);

    const alteredCandidatePath = join(artifactRoot, 'altered-toolchain-lock.json');
    writeFileSync(
      alteredCandidatePath,
      `${readFileSync(generated.candidatePath, 'utf8')}\n`,
    );
    const altered = runPromoter(
      alteredCandidatePath,
      generated.reportPath,
      projectRoot,
    );
    assert.notEqual(altered.status, 0);
    assert.match(altered.stderr, /candidate bytes do not match/u);
    assert.equal(existsSync(lockPath), false);
    assert.equal(readFileSync(workflowPath, 'utf8'), workflowBefore);

    const dryRun = runPromoter(
      generated.candidatePath,
      generated.reportPath,
      projectRoot,
    );
    assert.equal(dryRun.status, 0, dryRun.stderr);
    const preview = JSON.parse(dryRun.stdout);
    assert.equal(preview.mode, 'dry-run');
    assert.equal(preview.promoted, false);
    assert.equal(preview.changes.toolchainLock.changed, true);
    assert.equal(preview.changes.checkWorkflow.changed, true);
    assert.equal(existsSync(lockPath), false);
    assert.equal(readFileSync(workflowPath, 'utf8'), workflowBefore);

    const promotion = runPromoter(
      generated.candidatePath,
      generated.reportPath,
      projectRoot,
      '--promote',
    );
    assert.equal(promotion.status, 0, promotion.stderr);
    const promoted = JSON.parse(promotion.stdout);
    assert.equal(promoted.mode, 'promote');
    assert.equal(promoted.promoted, true);
    assert.equal(
      readFileSync(lockPath, 'utf8'),
      readFileSync(generated.candidatePath, 'utf8'),
    );
    const lock = JSON.parse(readFileSync(lockPath, 'utf8'));
    const workflow = readFileSync(workflowPath, 'utf8');
    validateToolchainLock(lock, { projectRoot, checkWorkflowSource: workflow });

    const repeated = runPromoter(
      generated.candidatePath,
      generated.reportPath,
      projectRoot,
      '--promote',
    );
    assert.equal(repeated.status, 0, repeated.stderr);
    const idempotent = JSON.parse(repeated.stdout);
    assert.equal(idempotent.changes.toolchainLock.changed, false);
    assert.equal(idempotent.changes.checkWorkflow.changed, false);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});
