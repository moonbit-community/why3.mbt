// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

export const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
export const GENERATOR = join(PROJECT_ROOT, 'tools', 'why3_oracle', 'generate_toolchain_lock.mjs');
export const INPUTS_PATH = join(PROJECT_ROOT, 'tools', 'contracts', 'toolchain-inputs-v1.json');

export function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

export function loadToolchainInputs() {
  const inputBytes = readFileSync(INPUTS_PATH);
  return { inputBytes, inputs: JSON.parse(inputBytes.toString('utf8')) };
}

export function reportFixture(inputs, inputBytes) {
  return {
    schemaVersion: 1,
    platform: inputs.oraclePlatform,
    toolchainInputs: {
      path: 'tools/contracts/toolchain-inputs-v1.json',
      fileSha256: sha256(inputBytes),
      contentSha256: inputs.toolchainInputsSha256,
    },
    why3: {
      version: inputs.why3.version,
      versionOutput: `Why3 platform, version ${inputs.why3.version}`,
      commit: inputs.why3.commit,
      shapeVersion: inputs.why3.shapeVersion,
      executable: {
        path: inputs.why3.executablePath,
        sha256: sha256('why3 executable fixture'),
      },
      datadir: {
        path: inputs.why3.datadirPath,
        treeSha256: sha256('Why3 datadir fixture'),
        stdlibTreeSha256: inputs.why3.stdlibTreeSha256,
      },
      driverClosureSha256: inputs.why3.driverClosureSha256,
      proverDetectionSha256: inputs.why3.proverDetectionSha256,
      sourceArchiveSha256: inputs.why3.referenceArchive.sha256,
    },
    z3: {
      version: inputs.z3.version,
      versionOutput: `Z3 version ${inputs.z3.version} - 64 bit`,
      executable: inputs.z3.executable,
    },
    environment: { LC_ALL: 'C', LANG: 'C', TZ: 'UTC' },
  };
}

export function generateCandidate(
  report,
  directory,
  { imageDigest = `sha256:${'a'.repeat(64)}`, buildCommit = 'b'.repeat(40) } = {},
) {
  const reportPath = join(directory, 'toolchain-report.json');
  const candidatePath = join(directory, 'toolchain-lock.json');
  writeFileSync(reportPath, `${JSON.stringify(report, null, 2)}\n`);
  const result = spawnSync(process.execPath, [
    GENERATOR,
    '--report',
    reportPath,
    '--image-digest',
    imageDigest,
    '--build-recipe-commit',
    buildCommit,
    '--output',
    candidatePath,
  ], { cwd: PROJECT_ROOT, encoding: 'utf8', shell: false });
  return { candidatePath, reportPath, result };
}
