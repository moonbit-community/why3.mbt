// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..');
const SHA256_PATTERN = /^[0-9a-f]{64}$/u;
const COMMIT_PATTERN = /^[0-9a-f]{40}$/u;
const WHY3_OPAM_RECIPE_PATH = 'tools/why3_oracle/why3-1.7.2.opam';
const WHY3_OPAM_RECIPE_SHA256 = '24d4eae07494af13d313fd9ebb82e15d565c45d250dc04d5d029a06cf0534081';
const WHY3_OPAM_RECIPE_BLOB = '6811b48fa50e6160ed7f812696e0939a1c40bd0d';

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function gitBlobSha(bytes) {
  return createHash('sha1')
    .update(`blob ${bytes.length}\0`)
    .update(bytes)
    .digest('hex');
}

function canonicalSha(value) {
  return sha256(`${JSON.stringify(value)}\n`);
}

function compareUtf8(left, right) {
  return Buffer.compare(Buffer.from(left, 'utf8'), Buffer.from(right, 'utf8'));
}

function parseArguments(argv) {
  if (argv.length === 0) return { mode: 'stdout', path: null };
  if (argv.length !== 2 || !['--output', '--check'].includes(argv[0])) {
    fail('usage: generate_toolchain_inputs.mjs [--output PATH | --check PATH]');
  }
  return { mode: argv[0].slice(2), path: resolve(argv[1]) };
}

function readJson(path) {
  return JSON.parse(readFileSync(join(PROJECT_ROOT, path), 'utf8'));
}

function githubActions() {
  const directory = join(PROJECT_ROOT, '.github', 'workflows');
  const actions = [];
  for (const name of readdirSync(directory).sort(compareUtf8)) {
    if (!name.endsWith('.yml') && !name.endsWith('.yaml')) continue;
    const workflow = `.github/workflows/${name}`;
    const source = readFileSync(join(directory, name), 'utf8');
    for (const match of source.matchAll(/^\s*-?\s*uses:\s*([^\s@]+)@([^\s#]+)\s*$/gmu)) {
      if (!COMMIT_PATTERN.test(match[2])) {
        fail(`${workflow} uses non-commit action reference ${match[0].trim()}`);
      }
      actions.push({ workflow, action: match[1], commit: match[2] });
    }
  }
  actions.sort((left, right) =>
    compareUtf8(`${left.workflow}\0${left.action}`, `${right.workflow}\0${right.action}`));
  return actions;
}

function baseImage(dockerfile) {
  const match = dockerfile.match(
    /^FROM\s+([^\s@]+):([^\s@]+)@sha256:([0-9a-f]{64})\s*$/mu,
  );
  if (!match) fail('Dockerfile must pin its base image by a 64-hex SHA-256 digest');
  return {
    repository: match[1],
    tagAtResolution: match[2],
    platform: 'linux/amd64',
    digest: `sha256:${match[3]}`,
  };
}

function dockerfileFrontend(dockerfile) {
  const match = dockerfile.match(
    /^#\s*syntax=([^\s@]+):([^\s@]+)@sha256:([0-9a-f]{64})\s*$/mu,
  );
  if (!match) fail('Dockerfile must pin its frontend image by a 64-hex SHA-256 digest');
  return {
    repository: match[1],
    tagAtResolution: match[2],
    digest: `sha256:${match[3]}`,
  };
}

function buildInputs() {
  const dockerfile = readFileSync(join(PROJECT_ROOT, 'Dockerfile'));
  const dockerfileSource = dockerfile.toString('utf8');
  const driverPath = 'tools/contracts/driver-closure-v1.json';
  const driver = readJson(driverPath);
  const why3OpamRecipe = readFileSync(join(PROJECT_ROOT, WHY3_OPAM_RECIPE_PATH));
  if (sha256(why3OpamRecipe) !== WHY3_OPAM_RECIPE_SHA256 ||
      gitBlobSha(why3OpamRecipe) !== WHY3_OPAM_RECIPE_BLOB) {
    fail('vendored Why3 opam recipe differs from the pinned upstream blob');
  }
  const dockerignore = readFileSync(join(PROJECT_ROOT, '.dockerignore'), 'utf8').split(/\r?\n/u);
  if (!dockerignore.includes(`!${WHY3_OPAM_RECIPE_PATH}`)) {
    fail('Docker build context does not include the vendored Why3 opam recipe');
  }
  if (!dockerfileSource.includes(
    `COPY ${WHY3_OPAM_RECIPE_PATH} /opt/why3-reference/source/why3.opam`,
  ) || !dockerfileSource.includes(WHY3_OPAM_RECIPE_SHA256) ||
      !dockerfileSource.includes('sha256sum --check --strict') ||
      !dockerfileSource.includes('--kind=path')) {
    fail('Dockerfile does not install and verify the pinned Why3 opam recipe');
  }
  if (/\bMOON_(?:VERSION|ARCHIVE_SHA256)\b|\/opt\/moonbit|cli\.moonbitlang\.com/u.test(
    dockerfileSource,
  )) {
    fail('Dockerfile must not install or pin the CI-managed MoonBit toolchain');
  }
  const value = {
    schemaVersion: 1,
    oraclePlatform: { os: 'linux', architecture: 'amd64', oci: 'linux/amd64' },
    baseImage: baseImage(dockerfileSource),
    buildRecipe: {
      path: 'Dockerfile',
      sha256: sha256(dockerfile),
      frontendImage: dockerfileFrontend(dockerfileSource),
      sourceArchiveKeptInImage: '/opt/why3-reference/why3-source.tar.gz',
    },
    githubActions: githubActions(),
    why3: {
      version: '1.7.2',
      commit: driver.why3.commit,
      gitTree: driver.why3.tree,
      shapeVersion: driver.why3.shapeVersion,
      referenceArchive: driver.why3.sourceArchive,
      opamRecipe: {
        path: WHY3_OPAM_RECIPE_PATH,
        sha256: WHY3_OPAM_RECIPE_SHA256,
        upstream: {
          repository: 'ocaml/opam-repository',
          commit: 'bfeb42d61bb49c607b888d38dadd2cc4c9d98358',
          path: 'packages/why3/why3.1.7.2/opam',
          gitBlob: WHY3_OPAM_RECIPE_BLOB,
        },
      },
      executablePath: '/home/opam/.opam/4.14/bin/why3',
      datadirPath: '/home/opam/.opam/4.14/share/why3',
      driverManifest: driverPath,
      driverManifestSha256: sha256(readFileSync(join(PROJECT_ROOT, driverPath))),
      driverClosureSha256: driver.driver.sha256,
      semanticSnapshotSha256: driver.semanticSnapshot.sha256,
      stdlibTreeSha256: driver.semanticSnapshot.stdlibTree.sha256,
      proverDetectionSha256: driver.proverDetection.sha256,
    },
    z3: {
      version: '4.8.12',
      commit: '3a402ca2c14c3891d24658318406f80ce59b719f',
      archive: {
        url: 'https://github.com/Z3Prover/z3/releases/download/z3-4.8.12/z3-4.8.12-x64-glibc-2.31.zip',
        sha256: '648e8a7afb57445440ad711b733bd675e3888da2767c14ae5122582c924d8d52',
      },
      executable: {
        path: '/opt/z3/bin/z3',
        sha256: '350bb28360df8694db72068a26fcb779797889599f584ed3146b899a98204824',
      },
    },
    environment: {
      LC_ALL: 'C',
      LANG: 'C',
      TZ: 'UTC',
      HOME: 'isolated Whyconf directory',
      TMPDIR: 'isolated Whyconf directory',
      defaultPlugins: 'disabled',
      standardLibrary: 'explicit --no-stdlib plus manifest loadpaths',
    },
  };
  for (const action of value.githubActions) {
    if (!COMMIT_PATTERN.test(action.commit)) fail(`invalid action commit ${action.commit}`);
  }
  for (const executable of [value.z3.executable]) {
    if (!SHA256_PATTERN.test(executable.sha256)) fail(`invalid executable hash for ${executable.path}`);
  }
  return { ...value, toolchainInputsSha256: canonicalSha(value) };
}

try {
  const arguments_ = parseArguments(process.argv.slice(2));
  const rendered = `${JSON.stringify(buildInputs(), null, 2)}\n`;
  if (arguments_.mode === 'output') {
    writeFileSync(arguments_.path, rendered);
  } else if (arguments_.mode === 'check') {
    if (readFileSync(arguments_.path, 'utf8') !== rendered) {
      fail(`${arguments_.path} does not match generated toolchain inputs`);
    }
  } else {
    process.stdout.write(rendered);
  }
} catch (error) {
  process.stderr.write(`generate_toolchain_inputs: ${error.message}\n`);
  process.exitCode = 1;
}
