// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

'use strict';

const { createHash } = require('node:crypto');
const { spawnSync } = require('node:child_process');
const { readFileSync, statSync } = require('node:fs');
const { dirname, isAbsolute, join, resolve } = require('node:path');

const PROJECT_ROOT = resolve(__dirname, '..', '..');
const ENVIRONMENT_LOCK_PATH = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'reference-environment-lock-v1.json',
);
const DIGEST_PATTERN = /^sha256:[0-9a-f]{64}$/u;
const SHA256_PATTERN = /^[0-9a-f]{64}$/u;
const COMMIT_PATTERN = /^[0-9a-f]{40}$/u;

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function assert(condition, message) {
  if (!condition) fail(message);
}

function assertEqual(actual, expected, message) {
  if (JSON.stringify(actual) !== JSON.stringify(expected)) {
    fail(`${message}: expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
  }
}

function assertExactKeys(value, expected, label) {
  assert(
    value !== null && typeof value === 'object' && !Array.isArray(value),
    `${label} must be an object`,
  );
  const actual = Object.keys(value).sort();
  const wanted = [...expected].sort();
  assertEqual(actual, wanted, `${label} keys`);
}

function assertAbsolutePath(path, label) {
  assert(typeof path === 'string' && isAbsolute(path), `${label} must be an absolute path`);
}

function expectedManifest(lock) {
  const switchBin = dirname(lock.why3.runtime.executable);
  return {
    schemaVersion: 1,
    ocaml: {
      version: lock.ocaml.version,
      runtime: {
        compiler: join(switchBin, 'ocamlc'),
        findlib: join(switchBin, 'ocamlfind'),
      },
    },
    why3: {
      version: lock.why3.version,
      commit: lock.why3.commit,
      tree: lock.why3.tree,
      archive: {
        path: lock.why3.archive.path,
        sha256: lock.why3.archive.sha256,
      },
      runtime: lock.why3.runtime,
    },
    z3: {
      version: lock.z3.version,
      runtime: lock.z3.runtime,
    },
  };
}

function renderExpectedManifest(lock) {
  return `${JSON.stringify(expectedManifest(lock), null, 2)}\n`;
}

function validateEnvironmentLock(lock) {
  assertExactKeys(
    lock,
    ['schemaVersion', 'platform', 'image', 'ocaml', 'why3', 'z3', 'manifest'],
    'reference environment lock',
  );
  assertEqual(lock.schemaVersion, 1, 'reference environment lock schema version');

  assertExactKeys(lock.platform, ['os', 'architecture', 'oci'], 'platform');
  assertEqual(lock.platform, {
    os: 'linux',
    architecture: 'amd64',
    oci: 'linux/amd64',
  }, 'reference platform');

  assertExactKeys(lock.image, ['repository', 'digest'], 'image');
  assertEqual(
    lock.image.repository,
    'ghcr.io/moonbit-community/why3.mbt-why3',
    'reference image repository',
  );
  assert(DIGEST_PATTERN.test(lock.image.digest), 'reference image digest is invalid');

  assertExactKeys(lock.ocaml, ['base', 'version'], 'OCaml');
  assertExactKeys(lock.ocaml.base, ['repository', 'tag', 'digest'], 'OCaml base');
  assertEqual(lock.ocaml.base.repository, 'ocaml/opam', 'OCaml base repository');
  assertEqual(lock.ocaml.base.tag, 'ubuntu-24.04-ocaml-4.14', 'OCaml base tag');
  assert(DIGEST_PATTERN.test(lock.ocaml.base.digest), 'OCaml base digest is invalid');
  assert(/^4\.14\.[0-9]+$/u.test(lock.ocaml.version), 'OCaml version is invalid');

  assertExactKeys(
    lock.why3,
    ['version', 'commit', 'tree', 'archive', 'runtime'],
    'Why3',
  );
  assertEqual(lock.why3.version, '1.7.2', 'Why3 version');
  assert(COMMIT_PATTERN.test(lock.why3.commit), 'Why3 commit is invalid');
  assert(COMMIT_PATTERN.test(lock.why3.tree), 'Why3 tree is invalid');
  assertExactKeys(lock.why3.archive, ['url', 'sha256', 'path'], 'Why3 archive');
  assert(/^https:\/\//u.test(lock.why3.archive.url), 'Why3 archive URL is invalid');
  assert(SHA256_PATTERN.test(lock.why3.archive.sha256), 'Why3 archive hash is invalid');
  assertAbsolutePath(lock.why3.archive.path, 'Why3 archive path');
  assertEqual(
    lock.why3.archive.path,
    '/opt/reference-env/why3-source.tar.gz',
    'Why3 archive path',
  );
  assertExactKeys(lock.why3.runtime, ['executable', 'datadir'], 'Why3 runtime');
  assertAbsolutePath(lock.why3.runtime.executable, 'Why3 executable');
  assertAbsolutePath(lock.why3.runtime.datadir, 'Why3 datadir');
  assertEqual(
    lock.why3.runtime,
    {
      executable: '/home/opam/.opam/4.14/bin/why3',
      datadir: '/home/opam/.opam/4.14/share/why3',
    },
    'Why3 runtime paths',
  );

  assertExactKeys(lock.z3, ['version', 'runtime'], 'Z3');
  assertEqual(lock.z3.version, '4.8.12', 'Z3 version');
  assertExactKeys(lock.z3.runtime, ['executable'], 'Z3 runtime');
  assertAbsolutePath(lock.z3.runtime.executable, 'Z3 executable');
  assertEqual(lock.z3.runtime.executable, '/opt/z3/bin/z3', 'Z3 executable');

  assertExactKeys(lock.manifest, ['path', 'sha256'], 'embedded manifest');
  assertAbsolutePath(lock.manifest.path, 'embedded manifest path');
  assertEqual(
    lock.manifest.path,
    '/opt/reference-env/manifest.json',
    'embedded manifest path',
  );
  assert(SHA256_PATTERN.test(lock.manifest.sha256), 'embedded manifest hash is invalid');
  assertEqual(
    lock.manifest.sha256,
    sha256(renderExpectedManifest(lock)),
    'embedded manifest expected hash',
  );
  return lock;
}

function validateManifest(manifest, lock) {
  assertExactKeys(manifest, ['schemaVersion', 'ocaml', 'why3', 'z3'], 'embedded manifest');
  assertExactKeys(manifest.ocaml, ['version', 'runtime'], 'manifest OCaml');
  assertExactKeys(manifest.ocaml.runtime, ['compiler', 'findlib'], 'manifest OCaml runtime');
  assertExactKeys(
    manifest.why3,
    ['version', 'commit', 'tree', 'archive', 'runtime'],
    'manifest Why3',
  );
  assertExactKeys(manifest.why3.archive, ['path', 'sha256'], 'manifest Why3 archive');
  assertExactKeys(manifest.why3.runtime, ['executable', 'datadir'], 'manifest Why3 runtime');
  assertExactKeys(manifest.z3, ['version', 'runtime'], 'manifest Z3');
  assertExactKeys(manifest.z3.runtime, ['executable'], 'manifest Z3 runtime');
  assertEqual(manifest, expectedManifest(lock), 'embedded manifest content');
  return manifest;
}

function readEnvironmentLock(path = ENVIRONMENT_LOCK_PATH) {
  return validateEnvironmentLock(JSON.parse(readFileSync(path, 'utf8')));
}

function checkedOutput(command, argv) {
  const result = spawnSync(command, argv, {
    encoding: 'utf8',
    env: { ...process.env, LC_ALL: 'C', LANG: 'C' },
    shell: false,
  });
  if (result.error || result.signal !== null || result.status !== 0) {
    const detail = `${result.stdout ?? ''}${result.stderr ?? ''}${result.error?.message ?? ''}`.trim();
    fail(`${command} ${argv.join(' ')} failed: ${detail}`);
  }
  return result.stdout.trim();
}

function verifyReferenceEnvironment(
  lock,
  { manifestPath = lock.manifest.path, run = checkedOutput } = {},
) {
  validateEnvironmentLock(lock);
  const manifestBytes = readFileSync(manifestPath);
  const actualManifestSha256 = sha256(manifestBytes);
  assertEqual(actualManifestSha256, lock.manifest.sha256, 'embedded manifest file hash');
  const manifest = validateManifest(JSON.parse(manifestBytes), lock);

  assert(statSync(lock.why3.archive.path).isFile(), 'Why3 source archive is not a file');
  assertEqual(
    sha256(readFileSync(lock.why3.archive.path)),
    lock.why3.archive.sha256,
    'Why3 source archive file hash',
  );
  assertEqual(
    run(manifest.ocaml.runtime.compiler, ['-version']),
    lock.ocaml.version,
    'OCaml runtime version',
  );
  assertEqual(
    run(manifest.ocaml.runtime.findlib, ['query', '-format', '%v', 'why3']),
    lock.why3.version,
    'OCaml Why3 package version',
  );
  assertEqual(
    run(lock.why3.runtime.executable, ['--version']),
    `Why3 platform, version ${lock.why3.version}`,
    'Why3 runtime version',
  );
  assertEqual(
    run(lock.why3.runtime.executable, ['--print-datadir']),
    lock.why3.runtime.datadir,
    'Why3 runtime datadir',
  );
  assertEqual(
    run(lock.z3.runtime.executable, ['--version']),
    `Z3 version ${lock.z3.version} - 64 bit`,
    'Z3 runtime version',
  );
  return { manifest, manifestSha256: actualManifestSha256 };
}

module.exports = {
  ENVIRONMENT_LOCK_PATH,
  expectedManifest,
  fail,
  readEnvironmentLock,
  renderExpectedManifest,
  sha256,
  validateEnvironmentLock,
  validateManifest,
  verifyReferenceEnvironment,
};
