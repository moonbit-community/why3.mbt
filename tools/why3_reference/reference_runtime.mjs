// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash, randomBytes } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import {
  existsSync,
  mkdirSync,
  readFileSync,
  realpathSync,
  renameSync,
  rmSync,
  statSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { cpus } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import referenceEnvironment from './reference_environment.cjs';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const PATCH_PATH = join(SCRIPT_DIRECTORY, 'patches', 'driver-trace.patch');
const DEPENDENCIES_PATH = join(
  SCRIPT_DIRECTORY,
  'runtime-dependencies-v1.json',
);
const BUILD_TARGETS = ['lib/why3/why3.cmxa', 'lib/why3/why3.cma'];
const CONFIGURE_ARGUMENTS = [
  '--disable-frama-c',
  '--disable-coq-libs',
  '--disable-js-of-ocaml',
  '--disable-re',
  '--enable-ocamlfind',
  '--disable-zarith',
  '--disable-mpfr',
  '--disable-zip',
  '--disable-hypothesis-selection',
  '--disable-stackify',
  '--disable-ide',
];
const COMPLETE_MARKER = '.complete.json';
let dependenciesReady = false;

const { readEnvironmentLock } = referenceEnvironment;

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function canonicalSha(value) {
  return sha256(`${JSON.stringify(value)}\n`);
}

function runChecked(command, argv, options = {}) {
  const result = spawnSync(command, argv, {
    cwd: options.cwd ?? PROJECT_ROOT,
    encoding: 'utf8',
    env: options.env ?? { ...process.env, LC_ALL: 'C', LANG: 'C' },
    maxBuffer: options.maxBuffer ?? 128 * 1024 * 1024,
    shell: false,
  });
  if (result.signal !== null || result.status !== 0 ||
      (result.error && result.error.code !== 'EPERM')) {
    const detail = `${result.stdout ?? ''}${result.stderr ?? ''}${result.error?.message ?? ''}`.trim();
    fail(`${command} ${argv.join(' ')} failed: ${detail}`);
  }
  return result.stdout ?? '';
}

function assertExactKeys(value, expected, label) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    fail(`${label} must be an object`);
  }
  const actual = Object.keys(value).sort();
  const wanted = [...expected].sort();
  if (JSON.stringify(actual) !== JSON.stringify(wanted)) {
    fail(`${label} keys must be exactly ${wanted.join(', ')}`);
  }
}

export function readRuntimeDependencies(path = DEPENDENCIES_PATH) {
  const manifest = JSON.parse(readFileSync(path, 'utf8'));
  assertExactKeys(manifest, ['schemaVersion', 'packages'], 'runtime dependency manifest');
  if (manifest.schemaVersion !== 1 || !Array.isArray(manifest.packages)) {
    fail('unsupported runtime dependency manifest');
  }
  const previous = new Set();
  for (const dependency of manifest.packages) {
    assertExactKeys(dependency, ['opam', 'version', 'findlib'], 'runtime dependency');
    if (typeof dependency.opam !== 'string' || previous.has(dependency.opam) ||
        typeof dependency.version !== 'string' || dependency.version === '' ||
        !Array.isArray(dependency.findlib) || dependency.findlib.length === 0 ||
        dependency.findlib.some(name => typeof name !== 'string')) {
      fail('invalid or duplicate runtime dependency');
    }
    previous.add(dependency.opam);
  }
  return manifest;
}

function findlibPackageVersion(name) {
  const result = spawnSync('ocamlfind', ['query', '-format', '%v', name], {
    cwd: PROJECT_ROOT,
    encoding: 'utf8',
    env: { ...process.env, LC_ALL: 'C', LANG: 'C' },
    shell: false,
  });
  if (result.signal !== null || result.status !== 0 ||
      (result.error && result.error.code !== 'EPERM')) return null;
  return (result.stdout ?? '').trim();
}

function opamInvocation(argv, { uid, env }) {
  const opamRoot = env.OPAMROOT;
  const ownedHome = typeof opamRoot === 'string'
    ? /^\/home\/([^/]+)\/\.opam\/?$/u.exec(opamRoot)
    : null;
  if (uid !== 0 || ownedHome === null) return ['opam', argv];

  // The locked image builds this switch as its home-directory owner, then
  // executes the GitHub Actions job as root. Restore that identity so opam's
  // Git repositories remain trusted and newly installed files keep one owner.
  const user = ownedHome[1];
  const home = `/home/${user}`;
  return [
    'runuser',
    [
      '--user',
      user,
      '--preserve-environment',
      '--',
      'env',
      `HOME=${home}`,
      `USER=${user}`,
      `LOGNAME=${user}`,
      `OPAMROOT=${opamRoot}`,
      'opam',
      ...argv,
    ],
  ];
}

export function installRuntimeDependencies(
  dependencies,
  run = runChecked,
  execution = {},
) {
  if (dependencies.length === 0) return;
  const identity = {
    uid: execution.uid ??
      (typeof process.getuid === 'function' ? process.getuid() : null),
    env: execution.env ?? process.env,
  };
  const runOpam = argv => {
    const [command, commandArguments] = opamInvocation(argv, identity);
    run(command, commandArguments);
  };
  runOpam(['update']);
  runOpam([
    'install',
    '--yes',
    ...dependencies.map(item => `${item.opam}.${item.version}`),
  ]);
}

export function ensureRuntimeDependencies() {
  if (dependenciesReady) return;
  const manifest = readRuntimeDependencies();
  const missing = manifest.packages.filter(dependency =>
    dependency.findlib.some(name =>
      findlibPackageVersion(name) !== dependency.version));
  if (missing.length !== 0) {
    process.stderr.write(
      'reference runtime: installing adapter dependencies ' +
      `${missing.map(item => `${item.opam}.${item.version}`).join(', ')}\n`,
    );
    installRuntimeDependencies(missing);
  }
  for (const dependency of manifest.packages) {
    for (const name of dependency.findlib) {
      const version = findlibPackageVersion(name);
      if (version !== dependency.version) {
        fail(
          `OCaml adapter dependency ${name} has version ${version ?? '<missing>'}; ` +
          `expected ${dependency.version}`,
        );
      }
    }
  }
  dependenciesReady = true;
}

function normalizedSourceOptions(options = {}) {
  const why3Root = options.why3Root === null || options.why3Root === undefined
    ? null
    : resolve(options.why3Root);
  const why3Archive = options.why3Archive === null || options.why3Archive === undefined
    ? null
    : resolve(options.why3Archive);
  if (why3Root !== null && why3Archive !== null) {
    const defaultRoot = resolve(PROJECT_ROOT, '..', 'why3');
    if (why3Root !== defaultRoot) {
      fail('--why3-root and --why3-archive are mutually exclusive');
    }
    return { why3Root: null, why3Archive };
  }
  if (why3Root !== null || why3Archive !== null) return { why3Root, why3Archive };
  if (process.env.WHY3_REFERENCE_ARCHIVE) {
    return { why3Root: null, why3Archive: resolve(process.env.WHY3_REFERENCE_ARCHIVE) };
  }
  return { why3Root: resolve(PROJECT_ROOT, '..', 'why3'), why3Archive: null };
}

function verifySource(options, lock) {
  const normalized = normalizedSourceOptions(options);
  if (normalized.why3Archive !== null) {
    const archive = realpathSync(normalized.why3Archive);
    const actual = sha256(readFileSync(archive));
    if (actual !== lock.why3.archive.sha256) {
      fail(`Why3 archive hash drift: expected ${lock.why3.archive.sha256}, got ${actual}`);
    }
    return { archive, root: null };
  }
  const root = realpathSync(normalized.why3Root);
  const commit = runChecked('git', ['-C', root, 'rev-parse', 'HEAD']).trim();
  const tree = runChecked('git', ['-C', root, 'rev-parse', 'HEAD^{tree}']).trim();
  if (commit !== lock.why3.commit || tree !== lock.why3.tree) {
    fail(
      `Why3 source identity drift: expected ${lock.why3.commit}/${lock.why3.tree}, ` +
      `got ${commit}/${tree}`,
    );
  }
  return { archive: null, root };
}

export function buildRuntimeDescriptor({
  lock,
  ocamlVersion,
  patchBytes = readFileSync(PATCH_PATH),
  builderBytes = readFileSync(fileURLToPath(import.meta.url)),
} = {}) {
  if (!lock) fail('runtime descriptor requires an environment lock');
  if (typeof ocamlVersion !== 'string' || ocamlVersion === '') {
    fail('runtime descriptor requires the OCaml version');
  }
  return {
    schemaVersion: 1,
    imageDigest: lock.image.digest,
    why3: {
      version: lock.why3.version,
      commit: lock.why3.commit,
      tree: lock.why3.tree,
      archiveSha256: lock.why3.archive.sha256,
    },
    tracePatchSha256: sha256(patchBytes),
    builderSha256: sha256(builderBytes),
    configureArguments: CONFIGURE_ARGUMENTS,
    buildTargets: BUILD_TARGETS,
    ocamlVersion,
  };
}

export function runtimeCacheKey(descriptor) {
  return canonicalSha(descriptor);
}

function runtimeArtifacts(directory) {
  return [
    join(directory, 'source', 'lib', 'why3', 'why3.cmxa'),
    join(directory, 'source', 'lib', 'why3', 'why3.cma'),
    join(directory, 'source', 'lib', 'why3', 'META'),
  ];
}

function runtimeDataPaths(directory) {
  const datadir = join(directory, 'install', 'share', 'why3');
  return [
    join(datadir, 'drivers'),
    join(datadir, 'stdlib'),
    join(datadir, 'provers-detection-data.conf'),
  ];
}

export function isCompleteRuntime(directory, expectedKey) {
  const markerPath = join(directory, COMPLETE_MARKER);
  if (!existsSync(markerPath)) return false;
  try {
    const marker = JSON.parse(readFileSync(markerPath, 'utf8'));
    return marker.schemaVersion === 1 && marker.cacheKey === expectedKey &&
      runtimeArtifacts(directory).every(path => existsSync(path) && statSync(path).isFile()) &&
      runtimeDataPaths(directory).every(path => existsSync(path));
  } catch {
    return false;
  }
}

export function publishRuntimeDirectory(temporary, destination, expectedKey) {
  if (!isCompleteRuntime(temporary, expectedKey)) {
    fail(`refusing to publish incomplete reference runtime ${temporary}`);
  }
  if (existsSync(destination)) {
    if (isCompleteRuntime(destination, expectedKey)) {
      rmSync(temporary, { recursive: true, force: true });
      return false;
    }
    rmSync(destination, { recursive: true, force: true });
  }
  try {
    renameSync(temporary, destination);
    return true;
  } catch (error) {
    if (isCompleteRuntime(destination, expectedKey)) {
      rmSync(temporary, { recursive: true, force: true });
      return false;
    }
    throw error;
  }
}

function populateSource(source, destination, temporary) {
  mkdirSync(destination, { recursive: true });
  if (source.archive !== null) {
    runChecked('tar', [
      '-xzf',
      source.archive,
      '--strip-components=1',
      '-C',
      destination,
    ]);
    return;
  }
  const archive = join(temporary, 'why3-source.tar');
  runChecked('git', [
    '-C',
    source.root,
    'archive',
    '--format=tar',
    '--output',
    archive,
    'HEAD',
  ]);
  runChecked('tar', ['-xf', archive, '-C', destination]);
  rmSync(archive, { force: true });
}

function buildRuntime(temporary, destination, source, descriptor, cacheKey) {
  const sourceRoot = join(temporary, 'source');
  populateSource(source, sourceRoot, temporary);
  runChecked('patch', ['--dry-run', '--batch', '-p1', '-i', PATCH_PATH], {
    cwd: sourceRoot,
  });
  runChecked('patch', ['--batch', '-p1', '-i', PATCH_PATH], { cwd: sourceRoot });
  const patchedDriverInterface = readFileSync(
    join(sourceRoot, 'src', 'driver', 'driver.mli'),
    'utf8',
  );
  if (!patchedDriverInterface.includes('val prepare_task_trace') ||
      !patchedDriverInterface.includes('val reference_profile_view')) {
    fail('trace patch application did not update the Why3 driver interface');
  }
  runChecked('./autogen.sh', [], { cwd: sourceRoot });
  runChecked('./configure', [
    `--prefix=${join(destination, 'install')}`,
    ...CONFIGURE_ARGUMENTS,
  ], { cwd: sourceRoot });
  const jobs = String(Math.max(1, Math.min(cpus().length, 4)));
  runChecked('make', [`-j${jobs}`, ...BUILD_TARGETS], {
    cwd: sourceRoot,
    maxBuffer: 512 * 1024 * 1024,
  });
  const runtimeDatadir = join(temporary, 'install', 'share', 'why3');
  mkdirSync(runtimeDatadir, { recursive: true });
  symlinkSync('../../../source/drivers', join(runtimeDatadir, 'drivers'), 'dir');
  symlinkSync('../../../source/stdlib', join(runtimeDatadir, 'stdlib'), 'dir');
  symlinkSync(
    '../../../source/share/provers-detection-data.conf',
    join(runtimeDatadir, 'provers-detection-data.conf'),
    'file',
  );
  const marker = {
    schemaVersion: 1,
    cacheKey,
    descriptor,
    artifacts: runtimeArtifacts(temporary).map(path =>
      path.slice(temporary.length + 1)),
    runtimeData: runtimeDataPaths(temporary).map(path =>
      path.slice(temporary.length + 1)),
  };
  writeFileSync(join(temporary, COMPLETE_MARKER), `${JSON.stringify(marker, null, 2)}\n`);
}

export function referenceRuntimeEnvironment(runtime, base = process.env) {
  return {
    ...base,
    LC_ALL: 'C',
    LANG: 'C',
    OCAMLPATH: [runtime.ocamlPath, base.OCAMLPATH].filter(Boolean).join(':'),
  };
}

export function prepareReferenceRuntime(options = {}) {
  const lock = readEnvironmentLock();
  const source = verifySource(options, lock);
  ensureRuntimeDependencies();
  const ocamlVersion = runChecked('ocamlc', ['-version']).trim();
  const descriptor = buildRuntimeDescriptor({ lock, ocamlVersion });
  const cacheKey = runtimeCacheKey(descriptor);
  const cacheRoot = resolve(
    process.env.WHY3_REFERENCE_CACHE_DIR ??
      join(PROJECT_ROOT, '_build', 'why3-reference-cache'),
  );
  mkdirSync(cacheRoot, { recursive: true });
  const directory = join(cacheRoot, cacheKey);
  let cacheHit = isCompleteRuntime(directory, cacheKey);
  if (!cacheHit) {
    const temporary = join(
      cacheRoot,
      `.build-${cacheKey}-${process.pid}-${randomBytes(8).toString('hex')}`,
    );
    mkdirSync(temporary);
    try {
      buildRuntime(temporary, directory, source, descriptor, cacheKey);
      publishRuntimeDirectory(temporary, directory, cacheKey);
    } catch (error) {
      rmSync(temporary, { recursive: true, force: true });
      throw error;
    }
    cacheHit = false;
  }
  process.stderr.write(
    `reference runtime: cache ${cacheHit ? 'hit' : 'miss'} ${cacheKey}\n`,
  );
  return {
    cacheHit,
    cacheKey,
    descriptor,
    directory,
    sourceRoot: join(directory, 'source'),
    ocamlPath: join(directory, 'source', 'lib'),
    lock,
  };
}
