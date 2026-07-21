// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import assert from 'node:assert/strict';
import {
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';

import referenceEnvironment from './why3_reference/reference_environment.cjs';
import {
  buildRuntimeDescriptor,
  installRuntimeDependencies,
  isCompleteRuntime,
  publishRuntimeDirectory,
  readRuntimeDependencies,
  runtimeCacheKey,
} from './why3_reference/reference_runtime.mjs';

function descriptorFixture(overrides = {}) {
  return buildRuntimeDescriptor({
    lock: referenceEnvironment.readEnvironmentLock(),
    ocamlVersion: '4.14.4',
    patchBytes: Buffer.from(overrides.patch ?? 'patch-a'),
    builderBytes: Buffer.from(overrides.builder ?? 'builder-a'),
  });
}

function completeFixture(directory, key, descriptor) {
  const library = join(directory, 'source', 'lib', 'why3');
  mkdirSync(library, { recursive: true });
  for (const name of ['why3.cmxa', 'why3.cma', 'META']) {
    writeFileSync(join(library, name), name);
  }
  const datadir = join(directory, 'install', 'share', 'why3');
  mkdirSync(join(datadir, 'drivers'), { recursive: true });
  mkdirSync(join(datadir, 'stdlib'));
  writeFileSync(join(datadir, 'provers-detection-data.conf'), 'data');
  writeFileSync(join(directory, '.complete.json'), `${JSON.stringify({
    schemaVersion: 1,
    cacheKey: key,
    descriptor,
    artifacts: [],
  })}\n`);
}

test('adapter dependencies are repository-pinned outside the Why3 cache key', () => {
  assert.deepEqual(readRuntimeDependencies().packages, [
    { opam: 'digestif', version: '1.3.0', findlib: ['digestif.ocaml'] },
    { opam: 'yojson', version: '2.1.0', findlib: ['yojson'] },
  ]);
  assert.equal(Object.hasOwn(descriptorFixture(), 'runtimeDependencies'), false);
});

test('runtime dependency installation refreshes opam before exact install', () => {
  const calls = [];
  const run = (command, argv) => calls.push([command, argv]);
  const execution = {
    uid: 1000,
    env: { OPAMROOT: '/home/opam/.opam' },
  };
  installRuntimeDependencies([], run, execution);
  installRuntimeDependencies(
    readRuntimeDependencies().packages,
    run,
    execution,
  );
  assert.deepEqual(calls, [
    ['opam', ['update']],
    ['opam', [
      'install',
      '--yes',
      'digestif.1.3.0',
      'yojson.2.1.0',
    ]],
  ]);
});

test('root installs runtime dependencies as the owner of the locked opam root', () => {
  const calls = [];
  const run = (command, argv) => calls.push([command, argv]);
  installRuntimeDependencies(
    readRuntimeDependencies().packages,
    run,
    {
      uid: 0,
      env: { OPAMROOT: '/home/opam/.opam' },
    },
  );
  const prefix = [
    '--user',
    'opam',
    '--preserve-environment',
    '--',
    'env',
    'HOME=/home/opam',
    'USER=opam',
    'LOGNAME=opam',
    'OPAMROOT=/home/opam/.opam',
    'opam',
  ];
  assert.deepEqual(calls, [
    ['runuser', [...prefix, 'update']],
    ['runuser', [
      ...prefix,
      'install',
      '--yes',
      'digestif.1.3.0',
      'yojson.2.1.0',
    ]],
  ]);
});

test('runtime key binds environment, source, patch, builder, arguments, and OCaml', () => {
  const first = descriptorFixture();
  const second = descriptorFixture({ patch: 'patch-b' });
  const third = descriptorFixture({ builder: 'builder-b' });
  const changedLock = referenceEnvironment.readEnvironmentLock();
  changedLock.image.digest = `sha256:${'b'.repeat(64)}`;
  const changedEnvironment = buildRuntimeDescriptor({
    lock: changedLock,
    ocamlVersion: '4.14.4',
    patchBytes: Buffer.from('patch-a'),
    builderBytes: Buffer.from('builder-a'),
  });
  const changedSourceLock = referenceEnvironment.readEnvironmentLock();
  changedSourceLock.why3.tree = 'c'.repeat(40);
  const changedSource = buildRuntimeDescriptor({
    lock: changedSourceLock,
    ocamlVersion: '4.14.4',
    patchBytes: Buffer.from('patch-a'),
    builderBytes: Buffer.from('builder-a'),
  });
  const changedCompiler = buildRuntimeDescriptor({
    lock: referenceEnvironment.readEnvironmentLock(),
    ocamlVersion: '4.14.3',
    patchBytes: Buffer.from('patch-a'),
    builderBytes: Buffer.from('builder-a'),
  });
  assert.notEqual(runtimeCacheKey(first), runtimeCacheKey(second));
  assert.notEqual(runtimeCacheKey(first), runtimeCacheKey(third));
  assert.notEqual(runtimeCacheKey(first), runtimeCacheKey(changedEnvironment));
  assert.notEqual(runtimeCacheKey(first), runtimeCacheKey(changedSource));
  assert.notEqual(runtimeCacheKey(first), runtimeCacheKey(changedCompiler));
  assert.deepEqual(first.buildTargets, [
    'lib/why3/why3.cmxa', 'lib/why3/why3.cma',
  ]);
  assert.equal(Object.hasOwn(first, 'adapter'), false);
  assert.equal(Object.hasOwn(first, 'fixtures'), false);
  assert.equal(Object.hasOwn(first, 'runtimeDependencies'), false);
});

test('runtime publication accepts only atomic completed directories', () => {
  const root = mkdtempSync(join(tmpdir(), 'why3-runtime-atomic-test-'));
  try {
    const descriptor = descriptorFixture();
    const key = runtimeCacheKey(descriptor);
    const incomplete = join(root, 'incomplete');
    mkdirSync(incomplete);
    assert.equal(isCompleteRuntime(incomplete, key), false);
    assert.throws(
      () => publishRuntimeDirectory(incomplete, join(root, 'rejected'), key),
      /refusing to publish incomplete/u,
    );

    const temporary = join(root, 'temporary');
    const destination = join(root, 'published');
    completeFixture(temporary, key, descriptor);
    assert.equal(publishRuntimeDirectory(temporary, destination, key), true);
    assert.equal(isCompleteRuntime(destination, key), true);
    assert.equal(readFileSync(join(destination, 'source', 'lib', 'why3', 'META'), 'utf8'), 'META');

    const racing = join(root, 'racing');
    completeFixture(racing, key, descriptor);
    assert.equal(publishRuntimeDirectory(racing, destination, key), false);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});
