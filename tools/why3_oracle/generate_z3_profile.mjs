// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  EXPECTED_WHY3_COMMIT,
  EXPECTED_WHY3_TREE,
  runChecked,
  sha256,
} from './export_driver_inventory.mjs';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const DRIVER_CONTRACT = join(PROJECT_ROOT, 'tools', 'contracts', 'driver-closure-v1.json');
const TRANSFORM_CONTRACT = join(PROJECT_ROOT, 'tools', 'contracts', 'transform-profile-v1.json');
const SNAPSHOT_MANIFEST = join(PROJECT_ROOT, 'stdlib', 'snapshot-manifest-v1.json');
const TRACE_PATCH = join(SCRIPT_DIRECTORY, 'patches', 'driver-trace.patch');
const DEFAULT_OUTPUT = join(PROJECT_ROOT, 'prover', 'z3', 'z3-static-profile-v1.json');

function fail(message) {
  throw new Error(message);
}

function readJson(path) {
  return JSON.parse(readFileSync(path, 'utf8'));
}

function equal(actual, expected, label) {
  if (JSON.stringify(actual) !== JSON.stringify(expected)) {
    fail(`${label} mismatch`);
  }
}

function parseArguments(argv) {
  let why3Root = resolve(PROJECT_ROOT, '..', 'why3');
  let rawProfile = null;
  let mode = 'stdout';
  let output = DEFAULT_OUTPUT;
  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index];
    if (argument === '--why3-root' || argument === '--raw-profile' ||
        argument === '--output' || argument === '--check') {
      const value = argv[index + 1];
      if (!value) fail(`${argument} requires a value`);
      if (argument === '--why3-root') why3Root = resolve(value);
      if (argument === '--raw-profile') rawProfile = resolve(value);
      if (argument === '--output' || argument === '--check') {
        if (mode !== 'stdout') fail('--output and --check are mutually exclusive');
        mode = argument.slice(2);
        output = resolve(value);
      }
      index += 1;
    } else {
      fail(`unknown argument: ${argument}`);
    }
  }
  if (rawProfile === null) fail('--raw-profile is required');
  return { why3Root, rawProfile, mode, output };
}

function requireSourceLine(source, line, label) {
  if (!source.split('\n').includes(line)) fail(`${label} drift`);
}

function buildProfile(options) {
  const commit = runChecked('git', ['-C', options.why3Root, 'rev-parse', 'HEAD']).trim();
  const tree = runChecked('git', ['-C', options.why3Root, 'rev-parse', 'HEAD^{tree}']).trim();
  if (commit !== EXPECTED_WHY3_COMMIT || tree !== EXPECTED_WHY3_TREE) {
    fail(`expected Why3 ${EXPECTED_WHY3_COMMIT}/${EXPECTED_WHY3_TREE}, got ${commit}/${tree}`);
  }
  runChecked('git', ['-C', options.why3Root, 'apply', '--check', TRACE_PATCH]);

  const driverContract = readJson(DRIVER_CONTRACT);
  const transformContract = readJson(TRANSFORM_CONTRACT);
  const snapshotManifest = readJson(SNAPSHOT_MANIFEST);
  const raw = readJson(options.rawProfile);
  if (raw.schemaVersion !== 1 || raw.driverProfile !== 'z3_487' ||
      raw.rootDriver !== 'z3_487.drv') {
    fail('raw Z3 profile identity mismatch');
  }
  equal(raw.transforms, driverContract.driver.transformations, 'driver transform order');
  if (raw.printer !== 'smtv2.6' || raw.filename !== '%f-%t-%g.smt2') {
    fail('raw Z3 printer/filename mismatch');
  }

  const rootDriver = readFileSync(join(options.why3Root, 'drivers', 'z3_487.drv'), 'utf8');
  const smtDriver = readFileSync(join(options.why3Root, 'drivers', 'smt-libv2.gen'), 'utf8');
  const detection = readFileSync(join(options.why3Root, 'share', 'provers-detection-data.conf'), 'utf8');
  requireSourceLine(rootDriver, 'steps ":rlimit-count +\\\\([0-9]+\\\\)" 1', 'Z3 step pattern');
  requireSourceLine(smtDriver, 'time "why3cpulimit time : %s s"', 'SMT time pattern');
  requireSourceLine(
    detection,
    'command = "%e -smt2 -T:%t sat.random_seed=42 nlsat.randomize=false smt.random_seed=42 -st %f"',
    'Z3 time command',
  );
  requireSourceLine(
    detection,
    'command_steps = "%e -smt2 sat.random_seed=42 nlsat.randomize=false smt.random_seed=42 -st rlimit=%S %f"',
    'Z3 steps command',
  );

  const transforms = raw.transforms;
  const monomorphicCheckpoints = ['driver-update', ...transforms];
  const polymorphicCheckpoints = ['driver-update'];
  for (const transform of transforms) {
    if (transform === 'discriminate_if_poly') {
      polymorphicCheckpoints.push('discriminate_if_poly:monomorphise_goal');
    }
    if (transform === 'encoding_smt_if_poly') {
      polymorphicCheckpoints.push(
        'encoding_smt_if_poly:monomorphise_goal',
        'encoding_smt_if_poly:select_kept',
        'encoding_smt_if_poly:keep_field_types',
        'encoding_smt_if_poly:twin',
        'encoding_smt_if_poly:guards',
      );
    }
    polymorphicCheckpoints.push(transform);
  }
  const tracePatchSha256 = sha256(readFileSync(TRACE_PATCH));
  if (transformContract.tracePatch.status !== 'active' ||
      transformContract.tracePatch.path !== 'tools/why3_oracle/patches/driver-trace.patch' ||
      transformContract.tracePatch.targetWhy3Commit !== commit ||
      transformContract.tracePatch.patchSha256 !== tracePatchSha256) {
    fail('transform profile does not bind the active trace patch');
  }
  equal(
    transformContract.tracePatch.checkpointSequences,
    {
      monomorphic: monomorphicCheckpoints,
      polymorphic: polymorphicCheckpoints,
    },
    'transform checkpoint sequences',
  );

  const { schemaVersion: _rawSchema, ...driver } = raw;
  return {
    schemaVersion: 1,
    why3: {
      version: '1.7.2',
      commit,
      tree,
    },
    evidence: {
      driverClosureSha256: driverContract.driver.sha256,
      transformProfileSha256: sha256(readFileSync(TRANSFORM_CONTRACT)),
      snapshotPayloadSha256: snapshotManifest.payload.sha256,
      snapshotCatalogSha256: snapshotManifest.symbolDigest.catalogSha256,
      tracePatchSha256,
      exporterSha256: sha256(readFileSync(join(SCRIPT_DIRECTORY, 'export_z3_profile.ml'))),
      generatorSha256: sha256(readFileSync(fileURLToPath(import.meta.url))),
    },
    tracePatch: {
      targetWhy3Commit: commit,
      checkpointSequences: transformContract.tracePatch.checkpointSequences,
    },
    command: {
      executable: 'z3',
      commonArguments: [
        '-smt2',
        'sat.random_seed=42',
        'nlsat.randomize=false',
        'smt.random_seed=42',
        '-st',
      ],
      timeLimitArgument: '-T:%t',
      stepLimitArgument: 'rlimit=%S',
      inputPlacement: 'last',
    },
    timePatterns: ['why3cpulimit time : %s s'],
    stepPatterns: [{ pattern: ':rlimit-count +\\([0-9]+\\)', group: 1 }],
    ...driver,
  };
}

export function main(argv = process.argv.slice(2)) {
  try {
    const options = parseArguments(argv);
    const bytes = Buffer.from(`${JSON.stringify(buildProfile(options), null, 2)}\n`);
    if (options.mode === 'output') {
      writeFileSync(options.output, bytes);
    } else if (options.mode === 'check') {
      const actual = readFileSync(options.output);
      if (!actual.equals(bytes)) fail(`${options.output} does not match generated profile`);
    } else {
      process.stdout.write(bytes);
    }
  } catch (error) {
    process.stderr.write(`generate_z3_profile: ${error.message}\n`);
    process.exitCode = 1;
  }
}

if (process.argv[1] !== undefined &&
    resolve(process.argv[1]) === fileURLToPath(import.meta.url)) main();
