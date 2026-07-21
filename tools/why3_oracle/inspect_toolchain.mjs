// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import {
  lstatSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  readlinkSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..');

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function canonicalSha(value) {
  return sha256(`${JSON.stringify(value)}\n`);
}

function compareUtf8(left, right) {
  return Buffer.compare(Buffer.from(left, 'utf8'), Buffer.from(right, 'utf8'));
}

function toPosix(path) {
  return path.split(sep).join('/');
}

function run(path, argv) {
  const result = spawnSync(path, argv, {
    encoding: 'utf8',
    env: { ...process.env, LC_ALL: 'C' },
    shell: false,
  });
  if (result.status !== 0 || result.signal !== null || result.error) {
    fail(`${path} ${argv.join(' ')} failed: ${(result.stderr ?? result.error?.message ?? '').trim()}`);
  }
  return (result.stdout ?? '').trim();
}

function treeInventory(root) {
  const entries = [];
  function visit(directory) {
    const children = readdirSync(directory, { withFileTypes: true })
      .sort((left, right) => compareUtf8(left.name, right.name));
    for (const child of children) {
      const absolutePath = join(directory, child.name);
      const path = toPosix(relative(root, absolutePath));
      if (child.isDirectory()) {
        visit(absolutePath);
      } else if (child.isFile()) {
        entries.push({ path, kind: 'file', sha256: sha256(readFileSync(absolutePath)) });
      } else if (child.isSymbolicLink()) {
        const target = readlinkSync(absolutePath);
        entries.push({ path, kind: 'symlink', target, sha256: sha256(target) });
      } else {
        fail(`unsupported tree entry ${absolutePath} (mode ${lstatSync(absolutePath).mode})`);
      }
    }
  }
  visit(root);
  return { entries, sha256: canonicalSha(entries) };
}

function assertHash(path, expected) {
  const actual = sha256(readFileSync(path));
  if (actual !== expected) fail(`${path} hash drift: expected ${expected}, got ${actual}`);
  return actual;
}

function inspectShapeVersion() {
  const directory = mkdtempSync(join(tmpdir(), 'why3-shape-version-'));
  const source = join(directory, 'shape_version.ml');
  const executable = join(directory, 'shape-version');
  try {
    writeFileSync(source, [
      'open Why3',
      'let () =',
      '  Format.printf "%a@." Termcode.pp_sum_shape_version',
      '    Termcode.current_sum_shape_version',
      '',
    ].join('\n'));
    run('ocamlfind', [
      'ocamlopt',
      '-linkpkg',
      '-package',
      'why3',
      '-o',
      executable,
      source,
    ]);
    const output = run(executable, []);
    if (output !== '6') fail(`unexpected installed Why3 shape version: ${output}`);
    return 6;
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

function inspect() {
  const inputsPath = 'tools/contracts/toolchain-inputs-v1.json';
  const inputsBytes = readFileSync(join(PROJECT_ROOT, inputsPath));
  const inputs = JSON.parse(inputsBytes.toString('utf8'));
  const { toolchainInputsSha256, ...toolchainInputContent } = inputs;
  if (canonicalSha(toolchainInputContent) !== toolchainInputsSha256) {
    fail('toolchain input self hash drift');
  }
  const why3OpamRecipe = readFileSync(join(PROJECT_ROOT, inputs.why3.opamRecipe.path));
  if (sha256(why3OpamRecipe) !== inputs.why3.opamRecipe.sha256) {
    fail('vendored Why3 opam recipe hash drift');
  }
  const driverBytes = readFileSync(join(PROJECT_ROOT, inputs.why3.driverManifest));
  if (sha256(driverBytes) !== inputs.why3.driverManifestSha256) {
    fail('driver manifest file hash drift');
  }
  const driver = JSON.parse(driverBytes.toString('utf8'));
  const { sha256: driverClosureSha256, ...driverClosureContent } = driver.driver;
  if (canonicalSha(driverClosureContent) !== driverClosureSha256 ||
      driverClosureSha256 !== inputs.why3.driverClosureSha256) {
    fail('driver closure self hash drift');
  }
  const snapshot = driver.semanticSnapshot;
  const snapshotContent = {
    userVisibleProgramRoots: snapshot.userVisibleProgramRoots,
    theories: snapshot.theories,
    modules: snapshot.modules,
    records: snapshot.records,
    observedVariants: snapshot.observedVariants,
    stdlibTreeSha256: snapshot.stdlibTree.sha256,
  };
  if (canonicalSha(snapshotContent) !== snapshot.sha256 ||
      snapshot.sha256 !== inputs.why3.semanticSnapshotSha256) {
    fail('Why3 semantic snapshot self hash drift');
  }
  if (process.platform !== 'linux' || process.arch !== 'x64') {
    fail(`expected linux/x64, got ${process.platform}/${process.arch}`);
  }
  for (const [name, expected] of [['LC_ALL', 'C'], ['LANG', 'C'], ['TZ', 'UTC']]) {
    if (process.env[name] !== expected) {
      fail(`expected ${name}=${expected}, got ${process.env[name] ?? '<unset>'}`);
    }
  }

  const why3VersionOutput = run(inputs.why3.executablePath, ['--version']);
  if (why3VersionOutput !== `Why3 platform, version ${inputs.why3.version}`) {
    fail(`unexpected Why3 version: ${why3VersionOutput}`);
  }
  const z3VersionOutput = run(inputs.z3.executable.path, ['--version']);
  if (z3VersionOutput !== `Z3 version ${inputs.z3.version} - 64 bit`) {
    fail(`unexpected Z3 version: ${z3VersionOutput}`);
  }

  assertHash(inputs.z3.executable.path, inputs.z3.executable.sha256);
  assertHash(
    inputs.buildRecipe.sourceArchiveKeptInImage,
    inputs.why3.referenceArchive.sha256,
  );

  const datadirOutput = run(inputs.why3.executablePath, ['--print-datadir']);
  if (datadirOutput !== inputs.why3.datadirPath) {
    fail(`Why3 datadir is ${datadirOutput}, expected ${inputs.why3.datadirPath}`);
  }
  for (const file of [...driver.driver.files, ...driver.auxiliaryDrivers]) {
    assertHash(join(inputs.why3.datadirPath, 'drivers', file.path), file.sha256);
  }
  assertHash(
    join(inputs.why3.datadirPath, 'provers-detection-data.conf'),
    driver.proverDetection.sha256,
  );
  const stdlib = treeInventory(join(inputs.why3.datadirPath, 'stdlib'));
  if (stdlib.sha256 !== driver.semanticSnapshot.stdlibTree.sha256) {
    fail(`installed Why3 stdlib drift: ${stdlib.sha256}`);
  }

  return {
    schemaVersion: 1,
    platform: { os: process.platform, architecture: 'amd64', oci: 'linux/amd64' },
    toolchainInputs: {
      path: inputsPath,
      fileSha256: sha256(inputsBytes),
      contentSha256: inputs.toolchainInputsSha256,
    },
    why3: {
      version: inputs.why3.version,
      versionOutput: why3VersionOutput,
      commit: inputs.why3.commit,
      shapeVersion: inspectShapeVersion(),
      executable: {
        path: inputs.why3.executablePath,
        sha256: sha256(readFileSync(inputs.why3.executablePath)),
      },
      datadir: {
        path: inputs.why3.datadirPath,
        treeSha256: treeInventory(inputs.why3.datadirPath).sha256,
        stdlibTreeSha256: stdlib.sha256,
      },
      driverClosureSha256: driver.driver.sha256,
      proverDetectionSha256: driver.proverDetection.sha256,
      sourceArchiveSha256: inputs.why3.referenceArchive.sha256,
    },
    z3: {
      version: inputs.z3.version,
      versionOutput: z3VersionOutput,
      executable: inputs.z3.executable,
    },
    environment: { LC_ALL: 'C', LANG: 'C', TZ: 'UTC' },
  };
}

try {
  process.stdout.write(`${JSON.stringify(inspect(), null, 2)}\n`);
} catch (error) {
  process.stderr.write(`inspect_toolchain: ${error.message}\n`);
  process.exitCode = 1;
}
