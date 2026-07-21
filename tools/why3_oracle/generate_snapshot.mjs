// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import {
  mkdirSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  realpathSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  EXPECTED_WHY3_COMMIT,
  EXPECTED_WHY3_TREE,
  PROGRAM_ROOTS,
  WHY3_SOURCE_ARCHIVE,
  buildInventory,
  canonicalSha,
  compareUtf8,
  runChecked,
  sha256,
} from './export_driver_inventory.mjs';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const DRIVER_CONTRACT = join(PROJECT_ROOT, 'tools', 'contracts', 'driver-closure-v1.json');
const TRUSTED_SCHEMA = join(PROJECT_ROOT, 'tools', 'contracts', 'trusted-snapshot-schema-v1.json');
const EXPORTER_SOURCE = join(SCRIPT_DIRECTORY, 'export_snapshot.ml');
const INVENTORY_EXPORTER_SOURCE = join(SCRIPT_DIRECTORY, 'export_semantic_inventory.ml');
const DRIVER_EXPORTER_SOURCE = join(SCRIPT_DIRECTORY, 'export_driver_inventory.mjs');
const GENERATOR_SOURCE = fileURLToPath(import.meta.url);
const MANIFEST_NAME = 'snapshot-manifest-v1.json';
const TABLE_SLICE_BYTES = 512 * 1024;
const LITERAL_SLICE_BYTES = 16 * 1024;
const VISIBLE_SHARDS = ['builtin', 'bool', 'unit', 'int', 'real'];

function fail(message) {
  throw new Error(message);
}

function readJson(path) {
  return JSON.parse(readFileSync(path, 'utf8'));
}

function assertEqual(actual, expected, label) {
  if (JSON.stringify(actual) !== JSON.stringify(expected)) {
    fail(`${label} mismatch:\nexpected ${JSON.stringify(expected)}\nactual   ${JSON.stringify(actual)}`);
  }
}

function parseArguments(argv) {
  let why3Root = resolve(PROJECT_ROOT, '..', 'why3');
  let why3Archive = null;
  let outputMode = 'stdout';
  let outputDirectory = null;
  let sawWhy3Root = false;
  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index];
    if (argument === '--why3-root') {
      const value = argv[index + 1];
      if (!value) fail('--why3-root requires a path');
      why3Root = resolve(value);
      sawWhy3Root = true;
      index += 1;
    } else if (argument === '--why3-archive') {
      const value = argv[index + 1];
      if (!value) fail('--why3-archive requires a path');
      why3Archive = resolve(value);
      index += 1;
    } else if (argument === '--output-dir' || argument === '--check-dir') {
      const value = argv[index + 1];
      if (!value) fail(`${argument} requires a path`);
      if (outputMode !== 'stdout') {
        fail('--output-dir and --check-dir are mutually exclusive');
      }
      outputMode = argument === '--output-dir' ? 'output' : 'check';
      outputDirectory = resolve(value);
      index += 1;
    } else {
      fail(`unknown argument: ${argument}`);
    }
  }
  if (why3Archive !== null && sawWhy3Root) {
    fail('--why3-root and --why3-archive are mutually exclusive');
  }
  return { why3Root, why3Archive, outputMode, outputDirectory };
}

function verifyRepositoryRoot(why3Root) {
  const root = realpathSync(why3Root);
  const commit = runChecked('git', ['-C', root, 'rev-parse', 'HEAD']).trim();
  if (commit !== EXPECTED_WHY3_COMMIT) {
    fail(`expected Why3 ${EXPECTED_WHY3_COMMIT}, got ${commit}`);
  }
  const tree = runChecked('git', ['-C', root, 'rev-parse', 'HEAD^{tree}']).trim();
  if (tree !== EXPECTED_WHY3_TREE) {
    fail(`expected Why3 tree ${EXPECTED_WHY3_TREE}, got ${tree}`);
  }
  return root;
}

function withWhy3Source(options, action) {
  if (options.why3Archive === null) {
    return action(verifyRepositoryRoot(options.why3Root), false);
  }
  const archiveHash = sha256(readFileSync(options.why3Archive));
  if (archiveHash !== WHY3_SOURCE_ARCHIVE.sha256) {
    fail(`Why3 archive hash drift: expected ${WHY3_SOURCE_ARCHIVE.sha256}, got ${archiveHash}`);
  }
  const temporary = mkdtempSync(join(tmpdir(), 'why3-snapshot-source-'));
  try {
    runChecked('tar', ['-xzf', options.why3Archive, '-C', temporary], {
      cwd: temporary,
    });
    return action(join(temporary, `why3-${EXPECTED_WHY3_COMMIT}`), true);
  } finally {
    rmSync(temporary, { recursive: true, force: true });
  }
}

function exportSnapshot(why3Root, theoryRoots) {
  const buildDirectory = mkdtempSync(join(tmpdir(), 'why3-snapshot-exporter-'));
  const source = join(buildDirectory, 'export_snapshot.ml');
  const executable = join(buildDirectory, 'export-snapshot');
  try {
    writeFileSync(source, readFileSync(EXPORTER_SOURCE));
    runChecked('ocamlfind', [
      'ocamlopt',
      '-linkpkg',
      '-package',
      'why3,yojson,unix',
      '-o',
      executable,
      source,
    ], { cwd: buildDirectory });
    const exporterArgs = ['--stdlib', join(why3Root, 'stdlib')];
    for (const theory of theoryRoots) exporterArgs.push('--theory', theory);
    for (const pmodule of PROGRAM_ROOTS) exporterArgs.push('--module', pmodule);
    const output = runChecked(executable, exporterArgs, {
      cwd: PROJECT_ROOT,
      encoding: 'utf8',
      env: { ...process.env, LC_ALL: 'C' },
      maxBuffer: 128 * 1024 * 1024,
    });
    if (!output.endsWith('\n')) fail('snapshot exporter output has no final LF');
    return JSON.parse(output);
  } finally {
    rmSync(buildDirectory, { recursive: true, force: true });
  }
}

function sorted(values) {
  return [...values].sort(compareUtf8);
}

function validateVariants(snapshot, trusted) {
  const observed = snapshot.observedVariants;
  const allowed = trusted.allowedVariants;
  assertEqual(sorted(Object.keys(observed)), sorted(Object.keys(allowed)), 'variant categories');
  for (const category of Object.keys(allowed).sort(compareUtf8)) {
    assertEqual(sorted(observed[category]), sorted(allowed[category]), `observed ${category} variants`);
    const rejected = new Set(trusted.explicitlyRejectedTrustedVariants[category] ?? []);
    for (const variant of observed[category]) {
      if (rejected.has(variant)) {
        fail(`observed variant is also explicitly rejected: ${category}.${variant}`);
      }
    }
  }
}

function addSymbolKeys(snapshot) {
  const seenLocators = new Set();
  const keyedCatalog = snapshot.catalog.map(entry => {
    const locator = entry.locator;
    const expectedLocator = `${locator.theoryKey}#${locator.itemOrdinal}#${locator.innerOrdinal}#${locator.kind}`;
    if (locator.id !== expectedLocator) {
      fail(`malformed symbol locator ${locator.id}; expected ${expectedLocator}`);
    }
    if (seenLocators.has(locator.id)) fail(`duplicate symbol locator ${locator.id}`);
    seenLocators.add(locator.id);
    const digest = canonicalSha(entry.symbol);
    return {
      key: {
        theoryKey: locator.theoryKey,
        theoryItemOrdinal: locator.itemOrdinal,
        declarationInnerOrdinal: locator.innerOrdinal,
        symbolKind: locator.kind,
        digest,
      },
      locator,
      symbol: entry.symbol,
    };
  });
  return { ...snapshot, catalog: keyedCatalog };
}

function validateSnapshot(rawSnapshot, inventory, trusted) {
  if (rawSnapshot.schemaVersion !== trusted.schemaVersion) {
    fail(`snapshot schema ${rawSnapshot.schemaVersion} does not match trusted schema ${trusted.schemaVersion}`);
  }
  const theoryKeys = rawSnapshot.theories.map(theory => theory.key);
  const moduleKeys = rawSnapshot.modules.map(pmodule => pmodule.key);
  assertEqual(
    rawSnapshot.roots.theories.map(root => root.requested),
    inventory.driver.theoryRoots,
    'requested theory roots',
  );
  assertEqual(
    rawSnapshot.roots.modules.map(root => root.requested),
    PROGRAM_ROOTS,
    'requested program roots',
  );
  assertEqual(theoryKeys, inventory.semanticSnapshot.theories, 'theory closure');
  assertEqual(moduleKeys, inventory.semanticSnapshot.modules, 'module closure');
  if (new Set(theoryKeys).size !== theoryKeys.length) fail('duplicate theory key');
  if (new Set(moduleKeys).size !== moduleKeys.length) fail('duplicate module key');
  for (const root of rawSnapshot.roots.theories) {
    if (!theoryKeys.includes(root.resolvedKey)) {
      fail(`theory root ${root.requested} resolves outside the closure`);
    }
  }
  for (const root of rawSnapshot.roots.modules) {
    if (!moduleKeys.includes(root.resolvedKey)) {
      fail(`program root ${root.requested} resolves outside the closure`);
    }
  }
  validateVariants(rawSnapshot, trusted);
  for (const entry of rawSnapshot.catalog) {
    if (!theoryKeys.includes(entry.locator.theoryKey)) {
      fail(`catalog locator has no closure theory: ${entry.locator.id}`);
    }
  }
}

function moonBytesLiteral(bytes) {
  let result = 'b"';
  for (const byte of bytes) {
    if (byte === 0x22) result += '\\"';
    else if (byte === 0x5c) result += '\\\\';
    else if (byte === 0x0a) result += '\\n';
    else if (byte === 0x0d) result += '\\r';
    else if (byte === 0x09) result += '\\t';
    else if (byte >= 0x20 && byte <= 0x7e) result += String.fromCharCode(byte);
    else result += `\\x${byte.toString(16).padStart(2, '0')}`;
  }
  return `${result}"`;
}

function renderShard(functionName, bytes) {
  const literals = [];
  for (let offset = 0; offset < bytes.length; offset += LITERAL_SLICE_BYTES) {
    literals.push(moonBytesLiteral(bytes.subarray(offset, offset + LITERAL_SLICE_BYTES)));
  }
  return [
    '// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception',
    '// @generated by tools/why3_oracle/generate_snapshot.mjs; do not edit.',
    '',
    '///|',
    `fn ${functionName}() -> Array[Bytes] {`,
    '  [',
    ...literals.map(literal => `    ${literal},`),
    '  ]',
    '}',
    '',
  ].join('\n');
}

function shardName(index) {
  if (index < VISIBLE_SHARDS.length) return VISIBLE_SHARDS[index];
  return `driver_${String(index - VISIBLE_SHARDS.length).padStart(2, '0')}`;
}

function renderTables(payload) {
  const files = new Map();
  const functions = [];
  for (let offset = 0, index = 0; offset < payload.length;
    offset += TABLE_SLICE_BYTES, index += 1) {
    const name = shardName(index);
    const filename = `generated_${name}.mbt`;
    const functionName = `generated_snapshot_${name}`;
    const slice = payload.subarray(offset, offset + TABLE_SLICE_BYTES);
    files.set(filename, Buffer.from(renderShard(functionName, slice)));
    functions.push(functionName);
  }
  const indexSource = [
    '// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception',
    '// @generated by tools/why3_oracle/generate_snapshot.mjs; do not edit.',
    '',
    '///|',
    'fn generated_snapshot_shards() -> Array[Array[Bytes]] {',
    '  [',
    ...functions.map(name => `    ${name}(),`),
    '  ]',
    '}',
    '',
  ].join('\n');
  files.set('generated_snapshot_index.mbt', Buffer.from(indexSource));
  return files;
}

function fileEvidence(files) {
  return [...files.entries()]
    .map(([path, bytes]) => ({ path, byteLength: bytes.length, sha256: sha256(bytes) }))
    .sort((left, right) => compareUtf8(left.path, right.path));
}

function buildOutputs(why3Root, archiveVerified) {
  const inventory = buildInventory(why3Root, { archiveVerified });
  const lockedInventory = readJson(DRIVER_CONTRACT);
  assertEqual(inventory, lockedInventory, 'recursive driver inventory');
  const trusted = readJson(TRUSTED_SCHEMA);
  if (trusted.why3Commit !== EXPECTED_WHY3_COMMIT) {
    fail(`trusted schema Why3 commit drift: ${trusted.why3Commit}`);
  }
  if (trusted.driverProfile !== inventory.driver.profile) {
    fail(`trusted schema driver profile drift: ${trusted.driverProfile}`);
  }
  if (trusted.closureEvidence.driverSha256 !== inventory.driver.sha256 ||
      trusted.closureEvidence.semanticSnapshotSha256 !== inventory.semanticSnapshot.sha256 ||
      trusted.closureEvidence.stdlibTreeSha256 !== inventory.semanticSnapshot.stdlibTree.sha256) {
    fail('trusted schema closure evidence does not match the recursive driver inventory');
  }
  const rawSnapshot = exportSnapshot(why3Root, inventory.driver.theoryRoots);
  validateSnapshot(rawSnapshot, inventory, trusted);
  const snapshot = addSymbolKeys(rawSnapshot);
  const payload = Buffer.from(`${JSON.stringify(snapshot)}\n`);
  const files = renderTables(payload);
  const generatedFiles = fileEvidence(files);
  const catalogEvidence = snapshot.catalog.map(entry => ({
    locator: entry.locator.id,
    digest: entry.key.digest,
  }));
  const theoryEvidence = snapshot.theories.map(theory => ({
    key: theory.key,
    canonicalSha256: canonicalSha(theory),
  }));
  const moduleEvidence = snapshot.modules.map(pmodule => ({
    key: pmodule.key,
    canonicalSha256: canonicalSha(pmodule),
  }));
  const sourceFiles = [
    ['tools/why3_oracle/generate_snapshot.mjs', GENERATOR_SOURCE],
    ['tools/why3_oracle/export_snapshot.ml', EXPORTER_SOURCE],
    ['tools/why3_oracle/export_semantic_inventory.ml', INVENTORY_EXPORTER_SOURCE],
    ['tools/why3_oracle/export_driver_inventory.mjs', DRIVER_EXPORTER_SOURCE],
    ['tools/contracts/driver-closure-v1.json', DRIVER_CONTRACT],
    ['tools/contracts/trusted-snapshot-schema-v1.json', TRUSTED_SCHEMA],
  ].map(([path, absolute]) => ({ path, sha256: sha256(readFileSync(absolute)) }));
  const transformInfluence = {
    driverClosureSha256: inventory.driver.sha256,
    transformations: inventory.driver.transformations,
    theories: theoryEvidence,
    modules: moduleEvidence,
    symbolCatalogSha256: canonicalSha(catalogEvidence),
  };
  const manifest = {
    schemaVersion: 1,
    snapshotSchemaVersion: trusted.schemaVersion,
    exporterVersion: 1,
    why3: {
      version: inventory.why3.version,
      commit: inventory.why3.commit,
      tree: inventory.why3.tree,
      shapeVersion: inventory.why3.shapeVersion,
    },
    driver: {
      profile: inventory.driver.profile,
      closureSha256: inventory.driver.sha256,
      files: inventory.driver.files,
      loadOrder: inventory.driver.loadOrder,
      theoryRoots: inventory.driver.theoryRoots,
      transformations: inventory.driver.transformations,
    },
    closure: {
      userVisibleProgramRoots: PROGRAM_ROOTS,
      rootMappings: snapshot.roots,
      theories: inventory.semanticSnapshot.theories,
      modules: inventory.semanticSnapshot.modules,
      semanticInventorySha256: inventory.semanticSnapshot.sha256,
      stdlibTreeSha256: inventory.semanticSnapshot.stdlibTree.sha256,
      theoryCanonical: theoryEvidence,
      moduleCanonical: moduleEvidence,
      transformInfluenceClosureSha256: canonicalSha(transformInfluence),
    },
    sources: sourceFiles,
    counts: {
      theories: snapshot.theories.length,
      modules: snapshot.modules.length,
      symbols: snapshot.catalog.length,
      typeVariables: snapshot.typeVariables.length,
      generatedTableFiles: generatedFiles.length,
    },
    symbolDigest: {
      algorithm: 'sha256(ordered-json-v1(symbol) + LF)',
      catalogSha256: canonicalSha(catalogEvidence),
    },
    payload: {
      encoding: 'utf8-compact-json-v1',
      byteLength: payload.length,
      sha256: sha256(payload),
    },
    generatedFiles,
    generatedTreeSha256: canonicalSha(generatedFiles),
  };
  files.set(MANIFEST_NAME, Buffer.from(`${JSON.stringify(manifest, null, 2)}\n`));
  return { files, manifest };
}

function expectedNames(files) {
  return sorted(files.keys());
}

function managedNames(directory) {
  return sorted(readdirSync(directory).filter(name =>
    name === MANIFEST_NAME || /^generated_.*\.mbt$/u.test(name)));
}

function writeOutputs(directory, files) {
  mkdirSync(directory, { recursive: true });
  const actualManaged = managedNames(directory);
  const expectedManaged = expectedNames(files);
  const stale = actualManaged.filter(name => !files.has(name));
  if (stale.length > 0) {
    fail(`refusing to leave stale generated snapshot files: ${stale.join(', ')}`);
  }
  for (const [name, bytes] of files) writeFileSync(join(directory, name), bytes);
  assertEqual(managedNames(directory), expectedManaged, 'generated snapshot file set');
}

function checkOutputs(directory, files) {
  assertEqual(managedNames(directory), expectedNames(files), 'generated snapshot file set');
  for (const [name, expected] of files) {
    const actual = readFileSync(join(directory, name));
    if (!actual.equals(expected)) fail(`${name} does not match generated snapshot output`);
  }
}

export function main(argv = process.argv.slice(2)) {
  const options = parseArguments(argv);
  try {
    const result = withWhy3Source(options, (why3Root, archiveVerified) =>
      buildOutputs(why3Root, archiveVerified));
    if (options.outputMode === 'output') {
      writeOutputs(options.outputDirectory, result.files);
    } else if (options.outputMode === 'check') {
      checkOutputs(options.outputDirectory, result.files);
    } else {
      process.stdout.write(`${JSON.stringify(result.manifest, null, 2)}\n`);
    }
  } catch (error) {
    process.stderr.write(`generate_snapshot: ${error.message}\n`);
    process.exitCode = 1;
  }
}

if (process.argv[1] !== undefined &&
    resolve(process.argv[1]) === fileURLToPath(import.meta.url)) main();
