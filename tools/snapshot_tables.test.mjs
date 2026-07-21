// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import test from 'node:test';
import { fileURLToPath } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const STDLIB = join(PROJECT_ROOT, 'stdlib');
const MANIFEST_PATH = join(STDLIB, 'snapshot-manifest-v1.json');

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function canonicalSha(value) {
  return sha256(`${JSON.stringify(value)}\n`);
}

function decodeMoonBytes(body) {
  const bytes = [];
  for (let index = 0; index < body.length; index += 1) {
    const character = body[index];
    if (character !== '\\') {
      bytes.push(character.charCodeAt(0));
      continue;
    }
    index += 1;
    const escaped = body[index];
    if (escaped === '"') bytes.push(0x22);
    else if (escaped === '\\') bytes.push(0x5c);
    else if (escaped === 'n') bytes.push(0x0a);
    else if (escaped === 'r') bytes.push(0x0d);
    else if (escaped === 't') bytes.push(0x09);
    else if (escaped === 'x') {
      const hex = body.slice(index + 1, index + 3);
      assert.match(hex, /^[0-9a-f]{2}$/u);
      bytes.push(Number.parseInt(hex, 16));
      index += 2;
    } else {
      assert.fail(`unsupported generated MoonBit byte escape \\${escaped}`);
    }
  }
  return Buffer.from(bytes);
}

function decodeShard(path) {
  const source = readFileSync(path, 'utf8');
  assert.doesNotMatch(source, /\bpub\b/u, `${path} exposes generated data`);
  const functionMatch = source.match(/^fn (generated_snapshot_[a-z0-9_]+)\(\) -> Array\[Bytes\] \{$/mu);
  assert(functionMatch, `${path} has no generated shard function`);
  const chunks = [];
  for (const line of source.split('\n')) {
    const literal = line.match(/^    b"(.*)",$/u);
    if (literal) chunks.push(decodeMoonBytes(literal[1]));
  }
  assert(chunks.length > 0, `${path} has no byte literals`);
  return [functionMatch[1], Buffer.concat(chunks)];
}

function snapshotPayload(manifest) {
  const shards = new Map();
  for (const file of manifest.generatedFiles) {
    if (file.path === 'generated_snapshot_index.mbt') continue;
    const [functionName, bytes] = decodeShard(join(STDLIB, file.path));
    assert(!shards.has(functionName), `duplicate generated function ${functionName}`);
    shards.set(functionName, bytes);
  }
  const indexSource = readFileSync(join(STDLIB, 'generated_snapshot_index.mbt'), 'utf8');
  assert.doesNotMatch(indexSource, /\bpub\b/u, 'snapshot index must remain private');
  const order = [...indexSource.matchAll(/^    (generated_snapshot_[a-z0-9_]+)\(\),$/gmu)]
    .map(match => match[1]);
  assert.equal(order.length, shards.size, 'snapshot shard index size');
  return Buffer.concat(order.map(name => {
    assert(shards.has(name), `snapshot index references unknown shard ${name}`);
    return shards.get(name);
  }));
}

function programNamespaceEntries(namespace, entries = new Map()) {
  for (const [nameHex, reference] of namespace.program) {
    entries.set(Buffer.from(nameHex, 'hex').toString('utf8'), reference);
  }
  for (const [, nested] of namespace.subspaces) programNamespaceEntries(nested, entries);
  return entries;
}

test('checked-in snapshot tables match their complete semantic manifest', () => {
  const manifest = JSON.parse(readFileSync(MANIFEST_PATH, 'utf8'));
  const payload = snapshotPayload(manifest);
  assert.equal(payload.length, manifest.payload.byteLength);
  assert.equal(sha256(payload), manifest.payload.sha256);
  assert.equal(payload.at(-1), 0x0a, 'snapshot payload final LF');

  const snapshot = JSON.parse(payload.toString('utf8'));
  assert.equal(snapshot.schemaVersion, manifest.snapshotSchemaVersion);
  assert.equal(snapshot.theories.length, manifest.counts.theories);
  assert.equal(snapshot.modules.length, manifest.counts.modules);
  assert.equal(snapshot.catalog.length, manifest.counts.symbols);
  assert.equal(snapshot.typeVariables.length, manifest.counts.typeVariables);
  assert.deepEqual(snapshot.roots, manifest.closure.rootMappings);
  assert.deepEqual(
    snapshot.roots.modules.map(root => root.requested),
    manifest.closure.userVisibleProgramRoots,
  );

  const generatedEvidence = manifest.generatedFiles.map(file => {
    const bytes = readFileSync(join(STDLIB, file.path));
    assert.equal(bytes.length, file.byteLength, `${file.path} byte length`);
    assert.equal(sha256(bytes), file.sha256, `${file.path} SHA-256`);
    return file;
  });
  assert.equal(canonicalSha(generatedEvidence), manifest.generatedTreeSha256);

  const locators = new Set();
  const catalogEvidence = snapshot.catalog.map(entry => {
    const { locator, key, symbol } = entry;
    assert.equal(
      locator.id,
      `${locator.theoryKey}#${locator.itemOrdinal}#${locator.innerOrdinal}#${locator.kind}`,
    );
    assert(!locators.has(locator.id), `duplicate snapshot locator ${locator.id}`);
    locators.add(locator.id);
    assert.deepEqual(key, {
      theoryKey: locator.theoryKey,
      theoryItemOrdinal: locator.itemOrdinal,
      declarationInnerOrdinal: locator.innerOrdinal,
      symbolKind: locator.kind,
      digest: canonicalSha(symbol),
    });
    return { locator: locator.id, digest: key.digest };
  });
  assert.equal(canonicalSha(catalogEvidence), manifest.symbolDigest.catalogSha256);

  const catalogByLocator = new Map(snapshot.catalog.map(entry => [entry.locator.id, entry]));
  for (const [moduleKey, requiredNames] of [
    ['int.Int', ['prefix -', 'infix <', 'infix >=']],
    ['real.Real', ['prefix -', 'infix +', 'infix -', 'infix *', 'infix /', 'infix <', 'infix >=']],
  ]) {
    const pmodule = snapshot.modules.find(candidate => candidate.key === moduleKey);
    assert(pmodule, `missing required program module ${moduleKey}`);
    const program = programNamespaceEntries(pmodule.exportNamespace);
    for (const name of requiredNames) {
      assert(program.has(name), `${moduleKey} omits program operator ${name}`);
      const catalogEntry = catalogByLocator.get(program.get(name));
      assert(catalogEntry, `${moduleKey}.${name} points outside the symbol catalog`);
      assert.equal(catalogEntry.symbol.tag, 'RoutineSymbol');
      assert(catalogEntry.symbol.cty, `${moduleKey}.${name} has no Cty`);
      assert.match(catalogEntry.symbol.logic[0], /^RL(?:ls|none)$/u);
    }
  }

  const theoryEvidence = snapshot.theories.map(theory => ({
    key: theory.key,
    canonicalSha256: canonicalSha(theory),
  }));
  const moduleEvidence = snapshot.modules.map(pmodule => ({
    key: pmodule.key,
    canonicalSha256: canonicalSha(pmodule),
  }));
  assert.deepEqual(theoryEvidence, manifest.closure.theoryCanonical);
  assert.deepEqual(moduleEvidence, manifest.closure.moduleCanonical);
  assert.deepEqual(snapshot.theories.map(theory => theory.key), manifest.closure.theories);
  assert.deepEqual(snapshot.modules.map(pmodule => pmodule.key), manifest.closure.modules);

  const transformInfluence = {
    driverClosureSha256: manifest.driver.closureSha256,
    transformations: manifest.driver.transformations,
    theories: theoryEvidence,
    modules: moduleEvidence,
    symbolCatalogSha256: manifest.symbolDigest.catalogSha256,
  };
  assert.equal(
    canonicalSha(transformInfluence),
    manifest.closure.transformInfluenceClosureSha256,
  );
});
