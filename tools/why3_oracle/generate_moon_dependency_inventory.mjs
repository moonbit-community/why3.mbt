// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import {
  lstatSync,
  readFileSync,
  readdirSync,
  readlinkSync,
  writeFileSync,
} from 'node:fs';
import { dirname, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..');
const MODULE_PATH = join(PROJECT_ROOT, 'moon.mod');
const CACHE_ROOT = join(PROJECT_ROOT, '.mooncakes');

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

function parseArguments(argv) {
  if (argv.length === 0) return { mode: 'stdout', path: null };
  if (argv.length !== 2 || !['--output', '--check'].includes(argv[0])) {
    fail('usage: generate_moon_dependency_inventory.mjs [--output PATH | --check PATH]');
  }
  return { mode: argv[0].slice(2), path: resolve(argv[1]) };
}

function declaredDependencies() {
  const source = readFileSync(MODULE_PATH, 'utf8');
  const imports = [];
  const semanticSource = source.replace(/^\s*\/\/.*$/gmu, '');
  const importBlock = semanticSource.match(/\bimport\s*\{([\s\S]*?)\n\}/u)?.[1];
  if (importBlock === undefined) fail('moon.mod has no import block');
  for (const match of importBlock.matchAll(/"([^"@]+\/[^"@]+)@([^"@]+)"/gu)) {
    imports.push({ name: match[1], version: match[2] });
  }
  imports.sort((left, right) => compareUtf8(left.name, right.name));
  if (imports.length === 0) fail('moon.mod import block is empty');
  const names = new Set(imports.map(dependency => dependency.name));
  if (names.size !== imports.length) fail('moon.mod contains duplicate dependency imports');
  return { source, imports };
}

function packageMetadata(root) {
  for (const name of ['moon.mod', 'moon.mod.json']) {
    try {
      const source = readFileSync(join(root, name), 'utf8');
      if (name.endsWith('.json')) {
        const parsed = JSON.parse(source);
        return { name: parsed.name, version: parsed.version };
      }
      const packageName = source.match(/^name\s*=\s*"([^"]+)"\s*$/mu)?.[1];
      const version = source.match(/^version\s*=\s*"([^"]+)"\s*$/mu)?.[1];
      return { name: packageName, version };
    } catch (error) {
      if (error.code !== 'ENOENT') throw error;
    }
  }
  fail(`dependency at ${root} has no moon.mod or moon.mod.json`);
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
        fail(`unsupported dependency entry ${path} (mode ${lstatSync(absolutePath).mode})`);
      }
    }
  }
  visit(root);
  return { entries, sha256: canonicalSha(entries) };
}

function buildInventory() {
  const { source, imports } = declaredDependencies();
  const dependencies = imports.map(dependency => {
    const root = join(CACHE_ROOT, ...dependency.name.split('/'));
    const metadata = packageMetadata(root);
    if (metadata.name !== dependency.name || metadata.version !== dependency.version) {
      fail(
        `${dependency.name} cache metadata is ${metadata.name}@${metadata.version}, ` +
        `expected ${dependency.name}@${dependency.version}`,
      );
    }
    return { ...dependency, tree: treeInventory(root) };
  });
  return {
    schemaVersion: 1,
    module: { path: 'moon.mod', sha256: sha256(source) },
    policy: {
      dependencySetComesFromExactMoonModImports: true,
      entryOrder: 'dependency name and POSIX relative path bytewise ascending',
      treeHash: 'SHA-256 of compact JSON entry inventory plus one LF',
      ignoredEntries: [],
    },
    dependencies,
    closureSha256: canonicalSha(dependencies.map(dependency => ({
      name: dependency.name,
      version: dependency.version,
      treeSha256: dependency.tree.sha256,
    }))),
  };
}

try {
  const arguments_ = parseArguments(process.argv.slice(2));
  const rendered = `${JSON.stringify(buildInventory(), null, 2)}\n`;
  if (arguments_.mode === 'output') {
    writeFileSync(arguments_.path, rendered);
  } else if (arguments_.mode === 'check') {
    if (readFileSync(arguments_.path, 'utf8') !== rendered) {
      fail(`${arguments_.path} does not match the installed Moon dependency closure`);
    }
  } else {
    process.stdout.write(rendered);
  }
} catch (error) {
  process.stderr.write(`generate_moon_dependency_inventory: ${error.message}\n`);
  process.exitCode = 1;
}
