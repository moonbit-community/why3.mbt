#!/usr/bin/env node
// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const PROJECT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..');
const WHY3_COMMIT = '1343338d3bb1941c0d4f134283bb0790816113c4';
const AST_FILES = [
  'parser/ast_common.mbt',
  'parser/ast_ident_type.mbt',
  'parser/ast_term.mbt',
  'parser/ast_decl.mbt',
  'parser/ast_expr.mbt',
  'literal/constant.mbt',
];

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

function discoverVariants() {
  const discovered = new Map();
  for (const path of AST_FILES) {
    const source = readFileSync(join(PROJECT_ROOT, path), 'utf8');
    const enumPattern =
      /pub(?:\(all\))?\s+enum\s+([A-Za-z][A-Za-z0-9_]*)\s*\{([\s\S]*?)\n\}/gu;
    for (const match of source.matchAll(enumPattern)) {
      const enumName = match[1];
      if (discovered.has(enumName)) fail(`duplicate public enum ${enumName}`);
      const variants = [];
      for (const line of match[2].split('\n')) {
        const variant = line.trim().match(/^([A-Z][A-Za-z0-9_]*)\b/u)?.[1];
        if (variant) variants.push(variant);
      }
      if (variants.length === 0) fail(`public enum ${enumName} has no variants`);
      discovered.set(enumName, { path, variants });
    }
  }
  return discovered;
}

function buildInventory() {
  const discovered = discoverVariants();
  const sources = AST_FILES.map(path => ({
    path,
    sha256: sha256(readFileSync(join(PROJECT_ROOT, path))),
  }));
  const variants = [...discovered.entries()]
    .flatMap(([enumName, entry]) => entry.variants.map(variant => ({
      id: `${enumName}.${variant}`,
      enum: enumName,
      variant,
      source: entry.path,
    })))
    .sort((left, right) => compareUtf8(left.id, right.id));
  return {
    schemaVersion: 1,
    contract: 'why3mbt-project-parser-ast-inventory-v1',
    why3Version: '1.7.2',
    why3Commit: WHY3_COMMIT,
    scope: {
      sourceOfTruth: 'MoonBit public parser/literal enums listed in sourceInventory',
      upstreamPtreeInventory: false,
      note:
        'These are project AST variants, not an inventory of Why3 Ptree constructors.',
    },
    policy: {
      lanesAssignedHere: false,
      officialBehaviorContract: 'tools/contracts/features-v2.json',
      legalBehavior: 'exact',
      illegalShape: 'reject with structured diagnostics',
    },
    counts: {
      sourceFiles: sources.length,
      enums: discovered.size,
      variants: variants.length,
    },
    sourceInventory: sources,
    sourceInventorySha256: canonicalSha(sources),
    variants,
    variantInventorySha256: canonicalSha(variants),
  };
}

function renderInventory() {
  return `${JSON.stringify(buildInventory(), null, 2)}\n`;
}

function run() {
  const [mode, path, ...rest] = process.argv.slice(2);
  if (rest.length > 0 ||
      (mode !== undefined && mode !== '--output' && mode !== '--check') ||
      (mode !== undefined && path === undefined)) {
    fail(
      'usage: generate_parser_ast_inventory.mjs ' +
        '[--output PATH | --check PATH]',
    );
  }
  const rendered = renderInventory();
  if (mode === '--output') {
    writeFileSync(resolve(path), rendered);
  } else if (mode === '--check') {
    if (readFileSync(resolve(path), 'utf8') !== rendered) {
      fail(`${path} does not match the generated parser AST inventory`);
    }
  } else {
    process.stdout.write(rendered);
  }
}

try {
  run();
} catch (error) {
  process.stderr.write(`generate_parser_ast_inventory: ${error.message}\n`);
  process.exitCode = 1;
}
