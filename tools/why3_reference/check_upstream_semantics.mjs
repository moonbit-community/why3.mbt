// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawn, spawnSync } from 'node:child_process';
import {
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import {
  collectUpstreamCorpus,
  compareInventoryToContract,
  mapConcurrent,
  validateUpstreamCorpusContract,
} from './upstream_corpus.mjs';
import {
  prepareReferenceRuntime,
  referenceRuntimeEnvironment,
} from './reference_runtime.mjs';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const DEFAULT_CONTRACT = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'upstream-corpus-v1.json',
);
const SEMANTIC_PROFILE = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'semantic-profile-v3.json',
);
const DIAGNOSTIC_CONTRACT = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'diagnostics-v1.json',
);
const Z3_PROFILE = join(
  PROJECT_ROOT,
  'prover',
  'z3',
  'z3-static-profile-v1.json',
);
const PRODUCT = join(
  PROJECT_ROOT,
  '_build',
  'native',
  'release',
  'build',
  'cmd',
  'elab_canonical',
  'elab_canonical.exe',
);
const DEBUG_PRODUCT = join(
  PROJECT_ROOT,
  '_build',
  'native',
  'debug',
  'build',
  'cmd',
  'elab_canonical',
  'elab_canonical.exe',
);
const CANONICAL_MARKER = Buffer.from(',"canonical":', 'utf8');
const RECORD_END = Buffer.from('}\n', 'utf8');
const STDERR_LIMIT = 64 * 1024;
const RECORD_PREFIX_LIMIT = 64 * 1024;

function fail(message) {
  throw new Error(message);
}

function readJson(path) {
  return JSON.parse(readFileSync(path, 'utf8'));
}

function runChecked(command, argv, options = {}) {
  const result = spawnSync(command, argv, {
    cwd: options.cwd ?? PROJECT_ROOT,
    encoding: 'utf8',
    env: options.env ?? process.env,
    maxBuffer: options.maxBuffer ?? 128 * 1024 * 1024,
    shell: false,
  });
  if (result.status !== 0 || result.signal !== null ||
      (result.error && result.error.code !== 'EPERM')) {
    const detail =
      `${result.stdout ?? ''}${result.stderr ?? ''}` +
      `${result.error?.message ?? ''}`;
    fail(`${command} ${argv.join(' ')} failed: ${detail.trim()}`);
  }
  return result.stdout ?? '';
}

function copyReferenceSource(buildDirectory, name) {
  writeFileSync(
    join(buildDirectory, name),
    readFileSync(join(SCRIPT_DIRECTORY, name)),
  );
}

function compileReference(buildDirectory, runtime) {
  const env = referenceRuntimeEnvironment(runtime);
  for (const name of [
    'canonical_v3_profile.ml',
    'canonical_v3.ml',
    'canonical_graph_v3.ml',
    'export_upstream_semantics.ml',
  ]) {
    copyReferenceSource(buildDirectory, name);
  }
  for (const source of [
    'canonical_v3_profile.ml',
    'canonical_v3.ml',
    'canonical_graph_v3.ml',
  ]) {
    runChecked('ocamlfind', [
      'ocamlopt',
      '-package',
      'why3,yojson,digestif.ocaml,unix',
      '-c',
      source,
    ], { cwd: buildDirectory, env });
  }
  const executable = join(buildDirectory, 'export-upstream-semantics');
  runChecked('ocamlfind', [
    'ocamlopt',
    '-linkpkg',
    '-package',
    'why3,yojson,digestif.ocaml,unix',
    '-o',
    executable,
    'canonical_v3_profile.cmx',
    'canonical_v3.cmx',
    'canonical_graph_v3.cmx',
    'export_upstream_semantics.ml',
  ], { cwd: buildDirectory, env });
  return executable;
}

class CanonicalRecordScanner {
  constructor(label, captureRecords = 1) {
    this.label = label;
    this.captureRecords = captureRecords;
    this.state = 'prefix';
    this.prefix = Buffer.alloc(0);
    this.pending = Buffer.alloc(0);
    this.hash = null;
    this.canonicalChunks = null;
    this.canonicalBytes = 0;
    this.records = [];
  }

  push(chunk) {
    let input = Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk);
    while (input.length !== 0) {
      if (this.state === 'prefix') {
        const combined = this.prefix.length === 0
          ? input
          : Buffer.concat([this.prefix, input]);
        const marker = combined.indexOf(CANONICAL_MARKER);
        if (marker < 0) {
          if (combined.length > RECORD_PREFIX_LIMIT) {
            fail(`${this.label}: canonical record prefix is too large`);
          }
          this.prefix = Buffer.from(combined);
          return;
        }
        const rawPrefix = combined.subarray(0, marker).toString('utf8');
        let metadata;
        try {
          metadata = JSON.parse(`${rawPrefix}}`);
        } catch (error) {
          fail(`${this.label}: invalid canonical record prefix: ${error.message}`);
        }
        if (!/^[0-9a-f]{64}$/u.test(metadata.canonical_sha256 ?? '')) {
          fail(`${this.label}: record has no valid canonical SHA-256`);
        }
        this.current = { rawPrefix, metadata };
        this.state = 'canonical';
        this.prefix = Buffer.alloc(0);
        this.pending = Buffer.alloc(0);
        this.hash = createHash('sha256');
        this.canonicalChunks =
          this.records.length < this.captureRecords ? [] : null;
        this.canonicalBytes = 0;
        input = combined.subarray(marker + CANONICAL_MARKER.length);
      } else {
        const combined = this.pending.length === 0
          ? input
          : Buffer.concat([this.pending, input]);
        const end = combined.indexOf(RECORD_END);
        if (end < 0) {
          if (combined.length > 1) {
            const safe = combined.subarray(0, combined.length - 1);
            this.hash.update(safe);
            if (this.canonicalChunks !== null) {
              this.canonicalChunks.push(Buffer.from(safe));
            }
            this.canonicalBytes += safe.length;
          }
          this.pending = Buffer.from(
            combined.subarray(Math.max(0, combined.length - 1)),
          );
          return;
        }
        const finalCanonical = combined.subarray(0, end);
        this.hash.update(finalCanonical);
        this.hash.update('\n');
        if (this.canonicalChunks !== null) {
          this.canonicalChunks.push(Buffer.from(finalCanonical));
        }
        this.canonicalBytes += finalCanonical.length;
        const actualSha256 = this.hash.digest('hex');
        if (this.canonicalBytes === 0) {
          fail(`${this.label}: record has an empty canonical payload`);
        }
        if (actualSha256 !== this.current.metadata.canonical_sha256) {
          fail(
            `${this.label}: record ${this.records.length} canonical hash ` +
            `is ${actualSha256}, claimed ` +
            `${this.current.metadata.canonical_sha256}`,
          );
        }
        this.records.push({
          ...this.current,
          canonicalBytes: this.canonicalBytes,
          canonicalText: this.canonicalChunks === null
            ? null
            : Buffer.concat(this.canonicalChunks).toString('utf8'),
        });
        this.current = null;
        this.state = 'prefix';
        this.pending = Buffer.alloc(0);
        this.hash = null;
        this.canonicalChunks = null;
        this.canonicalBytes = 0;
        input = combined.subarray(end + RECORD_END.length);
      }
    }
  }

  finish() {
    if (this.state !== 'prefix' || this.prefix.length !== 0) {
      fail(`${this.label}: truncated canonical NDJSON stream`);
    }
    return this.records;
  }
}

function collectCanonicalRecords(
  command,
  argv,
  {
    label,
    env = process.env,
    timeoutMs = 30 * 60 * 1000,
    captureRecords = 1,
  },
) {
  return new Promise((resolveRecords, rejectRecords) => {
    const scanner = new CanonicalRecordScanner(label, captureRecords);
    const child = spawn(command, argv, {
      cwd: PROJECT_ROOT,
      env,
      stdio: ['ignore', 'pipe', 'pipe'],
      shell: false,
    });
    let stderr = '';
    let timedOut = false;
    let streamError = null;
    let settled = false;
    const finish = (status, signal, processError = null) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      if (streamError !== null) {
        rejectRecords(streamError);
        return;
      }
      if (timedOut || status !== 0 || signal !== null || processError !== null) {
        rejectRecords(new Error(
          `${label} failed` +
          `${timedOut ? ' after timeout' : ''}` +
          `${status === null ? '' : ` with status ${status}`}` +
          `${signal === null ? '' : ` from signal ${signal}`}` +
          `${processError === null ? '' : `: ${processError.message}`}` +
          `${stderr.trim() === '' ? '' : `: ${stderr.trim()}`}`,
        ));
        return;
      }
      try {
        resolveRecords(scanner.finish());
      } catch (error) {
        rejectRecords(error);
      }
    };
    const timer = setTimeout(() => {
      timedOut = true;
      child.kill('SIGKILL');
    }, timeoutMs);
    child.stdout.on('data', chunk => {
      if (streamError !== null) return;
      try {
        scanner.push(chunk);
      } catch (error) {
        streamError = error;
        child.kill('SIGKILL');
      }
    });
    child.stderr.setEncoding('utf8');
    child.stderr.on('data', chunk => {
      if (stderr.length < STDERR_LIMIT) {
        stderr += chunk.slice(0, STDERR_LIMIT - stderr.length);
      }
    });
    child.on('error', error => finish(null, null, error));
    child.on('close', (status, signal) => finish(status, signal));
  });
}

function goalIdentity(record) {
  return [
    record.unit_name_hex,
    record.goal_name_hex,
    record.goal_ordinal,
  ].join(':');
}

function validateSemanticRecords(
  records,
  entry,
  profiles,
  producer,
) {
  const counts = {
    typedUnits: 0,
    rawTasks: 0,
    transformCheckpoints: 0,
    preparedTasks: 0,
    smtTokens: 0,
    canonicalBytes: 0,
  };
  for (let recordIndex = 0; recordIndex < records.length; recordIndex += 1) {
    const record = records[recordIndex];
    const metadata = record.metadata;
    counts.canonicalBytes += record.canonicalBytes;
    if (metadata.schema !== 3 ||
        metadata.semantic_profile_sha256 !== profiles.semantic ||
        metadata.diagnostic_contract_sha256 !== profiles.diagnostic ||
        metadata.fixture !== entry.path ||
        metadata.source_sha256 !== entry.sourceSha256) {
      fail(
        `${producer} ${entry.path} record ${recordIndex} has invalid ` +
        'portable metadata',
      );
    }
  }
  let currentUnit = null;
  let index = 0;
  while (index < records.length) {
    const record = records[index];
    const metadata = record.metadata;
    if (metadata.scope === 'unit') {
      if ((metadata.unit_kind === 'theory' &&
           metadata.stage !== 'typed-semantic') ||
          (metadata.unit_kind === 'module' &&
           metadata.stage !== 'typed-program') ||
          (metadata.unit_kind !== 'theory' &&
           metadata.unit_kind !== 'module')) {
        fail(
          `${producer} ${entry.path} record ${index} has invalid typed stage`,
        );
      }
      currentUnit = metadata.unit_name_hex;
      counts.typedUnits += 1;
      index += 1;
      continue;
    }
    if (metadata.scope !== 'goal' ||
        metadata.unit_kind !== 'theory' ||
        metadata.stage !== 'raw-task' ||
        currentUnit === null ||
        metadata.unit_name_hex !== currentUnit ||
        !/^[0-9a-f]*$/u.test(metadata.goal_name_hex ?? '') ||
        !Number.isInteger(metadata.goal_ordinal) ||
        metadata.goal_ordinal < 0) {
      fail(
        `${producer} ${entry.path} record ${index} does not start a valid goal chain`,
      );
    }
    const identity = goalIdentity(metadata);
    counts.rawTasks += 1;
    index += 1;
    const stages = [];
    let lastCheckpoint = null;
    while (index < records.length &&
           records[index].metadata.stage !== 'prepared-task') {
      const checkpoint = records[index].metadata;
      if (checkpoint.scope !== 'goal' ||
          goalIdentity(checkpoint) !== identity) {
        fail(
          `${producer} ${entry.path} goal ${identity} has a broken checkpoint chain`,
        );
      }
      stages.push(checkpoint.stage);
      lastCheckpoint = checkpoint;
      counts.transformCheckpoints += 1;
      index += 1;
    }
    const validSequence =
      JSON.stringify(stages) === JSON.stringify(profiles.monomorphic) ||
      JSON.stringify(stages) === JSON.stringify(profiles.polymorphic);
    if (!validSequence || lastCheckpoint === null ||
        index >= records.length) {
      fail(
        `${producer} ${entry.path} goal ${identity} has checkpoint sequence ` +
        `${JSON.stringify(stages)}`,
      );
    }
    const preparedRecord = records[index];
    const prepared = preparedRecord.metadata;
    if (goalIdentity(prepared) !== identity ||
        prepared.stage !== 'prepared-task' ||
        prepared.canonical_sha256 !== lastCheckpoint.canonical_sha256) {
      fail(
        `${producer} ${entry.path} goal ${identity} has an invalid prepared task`,
      );
    }
    counts.preparedTasks += 1;
    index += 1;
    if (index >= records.length) {
      fail(`${producer} ${entry.path} goal ${identity} has no SMT tokens`);
    }
    const smtRecord = records[index];
    const smt = smtRecord.metadata;
    if (goalIdentity(smt) !== identity || smt.stage !== 'smt-tokens') {
      fail(
        `${producer} ${entry.path} goal ${identity} has invalid SMT tokens`,
      );
    }
    counts.smtTokens += 1;
    index += 1;
  }
  if (counts.rawTasks !== counts.preparedTasks ||
      counts.rawTasks !== counts.smtTokens) {
    fail(`${producer} ${entry.path} has incomplete goal-stage coverage`);
  }
  return counts;
}

function compareSemanticRecords(target, reference, entry) {
  const sharedLength = Math.min(target.length, reference.length);
  for (let index = 0; index < sharedLength; index += 1) {
    if (target[index].rawPrefix !== reference[index].rawPrefix) {
      const targetMetadata = target[index].metadata;
      const referenceMetadata = reference[index].metadata;
      const canonicalDifference = describeCanonicalDifference(
        target[index],
        reference[index],
      );
      fail(
        `${entry.path}: semantic mismatch at record ${index}; target ` +
        `${JSON.stringify(targetMetadata)}, reference ` +
        `${JSON.stringify(referenceMetadata)}${canonicalDifference}`,
      );
    }
  }
  if (target.length !== reference.length) {
    const index = sharedLength;
    fail(
      `${entry.path}: target emitted ${target.length} semantic records, ` +
      `reference emitted ${reference.length}; first unpaired record ${index}: ` +
      `target ${JSON.stringify(target[index]?.metadata ?? null)}, reference ` +
      `${JSON.stringify(reference[index]?.metadata ?? null)}`,
    );
  }
}

function firstJsonDifference(
  target,
  reference,
  path = '$',
  ignoreCanonicalIds = false,
) {
  if (Object.is(target, reference)) return null;
  if (Array.isArray(target) && Array.isArray(reference)) {
    if (ignoreCanonicalIds &&
        target[0] === 'Reference' && reference[0] === 'Reference' &&
        target[1] === reference[1]) {
      return null;
    }
    const sharedLength = Math.min(target.length, reference.length);
    for (let index = 0; index < sharedLength; index += 1) {
      if (ignoreCanonicalIds && index === 2 &&
          target[0] === 'Definition' && reference[0] === 'Definition' &&
          target[1] === reference[1]) {
        continue;
      }
      const difference = firstJsonDifference(
        target[index],
        reference[index],
        `${path}[${index}]`,
        ignoreCanonicalIds,
      );
      if (difference !== null) {
        difference.contexts ??= [];
        difference.contexts.push({ target, reference });
        return difference;
      }
    }
    if (target.length === reference.length) return null;
    return {
      path: `${path}.length`,
      target: target.length,
      reference: reference.length,
    };
  }
  if (target !== null && reference !== null &&
      typeof target === 'object' && typeof reference === 'object') {
    const targetKeys = Object.keys(target);
    const referenceKeys = Object.keys(reference);
    const sharedLength = Math.min(targetKeys.length, referenceKeys.length);
    for (let index = 0; index < sharedLength; index += 1) {
      if (targetKeys[index] !== referenceKeys[index]) {
        return {
          path: `${path}.[key ${index}]`,
          target: targetKeys[index],
          reference: referenceKeys[index],
        };
      }
      const key = targetKeys[index];
      const difference = firstJsonDifference(
        target[key],
        reference[key],
        `${path}.${key}`,
        ignoreCanonicalIds,
      );
      if (difference !== null) {
        difference.contexts ??= [];
        difference.contexts.push({ target, reference });
        return difference;
      }
    }
    if (targetKeys.length === referenceKeys.length) return null;
    return {
      path: `${path}.[key count]`,
      target: targetKeys.length,
      reference: referenceKeys.length,
    };
  }
  return { path, target, reference };
}

function diagnosticValue(value, limit = 512) {
  const encoded = JSON.stringify(value);
  if (encoded === undefined) return String(value);
  if (encoded.length <= limit) return encoded;
  return `${encoded.slice(0, limit - 3)}...`;
}

function definitionInventory(graph) {
  if (!Array.isArray(graph) || graph[0] !== 'GraphV3' ||
      !Array.isArray(graph[2])) {
    return null;
  }
  const inventory = {};
  for (const definition of graph[2]) {
    if (!Array.isArray(definition) || definition[0] !== 'Definition') continue;
    inventory[definition[1]] = (inventory[definition[1]] ?? 0) + 1;
  }
  return inventory;
}

function canonicalDefinitionMap(graph) {
  const definitions = new Map();
  if (!Array.isArray(graph) || graph[0] !== 'GraphV3' ||
      !Array.isArray(graph[2])) {
    return definitions;
  }
  for (const definition of graph[2]) {
    if (Array.isArray(definition) && definition[0] === 'Definition') {
      definitions.set(`${definition[1]}:${definition[2]}`, definition[3]);
    }
  }
  return definitions;
}

function canonicalReferenceValue(definitions, reference) {
  if (!Array.isArray(reference) || reference[0] !== 'Reference') return null;
  return definitions.get(`${reference[1]}:${reference[2]}`) ?? null;
}

function canonicalHexText(value) {
  if (Array.isArray(value) && value[0] === 'Bytes') value = value[1];
  if (typeof value !== 'string' || !/^(?:[0-9a-f]{2})*$/u.test(value)) {
    return diagnosticValue(value);
  }
  return Buffer.from(value, 'hex').toString('utf8');
}

function canonicalIdentifierName(definitions, reference) {
  const value = canonicalReferenceValue(definitions, reference);
  if (!Array.isArray(value) || value[0] !== 'Product' ||
      !Array.isArray(value[1]) || !Array.isArray(value[1][0]) ||
      value[1][0][0] !== 'Ident.ident') {
    return '<identifier>';
  }
  return canonicalHexText(value[1][0][1]);
}

function canonicalSymbolName(definitions, reference) {
  const value = canonicalReferenceValue(definitions, reference);
  if (!Array.isArray(value)) return '<symbol>';
  if (['Ty.tysymbol', 'Term.lsymbol', 'Decl.prsymbol'].includes(value[0])) {
    return canonicalIdentifierName(definitions, value[1]);
  }
  return `<${value[0] ?? 'symbol'}>`;
}

function canonicalDeclarationSummary(definitions, reference) {
  const value = canonicalReferenceValue(definitions, reference);
  if (!Array.isArray(value) || value[0] !== 'Product' ||
      !Array.isArray(value[1]) || !Array.isArray(value[1][0]) ||
      value[1][0][0] !== 'Decl.decl' ||
      !Array.isArray(value[1][0][1])) {
    return 'Decl <unknown>';
  }
  const node = value[1][0][1];
  const tag = node[0];
  let symbol = null;
  if (tag === 'Decl.decl_node.Dtype') {
    symbol = Array.isArray(node[1]) && node[1][0] === 'Sequence'
      ? node[1][1]?.[0]
      : node[1];
  } else if (tag === 'Decl.decl_node.Ddata') {
    symbol = node[1]?.[1]?.[0]?.[1]?.[0];
  } else if (tag === 'Decl.decl_node.Dparam') {
    symbol = node[1];
  } else if (tag === 'Decl.decl_node.Dlogic') {
    symbol = node[1]?.[1]?.[0]?.[1]?.[0];
  } else if (tag === 'Decl.decl_node.Dind') {
    symbol = node[1]?.[1]?.[1]?.[1]?.[0]?.[1]?.[0];
  } else if (tag === 'Decl.decl_node.Dprop') {
    symbol = node[1]?.[1]?.[1];
  }
  return `${tag ?? 'Decl'} ${canonicalSymbolName(definitions, symbol)}`;
}

function canonicalTheoryName(definitions, reference) {
  const value = canonicalReferenceValue(definitions, reference);
  if (!Array.isArray(value) || value[0] !== 'Theory.theory') {
    return '<theory>';
  }
  return canonicalIdentifierName(definitions, value[1]);
}

function canonicalNamedDefinitions(graph, kind) {
  const definitions = canonicalDefinitionMap(graph);
  const names = [];
  for (const key of definitions.keys()) {
    const [definitionKind, rawIndex] = key.split(':');
    if (definitionKind !== kind) continue;
    names.push(
      canonicalSymbolName(
        definitions,
        ['Reference', definitionKind, Number(rawIndex)],
      ),
    );
  }
  names.sort();
  return names;
}

function multisetDifference(left, right) {
  const remaining = new Map();
  for (const value of right) {
    remaining.set(value, (remaining.get(value) ?? 0) + 1);
  }
  const difference = [];
  for (const value of left) {
    const count = remaining.get(value) ?? 0;
    if (count === 0) difference.push(value);
    else remaining.set(value, count - 1);
  }
  return difference;
}

function rootTheoryDeclarationSummaries(graph) {
  const definitions = canonicalDefinitionMap(graph);
  const root = graph?.[1]?.[0];
  let theory = canonicalReferenceValue(definitions, root);
  if (Array.isArray(theory) && theory[0] === 'Pmodule.pmodule') {
    theory = canonicalReferenceValue(definitions, theory[1]);
  }
  const declarations = theory?.[3]?.[1];
  if (!Array.isArray(theory) || theory[0] !== 'Theory.theory' ||
      !Array.isArray(declarations)) {
    return null;
  }
  return declarations.map((reference, ordinal) => {
    const value = canonicalReferenceValue(definitions, reference);
    const node = value?.[1];
    let summary = '<unknown>';
    if (node?.[0] === 'Theory.tdecl_node.Use') {
      summary = `Use ${canonicalTheoryName(definitions, node[1])}`;
    } else if (node?.[0] === 'Theory.tdecl_node.Clone') {
      summary = `Clone ${canonicalTheoryName(
        definitions,
        node[1]?.[1]?.[0],
      )}`;
    } else if (node?.[0] === 'Theory.tdecl_node.Meta') {
      summary = `Meta ${canonicalHexText(node[1]?.[1]?.[0]?.[1])}`;
    } else if (node?.[0] === 'Theory.tdecl_node.Decl') {
      summary = canonicalDeclarationSummary(definitions, node[1]);
    }
    return `${ordinal}:${reference?.[2] ?? '?'}:${summary}`;
  });
}

function describeDifference(label, difference) {
  if (difference === null) return `; ${label} payloads are equal`;
  const contexts = (difference.contexts ?? []).slice(0, 5)
    .map((context, index) =>
      `; ${label} ancestor ${index} target ` +
      `${diagnosticValue(context.target)}, reference ` +
      `${diagnosticValue(context.reference)}`)
    .join('');
  return (
    `; ${label} divergence at ${difference.path}: target ` +
    `${diagnosticValue(difference.target)}, reference ` +
    `${diagnosticValue(difference.reference)}${contexts}`
  );
}

function describeCanonicalDifference(target, reference) {
  if (target.canonicalText === null || reference.canonicalText === null) {
    return '';
  }
  try {
    const targetCanonical = JSON.parse(target.canonicalText);
    const referenceCanonical = JSON.parse(reference.canonicalText);
    const difference = firstJsonDifference(
      targetCanonical,
      referenceCanonical,
    );
    const neutralDifference = firstJsonDifference(
      targetCanonical,
      referenceCanonical,
      '$',
      true,
    );
    const targetPropositions = canonicalNamedDefinitions(
      targetCanonical,
      'proposition-symbol',
    );
    const referencePropositions = canonicalNamedDefinitions(
      referenceCanonical,
      'proposition-symbol',
    );
    return (
      describeDifference('canonical', difference) +
      `; target definition inventory ` +
      `${diagnosticValue(definitionInventory(targetCanonical))}, reference ` +
      `${diagnosticValue(definitionInventory(referenceCanonical))}` +
      `; target root declarations ` +
      `${diagnosticValue(
        rootTheoryDeclarationSummaries(targetCanonical),
        4096,
      )}, ` +
      `reference ${diagnosticValue(
        rootTheoryDeclarationSummaries(referenceCanonical),
        4096,
      )}` +
      `; target-only propositions ` +
      `${diagnosticValue(multisetDifference(
        targetPropositions,
        referencePropositions,
      ), 4096)}, reference-only propositions ` +
      `${diagnosticValue(multisetDifference(
        referencePropositions,
        targetPropositions,
      ), 4096)}` +
      describeDifference('identity-neutral', neutralDifference)
    );
  } catch (error) {
    return `; canonical diagnostic failed: ${error.message}`;
  }
}

function addCounts(total, current) {
  for (const key of Object.keys(total)) total[key] += current[key];
}

export async function checkUpstreamSemantics({
  runtime,
  inventory,
  contract,
  entries = null,
  concurrency = 2,
  buildProduct = true,
  typedOnly = false,
  debugProduct = false,
  timeoutMs = 30 * 60 * 1000,
}) {
  const selected = entries ?? contract.entries.filter(entry => entry.accepted);
  const inventoryByPath = new Map(
    inventory.entries.map(entry => [entry.path, entry]),
  );
  const semantic = readJson(SEMANTIC_PROFILE);
  const diagnostic = readJson(DIAGNOSTIC_CONTRACT);
  const z3 = readJson(Z3_PROFILE);
  const profiles = {
    semantic: semantic.semanticProfileSha256,
    diagnostic: diagnostic.diagnosticContractSha256,
    monomorphic: z3.tracePatch.checkpointSequences.monomorphic,
    polymorphic: z3.tracePatch.checkpointSequences.polymorphic,
  };
  const product = debugProduct ? DEBUG_PRODUCT : PRODUCT;
  if (buildProduct) {
    const buildArguments = [
      'build',
      '--target',
      'native',
      'cmd/elab_canonical',
    ];
    if (!debugProduct) buildArguments.splice(3, 0, '--release');
    runChecked('moon', buildArguments);
  }
  const buildDirectory = mkdtempSync(
    join(tmpdir(), 'why3-upstream-semantics-'),
  );
  try {
    const reference = compileReference(buildDirectory, runtime);
    const referenceEnv = referenceRuntimeEnvironment(runtime);
    const results = await mapConcurrent(
      selected,
      concurrency,
      async contractEntry => {
        const entry = inventoryByPath.get(contractEntry.path);
        if (entry === undefined) {
          fail(`upstream inventory has no ${contractEntry.path}`);
        }
        const [targetRecords, referenceRecords] = await Promise.all([
          collectCanonicalRecords(product, [
            '--stage',
            typedOnly ? 'typed-semantic' : 'upstream-semantics',
            '--fixture',
            entry.path,
            '--file',
            entry.absolutePath,
            '-L',
            dirname(entry.absolutePath),
          ], {
            label: `target ${entry.path}`,
            env: { ...process.env, LC_ALL: 'C', LANG: 'C' },
            captureRecords: debugProduct ? 256 : typedOnly ? 16 : 1,
            timeoutMs,
          }),
          collectCanonicalRecords(reference, [
            '--why3-root',
            runtime.sourceRoot,
            '--fixture',
            entry.path,
            '--file',
            entry.absolutePath,
            ...(typedOnly ? ['--typed-only'] : []),
          ], {
            label: `reference ${entry.path}`,
            env: referenceEnv,
            captureRecords: debugProduct ? 256 : typedOnly ? 16 : 1,
            timeoutMs,
          }),
        ]);
        const targetCounts = validateSemanticRecords(
          targetRecords,
          contractEntry,
          profiles,
          'target',
        );
        const referenceCounts = validateSemanticRecords(
          referenceRecords,
          contractEntry,
          profiles,
          'reference',
        );
        compareSemanticRecords(targetRecords, referenceRecords, contractEntry);
        if (JSON.stringify(targetCounts) !== JSON.stringify(referenceCounts)) {
          fail(`${entry.path}: target/reference semantic coverage differs`);
        }
        return targetCounts;
      },
      { label: 'upstream-semantics', progressEvery: 10 },
    );
    const totals = {
      typedUnits: 0,
      rawTasks: 0,
      transformCheckpoints: 0,
      preparedTasks: 0,
      smtTokens: 0,
      canonicalBytes: 0,
    };
    for (const result of results) addCounts(totals, result);
    process.stdout.write(
      `upstream semantic corpus: ${selected.length}/${selected.length} ` +
      `accepted files exact; ${totals.typedUnits} typed units, ` +
      `${totals.rawTasks} raw tasks, ` +
      `${totals.transformCheckpoints} transform checkpoints, ` +
      `${totals.preparedTasks} prepared tasks, ` +
      `${totals.smtTokens} SMT token streams\n`,
    );
    return { files: selected.length, ...totals };
  } finally {
    rmSync(buildDirectory, { recursive: true, force: true });
  }
}

function requiredValue(argv, index, option) {
  const value = argv[index + 1];
  if (value === undefined || value.startsWith('--')) {
    fail(`${option} requires a value`);
  }
  return value;
}

export function parseSemanticArguments(argv) {
  const result = {
    why3Root: null,
    why3Archive: null,
    contract: DEFAULT_CONTRACT,
    paths: [],
    concurrency: 2,
    typedOnly: false,
    debugProduct: false,
    timeoutMs: 30 * 60 * 1000,
  };
  for (let index = 0; index < argv.length; index += 1) {
    const option = argv[index];
    if (option === '--typed-only') {
      result.typedOnly = true;
      continue;
    }
    if (option === '--debug-product') {
      result.debugProduct = true;
      continue;
    }
    const value = requiredValue(argv, index, option);
    if (option === '--why3-root') result.why3Root = resolve(value);
    else if (option === '--why3-archive') result.why3Archive = resolve(value);
    else if (option === '--contract') result.contract = resolve(value);
    else if (option === '--path') result.paths.push(value);
    else if (option === '--concurrency') {
      result.concurrency = Number(value);
      if (!Number.isInteger(result.concurrency) || result.concurrency < 1) {
        fail('--concurrency must be a positive integer');
      }
    } else if (option === '--timeout-minutes') {
      const minutes = Number(value);
      if (!Number.isInteger(minutes) || minutes < 1) {
        fail('--timeout-minutes must be a positive integer');
      }
      result.timeoutMs = minutes * 60 * 1000;
    } else {
      fail(`unknown argument ${option}`);
    }
    index += 1;
  }
  if (result.why3Root !== null && result.why3Archive !== null) {
    fail('--why3-root and --why3-archive are mutually exclusive');
  }
  return result;
}

export async function main(argv = process.argv.slice(2)) {
  const options = parseSemanticArguments(argv);
  const contract = validateUpstreamCorpusContract(readJson(options.contract));
  const runtime = prepareReferenceRuntime(options);
  const corpusRoot = options.why3Root ?? join(
    PROJECT_ROOT,
    'fixtures',
    'why3-1.7.2',
  );
  const inventory = collectUpstreamCorpus(corpusRoot);
  compareInventoryToContract(inventory, contract);
  const entryByPath = new Map(
    contract.entries.map(entry => [entry.path, entry]),
  );
  const entries = options.paths.length === 0
    ? null
    : options.paths.map(path => {
      const entry = entryByPath.get(path);
      if (entry === undefined) fail(`contract has no ${path}`);
      if (!entry.accepted) fail(`${path} is not an accepted corpus entry`);
      return entry;
    });
  return checkUpstreamSemantics({
    runtime,
    inventory,
    contract,
    entries,
    concurrency: options.concurrency,
    typedOnly: options.typedOnly,
    debugProduct: options.debugProduct,
    timeoutMs: options.timeoutMs,
  });
}

const isMain = process.argv[1] !== undefined &&
  pathToFileURL(resolve(process.argv[1])).href === import.meta.url;

if (isMain) {
  main().catch(error => {
    process.stderr.write(`check_upstream_semantics: ${error.message}\n`);
    process.exitCode = 1;
  });
}
