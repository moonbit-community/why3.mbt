// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import {
  lstatSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  readlinkSync,
  realpathSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { dirname, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
export const EXPECTED_WHY3_COMMIT = '1343338d3bb1941c0d4f134283bb0790816113c4';
export const EXPECTED_WHY3_TREE = 'f5e82693620413d7d8e3ebcba69addcb6a65f877';
export const WHY3_SOURCE_ARCHIVE = {
  url: 'https://gitlab.inria.fr/why3/why3/-/archive/1343338d3bb1941c0d4f134283bb0790816113c4/why3-1343338d3bb1941c0d4f134283bb0790816113c4.tar.gz',
  sha256: 'c7bf782933a5d8ef9e78638cbf18e480eef895dca95317ba50231f20d45e92c7',
};
const PROFILE = 'z3_487';
const ROOT_DRIVER = 'z3_487.drv';
export const PROGRAM_ROOTS = ['BuiltIn', 'Bool', 'Unit', 'int.Int', 'real.Real'];
const AUXILIARY_DRIVERS = [
  ['why3.drv', '9ac85a936a0526112fec236f1b32a0d1315422071a83f7ab52010168c0eadaed'],
  ['why3_smt.drv', '66101f2eea98ca0e772b29bcbec9f84896524e56c9bf8223044470b65ed9472a'],
];

function fail(message) {
  throw new Error(message);
}

export function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function toPosix(path) {
  return path.split(sep).join('/');
}

export function canonicalSha(value) {
  return sha256(`${JSON.stringify(value)}\n`);
}

export function compareUtf8(left, right) {
  return Buffer.compare(Buffer.from(left, 'utf8'), Buffer.from(right, 'utf8'));
}

export function runChecked(command, argv, options = {}) {
  const result = spawnSync(command, argv, {
    cwd: options.cwd ?? PROJECT_ROOT,
    encoding: options.encoding ?? 'utf8',
    env: options.env ?? process.env,
    maxBuffer: options.maxBuffer ?? 64 * 1024 * 1024,
    shell: false,
  });
  // The managed sandbox can report EPERM as side-channel metadata even when
  // the child ran and exited successfully. Status/output remain authoritative.
  if (result.status !== 0 || result.signal !== null) {
    const detail = `${result.stdout ?? ''}${result.stderr ?? ''}`.trim();
    fail(`${command} failed (${result.status ?? result.signal}): ${detail}`);
  }
  if (result.error && result.error.code !== 'EPERM') throw result.error;
  return result.stdout ?? '';
}

function parseArguments(argv) {
  let why3Root = resolve(PROJECT_ROOT, '..', 'why3');
  let why3Archive = null;
  let outputMode = 'stdout';
  let outputPath = null;
  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index];
    if (argument === '--why3-root') {
      const value = argv[index + 1];
      if (!value) fail('--why3-root requires a path');
      why3Root = resolve(value);
      index += 1;
    } else if (argument === '--why3-archive') {
      const value = argv[index + 1];
      if (!value) fail('--why3-archive requires a path');
      why3Archive = resolve(value);
      index += 1;
    } else if (argument === '--output' || argument === '--check') {
      const value = argv[index + 1];
      if (!value) fail(`${argument} requires a path`);
      if (outputMode !== 'stdout') fail('--output and --check are mutually exclusive');
      outputMode = argument.slice(2);
      outputPath = resolve(value);
      index += 1;
    } else {
      fail(`unknown argument: ${argument}`);
    }
  }
  if (why3Archive !== null && argv.includes('--why3-root')) {
    fail('--why3-root and --why3-archive are mutually exclusive');
  }
  return { why3Root, why3Archive, outputMode, outputPath };
}

// Preserve newlines and quoted strings while replacing nested OCaml comments
// with spaces. Driver declarations can then be scanned line-by-line without
// accidentally accepting disabled rules such as the commented Trigonometry
// block in z3_487.drv.
function maskComments(source, path) {
  let output = '';
  let commentDepth = 0;
  let inString = false;
  let escaped = false;
  for (let index = 0; index < source.length; index += 1) {
    const current = source[index];
    const next = source[index + 1];
    if (commentDepth > 0) {
      if (current === '(' && next === '*' && source[index + 2] !== ')') {
        commentDepth += 1;
        output += '  ';
        index += 1;
      } else if (current === '*' && next === ')') {
        commentDepth -= 1;
        output += '  ';
        index += 1;
      } else {
        output += current === '\n' ? '\n' : ' ';
      }
      continue;
    }
    if (inString) {
      output += current;
      if (escaped) {
        escaped = false;
      } else if (current === '\\') {
        escaped = true;
      } else if (current === '"') {
        inString = false;
      }
      continue;
    }
    if (current === '(' && next === '*' && source[index + 2] !== ')') {
      commentDepth = 1;
      output += '  ';
      index += 1;
    } else {
      output += current;
      if (current === '"') inString = true;
    }
  }
  if (commentDepth !== 0) fail(`unterminated comment in ${path}`);
  if (inString) fail(`unterminated string in ${path}`);
  return output;
}

function parseDriverFile(path) {
  const source = readFileSync(path, 'utf8');
  const masked = maskComments(source, path);
  const events = [];
  const patterns = [
    ['import', /^\s*import\s+"((?:[^"\\]|\\.)*)"\s*$/gmu],
    ['theory', /^\s*theory\s+([A-Za-z0-9_'.]+)\s*$/gmu],
    ['transformation', /^\s*transformation\s+"([^"\\]+)"\s*$/gmu],
  ];
  for (const [kind, pattern] of patterns) {
    for (const match of masked.matchAll(pattern)) {
      events.push({ kind, value: match[1], offset: match.index });
    }
  }
  events.sort((left, right) => left.offset - right.offset);
  return { bytes: Buffer.from(source), events };
}

function collectDriverClosure(driversDirectory) {
  const files = new Map();
  const loadOrder = [];
  const theoryRoots = [];
  const transformations = [];

  function visit(name, importer = null) {
    if (name.includes('/') || name.includes('\\') || name.includes('..')) {
      fail(`unsafe driver import ${JSON.stringify(name)} from ${importer}`);
    }
    if (files.has(name)) return;
    const absolutePath = join(driversDirectory, name);
    const parsed = parseDriverFile(absolutePath);
    const imports = parsed.events
      .filter(event => event.kind === 'import')
      .map(event => event.value);
    const theories = parsed.events
      .filter(event => event.kind === 'theory')
      .map(event => event.value);
    const fileTransforms = parsed.events
      .filter(event => event.kind === 'transformation')
      .map(event => event.value);
    files.set(name, {
      path: name,
      sha256: sha256(parsed.bytes),
      imports,
      theories,
      transformations: fileTransforms,
    });
    loadOrder.push(name);
    for (const event of parsed.events) {
      if (event.kind === 'import') visit(event.value, name);
      if (event.kind === 'theory') theoryRoots.push(event.value);
      if (event.kind === 'transformation') transformations.push(event.value);
    }
  }

  visit(ROOT_DRIVER);
  return {
    files: [...files.values()].sort((left, right) =>
      compareUtf8(left.path, right.path)),
    loadOrder,
    theoryRoots: [...new Set(theoryRoots)],
    transformations,
  };
}

function treeInventory(root) {
  const entries = [];
  function visit(directory) {
    const children = readdirSync(directory, { withFileTypes: true });
    children.sort((left, right) => compareUtf8(left.name, right.name));
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
        const mode = lstatSync(absolutePath).mode;
        fail(`unsupported stdlib entry ${path} (mode ${mode})`);
      }
    }
  }
  visit(root);
  return { entries, sha256: canonicalSha(entries) };
}

function parseSemanticRecords(output) {
  const records = [];
  for (const line of output.trim().split('\n')) {
    if (line === '') continue;
    const fields = line.split('\t');
    const kind = fields[0];
    if (kind === 'theory') {
      records.push({ kind, key: fields[1] });
    } else if (kind === 'theory-item') {
      const record = {
        kind,
        theory: fields[1],
        ordinal: Number(fields[2]),
        node: fields[3],
      };
      if (record.node === 'Use' || record.node === 'Clone') {
        record.target = fields[4];
      } else if (record.node === 'Meta') {
        record.meta = fields[4];
        record.argCount = Number(fields[5]);
      }
      records.push(record);
    } else if (kind === 'module') {
      records.push({ kind, key: fields[1], pureTheory: fields[2] });
    } else if (kind === 'module-item') {
      const record = {
        kind,
        module: fields[1],
        ordinalPath: fields[2].split('.').map(Number),
        node: fields[3],
      };
      if (record.node === 'Uuse' || record.node === 'Uclone') {
        record.target = fields[4];
      } else if (record.node === 'Umeta') {
        record.meta = fields[4];
        record.argCount = Number(fields[5]);
      } else if (record.node === 'Uscope') {
        record.name = fields[4];
        record.itemCount = Number(fields[5]);
      }
      records.push(record);
    } else if (kind === 'variant') {
      records.push({ kind, category: fields[1], variant: fields[2] });
    } else {
      fail(`unknown semantic inventory record: ${line}`);
    }
  }
  records.sort((left, right) => compareUtf8(JSON.stringify(left), JSON.stringify(right)));
  return records;
}

function exportSemanticInventory(why3Root, theoryRoots) {
  const buildDirectory = mkdtempSync(join(tmpdir(), 'why3-semantic-inventory-'));
  const executable = join(buildDirectory, 'export-semantic-inventory');
  const source = join(buildDirectory, 'export_semantic_inventory.ml');
  try {
    writeFileSync(source, readFileSync(
      join(SCRIPT_DIRECTORY, 'export_semantic_inventory.ml'),
    ));
    runChecked('ocamlfind', [
      'ocamlopt',
      '-linkpkg',
      '-package',
      'why3',
      '-o',
      executable,
      source,
    ], { cwd: buildDirectory });
    const semanticArgs = ['--stdlib', join(why3Root, 'stdlib')];
    for (const theory of theoryRoots) semanticArgs.push('--theory', theory);
    for (const pmodule of PROGRAM_ROOTS) semanticArgs.push('--module', pmodule);
    return parseSemanticRecords(runChecked(executable, semanticArgs, {
      cwd: PROJECT_ROOT,
      encoding: 'utf8',
      env: { ...process.env, LC_ALL: 'C' },
      maxBuffer: 64 * 1024 * 1024,
    }));
  } finally {
    rmSync(buildDirectory, { recursive: true, force: true });
  }
}

function observedVariants(records) {
  const values = kind => [...new Set(records
    .filter(record => record.kind === kind)
    .map(record => record.node))].sort(compareUtf8);
  const declarations = [...new Set(records
    .filter(record => record.kind === 'theory-item' &&
      record.node.startsWith('D'))
    .map(record => record.node.split(':')[0]))].sort(compareUtf8);
  const typeDefinitions = [...new Set(records
    .filter(record => record.kind === 'theory-item' &&
      record.node.startsWith('Dtype:'))
    .map(record => record.node.slice('Dtype:'.length)))].sort(compareUtf8);
  const semanticNodes = {};
  for (const record of records.filter(record => record.kind === 'variant')) {
    semanticNodes[record.category] ??= [];
    semanticNodes[record.category].push(record.variant);
  }
  for (const variants of Object.values(semanticNodes)) variants.sort(compareUtf8);
  return {
    theoryItems: values('theory-item'),
    declarations,
    typeDefinitions,
    moduleItems: values('module-item'),
    programDeclarations: semanticNodes['program-declaration'] ?? [],
    semanticNodes,
  };
}

function auxiliaryDriverInventory(driversDirectory) {
  return AUXILIARY_DRIVERS.map(([path, expectedSha256]) => {
    const actualSha256 = sha256(readFileSync(join(driversDirectory, path)));
    if (actualSha256 !== expectedSha256) {
      fail(`${path} hash drift: expected ${expectedSha256}, got ${actualSha256}`);
    }
    return { path, sha256: actualSha256 };
  });
}

function why3ShapeVersion(why3Root) {
  const source = readFileSync(join(why3Root, 'src', 'session', 'termcode.ml'), 'utf8');
  const match = source.match(/^let current_sum_shape_version = SV([0-9]+)\s*$/mu);
  if (!match) fail('cannot read Why3 current shape version');
  const version = Number(match[1]);
  if (version !== 6) fail(`expected Why3 shape version 6, got ${version}`);
  return version;
}

export function buildInventory(why3Root, options = {}) {
  const realRoot = realpathSync(why3Root);
  const commit = options.archiveVerified
    ? EXPECTED_WHY3_COMMIT
    : runChecked('git', ['-C', realRoot, 'rev-parse', 'HEAD']).trim();
  if (commit !== EXPECTED_WHY3_COMMIT) {
    fail(`expected Why3 ${EXPECTED_WHY3_COMMIT}, got ${commit}`);
  }
  const tree = options.archiveVerified
    ? EXPECTED_WHY3_TREE
    : runChecked('git', ['-C', realRoot, 'rev-parse', 'HEAD^{tree}']).trim();
  if (tree !== EXPECTED_WHY3_TREE) {
    fail(`expected Why3 tree ${EXPECTED_WHY3_TREE}, got ${tree}`);
  }
  const driversDirectory = join(realRoot, 'drivers');
  const driver = collectDriverClosure(driversDirectory);
  const semanticRecords = exportSemanticInventory(realRoot, driver.theoryRoots);
  const semanticSnapshot = {
    userVisibleProgramRoots: PROGRAM_ROOTS,
    theories: semanticRecords.filter(record => record.kind === 'theory')
      .map(record => record.key).sort(compareUtf8),
    modules: semanticRecords.filter(record => record.kind === 'module')
      .map(record => record.key).sort(compareUtf8),
    records: semanticRecords,
    observedVariants: observedVariants(semanticRecords),
    stdlibTree: treeInventory(join(realRoot, 'stdlib')),
  };
  semanticSnapshot.sha256 = canonicalSha({
    userVisibleProgramRoots: semanticSnapshot.userVisibleProgramRoots,
    theories: semanticSnapshot.theories,
    modules: semanticSnapshot.modules,
    records: semanticSnapshot.records,
    observedVariants: semanticSnapshot.observedVariants,
    stdlibTreeSha256: semanticSnapshot.stdlibTree.sha256,
  });
  const driverSection = {
    profile: PROFILE,
    root: ROOT_DRIVER,
    files: driver.files,
    loadOrder: driver.loadOrder,
    theoryRoots: driver.theoryRoots,
    transformations: driver.transformations,
  };
  driverSection.sha256 = canonicalSha(driverSection);
  const detectionPath = join(realRoot, 'share', 'provers-detection-data.conf');
  return {
    schemaVersion: 1,
    why3: {
      version: '1.7.2',
      commit,
      tree,
      shapeVersion: why3ShapeVersion(realRoot),
      sourceArchive: WHY3_SOURCE_ARCHIVE,
    },
    driver: driverSection,
    auxiliaryDrivers: auxiliaryDriverInventory(driversDirectory),
    semanticSnapshot,
    proverDetection: {
      path: 'share/provers-detection-data.conf',
      sha256: sha256(readFileSync(detectionPath)),
    },
  };
}

export function buildInventoryFromArchive(archive) {
  const actualSha256 = sha256(readFileSync(archive));
  if (actualSha256 !== WHY3_SOURCE_ARCHIVE.sha256) {
    fail(`Why3 source archive hash drift: expected ${WHY3_SOURCE_ARCHIVE.sha256}, got ${actualSha256}`);
  }
  const temporary = mkdtempSync(join(tmpdir(), 'why3-source-'));
  try {
    runChecked('tar', ['-xzf', archive, '-C', temporary], { cwd: temporary });
    const root = join(temporary, `why3-${EXPECTED_WHY3_COMMIT}`);
    return buildInventory(root, { archiveVerified: true });
  } finally {
    rmSync(temporary, { recursive: true, force: true });
  }
}

export function main(argv = process.argv.slice(2)) {
  const {
    why3Root,
    why3Archive,
    outputMode,
    outputPath,
  } = parseArguments(argv);
  try {
    const inventory = why3Archive === null
      ? buildInventory(why3Root)
      : buildInventoryFromArchive(why3Archive);
    const rendered = `${JSON.stringify(inventory, null, 2)}\n`;
    if (outputMode === 'output') {
      writeFileSync(outputPath, rendered);
    } else if (outputMode === 'check') {
      if (readFileSync(outputPath, 'utf8') !== rendered) {
        fail(`${outputPath} does not match the generated driver inventory`);
      }
    } else {
      process.stdout.write(rendered);
    }
  } catch (error) {
    process.stderr.write(`export_driver_inventory: ${error.message}\n`);
    process.exitCode = 1;
  }
}

if (process.argv[1] !== undefined &&
    resolve(process.argv[1]) === fileURLToPath(import.meta.url)) main();
