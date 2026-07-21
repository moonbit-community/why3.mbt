import {
  existsSync,
  readFileSync,
} from 'node:fs';
import {
  lstat,
  mkdtemp,
  open,
  readFile,
  readdir,
  readlink,
  realpath,
  rm,
  stat,
} from 'node:fs/promises';
import { availableParallelism, tmpdir } from 'node:os';
import {
  dirname,
  isAbsolute,
  join,
  relative,
  resolve,
  sep,
} from 'node:path';
import { spawn, spawnSync } from 'node:child_process';
import { fileURLToPath, pathToFileURL } from 'node:url';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..');
const FIXTURE_ROOT = join(PROJECT_ROOT, 'fixtures', 'why3-1.7.2');
const MANIFEST_PATH = join(SCRIPT_DIRECTORY, 'why3_reject_manifest.json');
const PPRINT_WHYML_SEXP_PATH = join(
  PROJECT_ROOT,
  '_build/native/debug/build/cmd/pprint_whyml_sexp/pprint_whyml_sexp.exe',
);

const EXPECTED_REGULAR = 976;
const EXPECTED_SYMLINK = 13;
const EXPECTED_TOTAL = 989;
const EXPECTED_DIFF = 929;
const EXPECTED_REJECT = 58;
const EXPECTED_EXTENSION = 2;

function fail(message) {
  throw new Error(message);
}

function toPosix(path) {
  return path.split(sep).join('/');
}

function isWithinRoot(root, target) {
  const pathFromRoot = relative(root, target);
  return pathFromRoot === '' ||
    (!pathFromRoot.startsWith(`..${sep}`) && pathFromRoot !== '..' &&
      !isAbsolute(pathFromRoot));
}

export async function enumerateFixtures(root = FIXTURE_ROOT) {
  const rootReal = await realpath(root);
  const fixtures = [];
  let regular = 0;
  let symlink = 0;

  async function visit(directory) {
    const entries = await readdir(directory, { withFileTypes: true });
    entries.sort((left, right) => left.name.localeCompare(right.name));
    for (const entry of entries) {
      const absolutePath = join(directory, entry.name);
      if (entry.isDirectory()) {
        await visit(absolutePath);
        continue;
      }
      if (!entry.name.endsWith('.mlw')) continue;
      const relativePath = toPosix(relative(root, absolutePath));
      if (entry.isFile()) {
        regular += 1;
        fixtures.push({ absolutePath, relativePath, kind: 'regular' });
        continue;
      }
      if (entry.isSymbolicLink()) {
        const linkText = await readlink(absolutePath);
        const target = await realpath(absolutePath);
        if (!isWithinRoot(rootReal, target)) {
          fail(`fixture symlink escapes root: ${relativePath} -> ${linkText}`);
        }
        if (!(await stat(target)).isFile()) {
          fail(`fixture symlink does not target a file: ${relativePath}`);
        }
        symlink += 1;
        fixtures.push({ absolutePath, relativePath, kind: 'symlink' });
        continue;
      }
      const metadata = await lstat(absolutePath);
      fail(`unsupported .mlw fixture type (${metadata.mode}): ${relativePath}`);
    }
  }

  await visit(root);
  fixtures.sort((left, right) =>
    left.relativePath.localeCompare(right.relativePath));
  return { fixtures, regular, symlink, total: fixtures.length };
}

function isIntegerArray(value, length) {
  return Array.isArray(value) && value.length === length &&
    value.every(Number.isInteger);
}

export function validateManifest(manifest, fixturePaths) {
  if (manifest.why3Version !== '1.7.2') {
    fail(`manifest Why3 version must be 1.7.2, got ${manifest.why3Version}`);
  }
  if (!manifest.entries || Array.isArray(manifest.entries) ||
    typeof manifest.entries !== 'object') {
    fail('manifest entries must be an object');
  }
  const paths = Object.keys(manifest.entries);
  if (paths.length !== EXPECTED_REJECT + EXPECTED_EXTENSION) {
    fail(`manifest must contain 60 entries, got ${paths.length}`);
  }
  const sortedPaths = [...paths].sort();
  if (JSON.stringify(paths) !== JSON.stringify(sortedPaths)) {
    fail('manifest entries must be sorted by POSIX path');
  }

  const knownFixtures = new Set(fixturePaths);
  let reject = 0;
  let extension = 0;
  for (const path of paths) {
    if (path.startsWith('/') || path.includes('\\') ||
      path.split('/').includes('..')) {
      fail(`manifest path is not a safe POSIX relative path: ${path}`);
    }
    if (!knownFixtures.has(path)) fail(`manifest fixture is missing: ${path}`);
    const entry = manifest.entries[path];
    if (entry.lane === 'reject') {
      reject += 1;
      if (typeof entry.moonbitKind !== 'string' ||
        entry.moonbitKind === 'AcceptExtension') {
        fail(`invalid MoonBit reject kind for ${path}`);
      }
      if (entry.why3Position === null) {
        if (path !== 'examples/use_api/epsilon.mlw' ||
          entry.moonbitKind !== 'UnsupportedEpsilon' ||
          !isIntegerArray(entry.moonbitPosition, 4)) {
          fail(`only epsilon may have a null Why3 position: ${path}`);
        }
      } else if (!isIntegerArray(entry.why3Position, 3)) {
        fail(`invalid Why3 position for ${path}`);
      }
    } else if (entry.lane === 'extension') {
      extension += 1;
      if (!isIntegerArray(entry.why3Position, 3) ||
        entry.moonbitKind !== 'AcceptExtension' ||
        typeof entry.structureTest !== 'string') {
        fail(`invalid extension manifest entry for ${path}`);
      }
    } else {
      fail(`unknown manifest lane for ${path}: ${entry.lane}`);
    }
  }
  if (reject !== EXPECTED_REJECT || extension !== EXPECTED_EXTENSION) {
    fail(`manifest lanes must be 58 reject / 2 extension, got ${reject} / ${extension}`);
  }
  return { reject, extension };
}

function runCapture(command, argv, options = {}) {
  return new Promise((resolveRun, rejectRun) => {
    const child = spawn(command, argv, {
      cwd: options.cwd,
      env: options.env,
      shell: false,
      stdio: ['ignore', options.stdoutFd ?? 'pipe', 'pipe'],
    });
    const stdout = [];
    const stderr = [];
    if (child.stdout) child.stdout.on('data', chunk => stdout.push(chunk));
    child.stderr.on('data', chunk => stderr.push(chunk));
    child.once('error', rejectRun);
    child.once('close', (code, signal) => {
      resolveRun({
        code,
        signal,
        stdout: Buffer.concat(stdout).toString('utf8'),
        stderr: Buffer.concat(stderr).toString('utf8'),
      });
    });
  });
}

async function runToFile(command, argv, outputPath, options = {}) {
  const output = await open(outputPath, 'w');
  try {
    return await runCapture(command, argv, { ...options, stdoutFd: output.fd });
  } finally {
    await output.close();
  }
}

function verifyWhy3Version() {
  const result = spawnSync('why3', ['--version'], {
    cwd: PROJECT_ROOT,
    encoding: 'utf8',
    shell: false,
    env: { ...process.env, LC_ALL: 'C' },
  });
  if (result.error) throw result.error;
  if (result.status !== 0) fail(`why3 --version failed: ${result.stderr}`);
  if (!/^Why3 platform, version 1\.7\.2\s*$/u.test(result.stdout)) {
    fail(`expected Why3 1.7.2, got ${result.stdout.trim()}`);
  }
}

async function buildPprintWhymlSexp() {
  const result = await runCapture(
    'moon',
    ['build', '--target', 'native', 'cmd/pprint_whyml_sexp'],
    { cwd: PROJECT_ROOT, env: process.env },
  );
  if (result.code !== 0) {
    fail(`cannot build pprint_whyml_sexp:\n${result.stdout}${result.stderr}`);
  }
  if (!existsSync(PPRINT_WHYML_SEXP_PATH)) {
    fail(`pprint_whyml_sexp is missing: ${PPRINT_WHYML_SEXP_PATH}`);
  }
}

async function checkExtensionStructure(entries) {
  for (const [path, entry] of entries) {
    const result = await runCapture(
      'moon',
      [
        'test',
        'cmd/pprint_whyml_sexp',
        '--target',
        'native',
        '--filter',
        entry.structureTest,
      ],
      { cwd: PROJECT_ROOT, env: process.env },
    );
    if (result.code !== 0) {
      fail(
        `extension structure assertion failed for ${path}:\n` +
        result.stdout + result.stderr,
      );
    }
    if (!/Total tests: 1, passed: 1, failed: 0\./u.test(result.stdout)) {
      fail(`extension structure test did not run exactly once for ${path}`);
    }
  }
}

export function parseWhy3Position(stderr) {
  const match = stderr.match(/line (\d+), characters (\d+)-(\d+):/u);
  return match ? match.slice(1).map(Number) : null;
}

export function parseMoonbitDiagnostic(stderr) {
  const match = stderr.match(
    /^pprint_whyml_sexp: parse error (\w+) (\d+):(\d+)-(\d+):(\d+): .+\n?$/u,
  );
  if (!match) return null;
  return {
    kind: match[1],
    position: match.slice(2).map(Number),
  };
}

export function sameNumbers(left, right) {
  if (left === null || right === null) return left === right;
  if (!Array.isArray(left) || !Array.isArray(right) ||
    left.length !== right.length) {
    return false;
  }
  return left.every((value, index) => value === right[index]);
}

async function compareRaw(expectedPath, actualPath, fixture) {
  const expected = await readFile(expectedPath);
  const actual = await readFile(actualPath);
  if (expected.equals(actual)) return;
  let offset = 0;
  const commonLength = Math.min(expected.length, actual.length);
  while (offset < commonLength && expected[offset] === actual[offset]) offset += 1;
  const from = Math.max(0, offset - 120);
  const toExpected = Math.min(expected.length, offset + 240);
  const toActual = Math.min(actual.length, offset + 240);
  fail(
    `sexp mismatch for ${fixture} at raw byte ${offset}\n` +
    `why3: ${JSON.stringify(expected.subarray(from, toExpected).toString())}\n` +
    `moon:  ${JSON.stringify(actual.subarray(from, toActual).toString())}`,
  );
}

async function runFixture(fixture, manifestEntry, directory, ordinal) {
  const prefix = join(directory, ordinal.toString().padStart(4, '0'));
  const why3Raw = `${prefix}.why3.raw`;
  const moonRaw = `${prefix}.moon.raw`;
  const why3 = await runToFile(
    'why3',
    ['pp', '--output=sexp', fixture.absolutePath],
    why3Raw,
    {
      cwd: PROJECT_ROOT,
      env: { ...process.env, LC_ALL: 'C' },
    },
  );

  if (manifestEntry) {
    if (why3.code === 0) {
      fail(`manifest fixture unexpectedly passed Why3: ${fixture.relativePath}`);
    }
    const why3Position = parseWhy3Position(why3.stderr);
    if (!sameNumbers(why3Position, manifestEntry.why3Position)) {
      fail(
        `Why3 position drift for ${fixture.relativePath}: expected ` +
        `${JSON.stringify(manifestEntry.why3Position)}, got ` +
        `${JSON.stringify(why3Position)}\n${why3.stderr}`,
      );
    }
    const moon = await runToFile(
      PPRINT_WHYML_SEXP_PATH,
      [fixture.absolutePath],
      moonRaw,
      { cwd: PROJECT_ROOT, env: process.env },
    );
    if (manifestEntry.lane === 'extension') {
      if (moon.code !== 0 || moon.stderr !== '') {
        fail(`MoonBit rejected extension ${fixture.relativePath}:\n${moon.stderr}`);
      }
      const output = await readFile(moonRaw, 'utf8');
      if (output.length === 0) {
        fail(`MoonBit extension projection is empty: ${fixture.relativePath}`);
      }
      return 'extension';
    }
    if (moon.code === 0) {
      fail(`MoonBit unexpectedly accepted reject fixture: ${fixture.relativePath}`);
    }
    if ((await stat(moonRaw)).size !== 0) {
      fail(`MoonBit reject polluted stdout: ${fixture.relativePath}`);
    }
    const diagnostic = parseMoonbitDiagnostic(moon.stderr);
    if (!diagnostic) {
      fail(`invalid MoonBit diagnostic for ${fixture.relativePath}: ${moon.stderr}`);
    }
    if (diagnostic.kind !== manifestEntry.moonbitKind) {
      fail(
        `MoonBit kind drift for ${fixture.relativePath}: expected ` +
        `${manifestEntry.moonbitKind}, got ${diagnostic.kind}`,
      );
    }
    const expectedMoonPosition = manifestEntry.moonbitPosition ?? [
      manifestEntry.why3Position[0],
      manifestEntry.why3Position[1],
      manifestEntry.why3Position[0],
      manifestEntry.why3Position[2],
    ];
    if (!sameNumbers(diagnostic.position, expectedMoonPosition)) {
      fail(
        `MoonBit position drift for ${fixture.relativePath}: expected ` +
        `${JSON.stringify(expectedMoonPosition)}, got ` +
        `${JSON.stringify(diagnostic.position)}`,
      );
    }
    return 'reject';
  }

  if (why3.code !== 0) {
    fail(`unmanifested Why3 rejection for ${fixture.relativePath}:\n${why3.stderr}`);
  }
  const moon = await runToFile(
    PPRINT_WHYML_SEXP_PATH,
    [fixture.absolutePath],
    moonRaw,
    { cwd: PROJECT_ROOT, env: process.env },
  );
  if (moon.code !== 0) {
    fail(`MoonBit rejected accepted fixture ${fixture.relativePath}:\n${moon.stderr}`);
  }
  if (moon.stderr !== '') {
    fail(`MoonBit polluted stderr for ${fixture.relativePath}:\n${moon.stderr}`);
  }
  await compareRaw(why3Raw, moonRaw, fixture.relativePath);
  return 'diff';
}

function workerCount() {
  const requested = process.env.WHY3_FIXTURE_JOBS;
  if (requested === undefined) return Math.max(1, Math.min(4, availableParallelism()));
  if (!/^\d+$/u.test(requested)) fail('WHY3_FIXTURE_JOBS must be an integer');
  const count = Number(requested);
  if (count < 1 || count > 8) fail('WHY3_FIXTURE_JOBS must be between 1 and 8');
  return count;
}

async function runPool(fixtures, manifest, directory) {
  const counts = { diff: 0, reject: 0, extension: 0 };
  let next = 0;
  let firstError = null;
  let completed = 0;

  async function worker() {
    while (firstError === null) {
      const ordinal = next;
      next += 1;
      if (ordinal >= fixtures.length) return;
      const fixture = fixtures[ordinal];
      try {
        const lane = await runFixture(
          fixture,
          manifest.entries[fixture.relativePath],
          directory,
          ordinal,
        );
        counts[lane] += 1;
        completed += 1;
        if (completed % 50 === 0 || completed === fixtures.length) {
          process.stdout.write(`checked ${completed}/${fixtures.length}\n`);
        }
      } catch (error) {
        firstError ??= error;
      }
    }
  }

  await Promise.all(Array.from({ length: workerCount() }, () => worker()));
  if (firstError) throw firstError;
  return counts;
}

export async function checkWhy3Fixtures() {
  verifyWhy3Version();
  const inventory = await enumerateFixtures();
  if (inventory.regular !== EXPECTED_REGULAR ||
    inventory.symlink !== EXPECTED_SYMLINK ||
    inventory.total !== EXPECTED_TOTAL) {
    fail(
      `fixture inventory drift: regular=${inventory.regular} ` +
      `symlink=${inventory.symlink} total=${inventory.total}`,
    );
  }
  process.stdout.write(
    `fixtures: regular=${inventory.regular} symlink=${inventory.symlink} ` +
    `total=${inventory.total}\n`,
  );

  const manifest = JSON.parse(readFileSync(MANIFEST_PATH, 'utf8'));
  validateManifest(manifest, inventory.fixtures.map(item => item.relativePath));
  await buildPprintWhymlSexp();
  await checkExtensionStructure(
    Object.entries(manifest.entries).filter(([, entry]) =>
      entry.lane === 'extension'),
  );

  const directory = await mkdtemp(join(tmpdir(), 'why3-parser-corpus-'));
  try {
    const counts = await runPool(inventory.fixtures, manifest, directory);
    if (counts.diff !== EXPECTED_DIFF ||
      counts.reject !== EXPECTED_REJECT ||
      counts.extension !== EXPECTED_EXTENSION) {
      fail(
        `corpus lane drift: ${counts.diff} diff / ${counts.reject} reject / ` +
        `${counts.extension} extension`,
      );
    }
    process.stdout.write(
      `corpus: ${counts.diff} diff / ${counts.reject} reject / ` +
      `${counts.extension} extension\n`,
    );
    return counts;
  } finally {
    await rm(directory, { recursive: true, force: true });
  }
}

const isMain = process.argv[1] &&
  import.meta.url === pathToFileURL(process.argv[1]).href;

if (isMain) {
  try {
    await checkWhy3Fixtures();
  } catch (error) {
    process.stderr.write(`check_whyml_parser: ${error.message}\n`);
    process.exitCode = 1;
  }
}
