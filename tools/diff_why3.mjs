import {
  createWriteStream,
  existsSync,
  statSync,
} from 'node:fs';
import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { spawn, spawnSync } from 'node:child_process';
import { pathToFileURL } from 'node:url';

function verifyWhy3Version() {
  const result = spawnSync('why3', ['--version'], {
    encoding: 'utf8',
    shell: false,
    env: { ...process.env, LC_ALL: 'C' },
  });
  if (result.error) throw result.error;
  if (result.status !== 0) {
    if (result.stderr) process.stderr.write(result.stderr);
    throw new Error('why3 --version failed');
  }
  if (!/^Why3 platform, version 1\.7\.2\s*$/u.test(result.stdout)) {
    throw new Error(`expected Why3 1.7.2, got ${result.stdout.trim()}`);
  }
}

function runToFile(command, argv, outputPath, options = {}) {
  return new Promise((resolveRun, rejectRun) => {
    const output = createWriteStream(outputPath, { flags: 'wx' });
    const child = spawn(command, argv, {
      cwd: options.cwd,
      env: options.env,
      shell: false,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    const stderr = [];
    child.stderr.on('data', chunk => stderr.push(chunk));
    child.stdout.pipe(output);
    child.once('error', rejectRun);
    output.once('error', rejectRun);
    child.once('close', code => {
      output.end(() => {
        resolveRun({
          code,
          stderr: Buffer.concat(stderr).toString('utf8'),
        });
      });
    });
  });
}

function runDiff(expectedPath, actualPath) {
  return new Promise((resolveRun, rejectRun) => {
    const child = spawn('diff', ['-u', expectedPath, actualPath], {
      shell: false,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    const stdout = [];
    const stderr = [];
    child.stdout.on('data', chunk => stdout.push(chunk));
    child.stderr.on('data', chunk => stderr.push(chunk));
    child.once('error', rejectRun);
    child.once('close', code => {
      resolveRun({
        code,
        stdout: Buffer.concat(stdout).toString('utf8'),
        stderr: Buffer.concat(stderr).toString('utf8'),
      });
    });
  });
}

export async function diffWhy3Fixture(fixture, options = {}) {
  const cwd = options.cwd ?? process.cwd();
  const fixturePath = resolve(cwd, fixture);
  if (!existsSync(fixturePath) || !statSync(fixturePath).isFile()) {
    throw new Error(`fixture is not a file: ${fixture}`);
  }
  verifyWhy3Version();

  const directory = await mkdtemp(join(tmpdir(), 'why3-parser-diff-'));
  try {
    const why3Raw = join(directory, 'why3.raw.sexp');
    const moonRaw = join(directory, 'moon.raw.sexp');

    const why3 = await runToFile(
      'why3',
      ['pp', '--output=sexp', fixturePath],
      why3Raw,
      { cwd, env: { ...process.env, LC_ALL: 'C' } },
    );
    if (why3.code !== 0) {
      if (why3.stderr) process.stderr.write(why3.stderr);
      throw new Error(`why3 pp failed with status ${why3.code}`);
    }

    const moon = await runToFile(
      'moon',
      [
        'run',
        '-q',
        '--target',
        'native',
        'cmd/pprint_whyml_sexp',
        fixturePath,
      ],
      moonRaw,
      { cwd, env: process.env },
    );
    if (moon.code !== 0) {
      if (moon.stderr) process.stderr.write(moon.stderr);
      throw new Error(`pprint_whyml_sexp failed with status ${moon.code}`);
    }

    const difference = await runDiff(why3Raw, moonRaw);
    if (difference.code === 0) return true;
    if (difference.stdout) process.stderr.write(difference.stdout);
    if (difference.stderr) process.stderr.write(difference.stderr);
    if (difference.code === 1) return false;
    throw new Error(`diff failed with status ${difference.code}`);
  } finally {
    await rm(directory, { recursive: true, force: true });
  }
}

const isMain = process.argv[1] &&
  import.meta.url === pathToFileURL(process.argv[1]).href;

if (isMain) {
  if (process.argv.length !== 3) {
    process.stderr.write('usage: node tools/diff_why3.mjs <fixture.mlw>\n');
    process.exitCode = 2;
  } else {
    try {
      const equal = await diffWhy3Fixture(process.argv[2]);
      if (!equal) process.exitCode = 1;
    } catch (error) {
      process.stderr.write(`diff_why3: ${error.message}\n`);
      process.exitCode = 1;
    }
  }
}
