import assert from 'node:assert/strict';
import {
  mkdtempSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import test from 'node:test';

const cwd = process.cwd();

function runPprintWhymlSexp(executable, path) {
  const argv = [];
  if (path !== undefined) argv.push(path);
  return spawnSync(executable, argv, {
    cwd,
    encoding: 'utf8',
    shell: false,
  });
}

test('pprint_whyml_sexp process protocol is stdout-clean and deterministic', () => {
  const build = spawnSync(
    'moon',
    ['build', '--output-json', '--target', 'native', 'cmd/pprint_whyml_sexp'],
    { cwd, encoding: 'utf8', shell: false },
  );
  assert.equal(build.status, 0, build.stderr);
  const artifact = build.stdout.trim().split('\n')
    .map(line => JSON.parse(line))
    .find(message => message.$message_type === 'artifact'
      && message.package === 'moonbit-community/why3/cmd/pprint_whyml_sexp');
  assert.ok(artifact?.path, 'build must report the executable artifact');


  const directory = mkdtempSync(join(tmpdir(), 'pprint whyml sexp '));
  try {
    const successPath = join(directory, 'fixture with spaces.mlw');
    writeFileSync(successPath, 'goal g : true\n');
    const success = runPprintWhymlSexp(artifact.path, successPath);
    assert.equal(success.status, 0, success.stderr);
    assert.equal(success.stderr, '');
    assert.match(success.stdout, /^\(Decls(?: |\n)/u);
    assert.match(success.stdout, /\)$/u);
    assert.doesNotMatch(success.stdout, /\n$/u);

    const missingArguments = runPprintWhymlSexp(artifact.path);
    assert.equal(missingArguments.status, 1);
    assert.equal(missingArguments.stdout, '');
    assert.equal(
      missingArguments.stderr,
      'pprint_whyml_sexp: expected exactly one fixture path\n',
    );

    const absent = runPprintWhymlSexp(artifact.path, join(directory, 'absent.mlw'));
    assert.equal(absent.status, 1);
    assert.equal(absent.stdout, '');
    assert.equal(absent.stderr, 'pprint_whyml_sexp: cannot read fixture\n');

    const invalidPath = join(directory, 'invalid.mlw');
    writeFileSync(invalidPath, 'goal g :\n');
    const invalid = runPprintWhymlSexp(artifact.path, invalidPath);
    assert.equal(invalid.status, 1);
    assert.equal(invalid.stdout, '');
    assert.equal(
      invalid.stderr,
      'pprint_whyml_sexp: parse error UnexpectedEof 2:0-2:0: unexpected end of input; expected lowercase identifier\n',
    );
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});
