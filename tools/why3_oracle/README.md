# Fixed Why3 oracle

This directory contains the test-only Why3 1.7.2 differential-oracle
scaffolding. It is not part of the `why3.mbt` product API.

The fixed Why3 commit archive does not contain an opam package file.
`why3-1.7.2.opam` is therefore vendored byte-for-byte from the official
`ocaml/opam-repository` file at commit
`bfeb42d61bb49c607b888d38dadd2cc4c9d98358` (Git blob
`6811b48fa50e6160ed7f812696e0939a1c40bd0d`). Its SHA-256 and upstream
identity are part of `toolchain-inputs-v1.json` and are checked before build.

The checked contracts are regenerated or verified with:

```sh
node tools/check_pr00_contracts.mjs --why3-root ../why3
```

In CI, after `setup-moonbit` and `moon update && moon check`, use the fixed image's retained
official source archive instead:

```sh
node tools/check_pr00_contracts.mjs \
  --why3-archive /opt/why3-reference/why3-source.tar.gz \
  --require-toolchain-lock
```

`run-fixed` is the only supported entry point for Why3 CLI oracle commands.
It refuses to run until `tools/contracts/toolchain-lock.json` has been promoted,
all executable/datadir/driver hashes match, and
`WHY3_ORACLE_IMAGE_DIGEST` equals the lock's immutable image digest. It creates
or reuses only a provenance-marked isolated Whyconf, replaces the ambient
process environment, injects the fixed loadpaths and plugin policy, and writes
a separate `resolved_context.json` diagnostic next to that Whyconf. Existing
developer Whyconf files and broad prover selectors such as `-P z3` are rejected.

```sh
tools/why3_oracle/run-fixed mvp.abs -- \
  prove --type-only tools/why3_oracle/fixtures/mvp.mlw
```

The `why3-image` workflow emits `toolchain-report.json`, a complete
`toolchain-lock.json` candidate, and the isolated promotion validation summary
as an artifact. Before upload, it promotes into a temporary checkout and runs
the strict contract gate plus a `run-fixed` smoke test inside the just-built
digest image. Repository promotion remains a second, reviewed change. Extract
the report and lock files, then preview the exact repository changes without
writing anything:

```sh
node tools/why3_oracle/promote_toolchain_lock.mjs \
  --candidate artifact/toolchain-lock.json \
  --report artifact/toolchain-report.json
```

After reviewing the JSON summary, repeat the command with `--promote`. The
promotion command reproduces the candidate from the report, checks every
contract hash, renders the literal `repository@sha256:...` workflow reference,
sets `WHY3_ORACLE_IMAGE_DIGEST`, enables `--require-toolchain-lock`, adds a
`run-fixed` smoke test, and revalidates the result before writing. A later
toolchain replacement additionally requires `--replace-existing-lock`; this
flag can be dry-run before it is combined with `--promote`. The candidate
includes the installed Why3 shape version and Why3/Z3 executable hashes.
MoonBit is deliberately outside this image and lock: CI installs the current
stable toolchain through the full-commit-pinned `setup-moonbit` action, logs its
version, restores the exact `moon.mod` dependencies, and checks those dependency
trees against `moon-dependencies-v1.json`. Ordinary CI never updates contracts
or golden data.
