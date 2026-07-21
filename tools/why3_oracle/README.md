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

In CI, after `setup-moonbit` and `moon update && moon check`, use the fixed
image's retained official source archive instead:

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
The only configuration operations admitted are mutating `config detect` and
read-only `config show`; the latter is used to validate the fully expanded
driver and command because Why3 1.7.2 stores only `[partial_prover]` entries.

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

The semantic standard-library snapshot is generated directly from the pinned
Why3 source APIs. The exporter follows the complete recursive `z3_487` driver
theory closure and the `BuiltIn`, `Bool`, `Unit`, `int.Int`, and `real.Real`
program-module roots. It fails closed when it encounters a variant outside
`trusted-snapshot-schema-v1.json`.

```sh
node tools/why3_oracle/generate_snapshot.mjs \
  --why3-root ../why3 \
  --output-dir stdlib

node tools/why3_oracle/generate_snapshot.mjs \
  --why3-root ../why3 \
  --check-dir stdlib
```

CI can substitute `--why3-archive /opt/why3-reference/why3-source.tar.gz`.
The checked-in `generated_*.mbt` files contain private byte literals; product
code reconstructs the payload without reading the Why3 source, drivers, or
manifest at runtime. `snapshot-manifest-v1.json` records the exporter sources,
per-Theory and per-Pmodule hashes, symbol catalog digest, driver inventory, and
the total transform-influence closure hash.

The elaboration gate reads the exact `../why3` source tree, verifies its commit
and tree, rebuilds the OCaml adapters in a temporary directory, and compares
MoonBit with Why3 byte-for-byte at both the typed-Theory/Pmodule and raw-Task
boundaries. The complete PR inventory currently contains 18 typed units and 24
raw goals across seven explicitly named sources. It also checks the three
typing rejection diagnostics and proves that portable records are unchanged
under two different absolute fixture roots. The Why3 CLI checks disable its
installed default stdlib and use only `../why3/stdlib`.

```sh
node tools/why3_oracle/run_elab_differential.mjs
```

Inside the fixed image, use the retained source archive:

```sh
node tools/why3_oracle/run_elab_differential.mjs \
  --why3-archive "$WHY3_REFERENCE_ARCHIVE"
```

The Stage-07 transform gate applies the repository-owned read-only trace patch
only to the pinned oracle build. The patch exposes `driver-update`, every
top-level Z3 driver transformation, and the polymorphic composite substeps;
the ordinary Why3 runtime path remains unchanged. The gate rebuilds the OCaml
adapter in a temporary directory, verifies the exact source commit/tree and
patch hash, and compares every complete canonical Task emitted by the real
MoonBit pipeline. The 24 curated goals produce 408 exact checkpoint records
and 24 exact prepared tasks. It also checks that traced
`Driver.prepare_task` returns the same final Task as the untraced call.

```sh
node tools/why3_oracle/run_transform_differential.mjs \
  --why3-root ../why3
```

Inside the fixed image, use its retained source archive instead:

```sh
node tools/why3_oracle/run_transform_differential.mjs \
  --why3-archive "$WHY3_REFERENCE_ARCHIVE"
```

The Stage-08 SMT gate extends the same pinned trace patch with test-only
identifier and clone observers. The ordinary printer remains an identity
path; the exporter substitutes unique quoted markers only on its own output
formatter, then a real SMT lexer restores User/Snapshot spellings and
alpha-renumbers only identifiers whose first semantic introduction is a
traced generated stage. It compares complete normalized token streams,
asserts the reserved/generated collision fixture retains its user tokens, and
replaces the terminal `check-sat` with `exit` before asking fixed Z3 4.8.12 to
parse every raw MoonBit query without solving it. All 24 curated goal token
streams are compared in full.

```sh
node tools/why3_oracle/run_smt_differential.mjs \
  --why3-root ../why3
```

Inside the fixed image, use the retained source archive:

```sh
node tools/why3_oracle/run_smt_differential.mjs \
  --why3-archive "$WHY3_REFERENCE_ARCHIVE"
```

The result gate keeps the transport divergence explicit: upstream
Why3 runs the detected `z3_487` `%f` command, while the MoonBit runner sends
the same prepared query through Z3 `-in`. It compares only the fast,
deterministic `Valid`, `Unknown("sat")`, and `Unknown("unknown")` lane; resource
boundaries remain canned parser/controlled-child tests. The script invokes
upstream CLI operations only through `run-fixed` and passes the exact locked Z3
executable to the MoonBit CLI. It checks all 23 product/prover goals named by
the corpus, including both program closure fixtures and the false-postcondition
`must-not-be-Valid` assertion, against the checked-in full result record.

```sh
node tools/why3_oracle/run_result_differential.mjs
```

The structural PR golden contains the complete canonical JSON or normalized
token content, not only hashes: 18 typed records, 24 raw tasks, 408 transform
checkpoints, 24 prepared tasks, and 24 SMT token streams. Ordinary CI only
checks it. Candidate generation writes to a separate empty directory, repeats
generation under two absolute roots, and reports a structured hash diff;
promotion requires a separate explicit command:

```sh
node tools/why3_oracle/manage_pr_goldens.mjs --check
node tools/why3_oracle/manage_pr_goldens.mjs --candidate /tmp/why3-candidate
node tools/why3_oracle/manage_pr_goldens.mjs --promote /tmp/why3-candidate
```

The result golden follows the same candidate/promote separation inside the
fixed image:

```sh
node tools/why3_oracle/run_result_differential.mjs \
  --candidate /tmp/prover-result.json
node tools/why3_oracle/run_result_differential.mjs \
  --promote /tmp/prover-result.json
node tools/why3_oracle/sync_pr_golden_lock.mjs \
  --candidate \
  --manifest /tmp/why3-candidate/manifest.json \
  --result /tmp/prover-result.json \
  --output /tmp/toolchain-lock.json
node tools/why3_oracle/sync_pr_golden_lock.mjs \
  --promote \
  --manifest /tmp/why3-candidate/manifest.json \
  --result /tmp/prover-result.json
```

The last explicit step keeps the promoted toolchain contract atomic with both
golden files; ordinary checks run `sync_pr_golden_lock.mjs --check` and never
rewrite the lock.

Finally, the unsupported gate enumerates every `unsupported.*` corpus entry,
checks its exact stable diagnostic where parsing reached elaboration, and
asserts that neither `emit-smt` nor `prove` creates output or resolves a prover:

```sh
node tools/why3_oracle/run_unsupported_gate.mjs
```
