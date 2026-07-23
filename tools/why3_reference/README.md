# Why3 reference checks

This directory contains the repository-owned half of the differential reference:
the OCaml adapters, the trace patch, curated fixtures, behavioral baselines, and
the runtime builder that connects them.

The container image is deliberately separate. `infra/reference-env/` builds an
environment containing OCaml, an unmodified Why3 1.7.2 installation, the exact
upstream Why3 source archive, Z3 4.8.12, and ordinary build tools. It does not
copy this directory or any project contract into the image.

## Environment lock

`tools/contracts/reference-environment-lock-v1.json` is the only image lock. It
contains only:

- the `linux/amd64` platform and image repository/digest;
- the OCaml base image and exact compiler version;
- the Why3 commit, tree, source archive, executable, and data directory;
- the Z3 version and executable path; and
- the hash of `/opt/reference-env/manifest.json`.

The lock intentionally does not contain workflow revisions, MoonBit versions,
project contracts, trace patches, adapters, generated files, or baselines.
Fixed-environment workflows read this one file in a small preliminary job and
feed its image reference to later jobs through `needs.environment.outputs.image`.

The `why3-image` workflow is triggered only by `infra/reference-env/**`. It
checks the three upstream components and uploads a
`reference-environment-lock-v1.json` candidate. Promotion consists only of
reviewing and replacing the checked-in environment lock.

After changing `infra/reference-env/**`, run that workflow for the branch and
promote its uploaded candidate before expecting fixed-reference jobs to pass;
the OCI digest must come from the pushed image and must never be synthesized
locally.

## Repository-owned runtime

`reference_runtime.mjs` verifies either the fixed upstream archive or an
explicit Why3 checkout, extracts a private source tree, applies
`patches/driver-trace.patch`, configures Why3, and builds only:

```text
lib/why3/why3.cmxa
lib/why3/why3.cma
```

The resulting library is exposed to adapter compilation with a temporary
`OCAMLPATH`. It is never installed and never replaces the image's global Why3.
The cache key binds the environment image digest, Why3 source identity, trace
patch, builder implementation and arguments, and OCaml version. Adapter and
fixture bytes are deliberately outside that key, so editing either does not
rebuild Why3.

The default cache lives under `_build/why3-reference-cache`. Set
`WHY3_REFERENCE_CACHE_DIR` to use a CI or external cache. A runtime becomes
visible only after its complete marker and both libraries have been built; a
partial build is never reused.

Adapter-only OCaml packages are declared in
`runtime-dependencies-v1.json`, including their exact versions. Missing or
mismatched packages are installed at runtime, so a dependency edit does not
require an image rebuild and does not change the Why3 library cache key.

## Commands

Run the complete fixed reference inside the locked image:

```sh
node tools/run.mjs reference \
  --why3-archive "$WHY3_REFERENCE_ARCHIVE"
```

This includes the full Why3 fixture corpus, project-contract regeneration,
all four differential layers, and the behavioral baseline checks.

Run one or all layered differentials with either source form:

```sh
node tools/run.mjs layers all --why3-archive /path/to/why3-source.tar.gz
node tools/run.mjs layers transform --why3-root /path/to/why3
```

`run-fixed` is the fixture-scoped entrypoint for the pristine installed Why3.
It verifies the environment manifest, source archive, driver closure, standard
library, loadpath profile, and fixture identity before running Why3. Image and
runtime provenance is written to stderr and `resolved_context.json`; it is not
part of any baseline.

```sh
tools/why3_reference/run-fixed mvp.abs -- \
  prove --parse-only tools/why3_reference/fixtures/mvp.mlw
```

Behavioral baselines use an explicit candidate/promote split:

```sh
node tools/run.mjs baselines check

node tools/run.mjs baselines candidate \
  --records /tmp/reference-records \
  --result /tmp/prover-result.json \
  --compare

node tools/run.mjs baselines promote \
  --records /tmp/reference-records \
  --result /tmp/prover-result.json
```

Structural records contain only portable canonical behavior. The prover result
baseline contains the corpus identity, comparison target, normalized answers,
and its self-hash. Candidate generation and promotion never read or modify the
environment lock.
