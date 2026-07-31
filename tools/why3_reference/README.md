# Why3 reference checks

This directory contains the repository-owned half of the differential reference:
the OCaml adapters, trace patches, curated fixtures, canonical v3 contracts,
and the runtime builder that connects them.

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
project contracts, trace patches, adapters, or generated files.
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
explicit Why3 checkout, extracts a private source tree, applies the isolated
`patches/driver-trace.patch` and `patches/full-mlw-export.patch` reference
hooks, configures Why3, and builds only:

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
mismatched packages are installed at runtime after refreshing the configured
opam repositories, so a dependency edit does not require an image rebuild and
does not change the Why3 library cache key. The aggregate `check` command
delays this validation until immediately before the adapter-backed contract and
differential checks, avoiding dependency installation until the project, smoke,
and fixture checks have passed.

## Commands

Run the complete project and fixed-reference check inside the locked image:

```sh
node tools/run.mjs check \
  --why3-archive "$WHY3_REFERENCE_ARCHIVE"
```

This includes the all-target project checks and tests, ASan and Node.js tool
tests, the full Why3 fixture corpus, project-contract regeneration, the
official upstream type corpus, and all four live differential layers.

The upstream type-corpus contract covers every `.mlw` and `.why` file under
the exact Why3 commit's `examples` and `tests` roots (446 + 58 files), while
excluding `examples_in_progress`. It records the exact source hashes and the
official Why3 accepted/rejected result for all 504 files. The target check
compares both classification and process exit code, with no language-feature
exemptions:

```sh
node tools/run.mjs upstream --why3-root /path/to/why3
```

`tools/contracts/upstream-corpus-v1.json` is regenerated and checked against
the fixed Why3 executable by the non-quick contract check.

Run one or all layered differentials with either source form:

```sh
node tools/run.mjs layers all --why3-archive /path/to/why3-source.tar.gz
node tools/run.mjs layers transform --why3-root /path/to/why3
```

The two module-interface fixtures use the official main WhyML entry rather
than the simplified `why3 pp --output=sexp` entry. Their lossless parse
envelopes (unit category, optional interface, declarations, and unit span) are
checked byte-for-byte with:

```sh
node tools/why3_reference/check_full_whyml_reference.mjs \
  --why3-root /path/to/why3
```

`run-fixed` is the fixture-scoped entrypoint for the pristine installed Why3.
It verifies the environment manifest, source archive, driver closure, standard
library, loadpath profile, and fixture identity before running Why3. Image and
runtime provenance is written to stderr and `resolved_context.json`; it is not
part of canonical behavior.

```sh
tools/why3_reference/run-fixed mvp.abs -- \
  prove --parse-only tools/why3_reference/fixtures/mvp.mlw
```
