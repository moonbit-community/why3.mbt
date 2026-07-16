# Why3 1.7.2 WhyML fixtures

This directory is a verbatim snapshot of every `.mlw` entry tracked by the
Why3 repository at version 1.7.2, commit
`1343338d3bb1941c0d4f134283bb0790816113c4`.

Source: <https://gitlab.inria.fr/why3/why3>

Inventory:

- 989 tracked `.mlw` entries;
- 976 regular files (5,163,407 bytes);
- 13 relative symbolic links, preserved from upstream;
- original paths retained below `bench/`, `doc/`, `examples/`,
  `examples_in_progress/`, `src/`, `stdlib/`, and `tests/`.

With the pinned `why3 pp --output=sexp` from Why3 1.7.2, 929 entries are
accepted and 60 are rejected. Two of those rejected entries exercise the
project's intentional `module M : Interface` parser extension; the remaining
58 form the structured-error corpus. See `plan.md` for the full matrix.

The fixtures are test data, not Apache-2.0 project source. They remain under
Why3's GNU LGPL 2.1 terms and upstream special exception; the complete license
is included as [`LICENSE`](LICENSE). Keep the files byte-for-byte unchanged.
Refresh the whole snapshot from the pinned upstream commit instead of editing
individual fixtures.
