# syntax=docker/dockerfile:1.7.0@sha256:dbbd5e059e8a07ff7ea6233b213b36aa516b4c53c645f1817a4dd18b83cbea56

# linux/amd64 manifest resolved 2026-07-21. The reference environment
# intentionally supports no other platform.
FROM ocaml/opam:ubuntu-24.04-ocaml-4.14@sha256:bea12da0ea6d56cbaa254dd8bbfe010eebf4d6e315accd8ee2f397daad655bc6

ARG OCAML_VERSION=4.14.2
ARG WHY3_VERSION=1.7.2
ARG WHY3_COMMIT=1343338d3bb1941c0d4f134283bb0790816113c4
ARG WHY3_TREE=f5e82693620413d7d8e3ebcba69addcb6a65f877
ARG WHY3_SOURCE_ARCHIVE_SHA256=c7bf782933a5d8ef9e78638cbf18e480eef895dca95317ba50231f20d45e92c7
ARG Z3_VERSION=4.8.12
ARG Z3_ARCHIVE_SHA256=648e8a7afb57445440ad711b733bd675e3888da2767c14ae5122582c924d8d52
ARG REFERENCE_MANIFEST_SHA256=775cad862f08b4c2cb0b54f2dbda73336a87306277ffce4910122eab3dd6a109

LABEL org.opencontainers.image.source="https://github.com/moonbit-community/why3.mbt" \
      org.opencontainers.image.title="why3.mbt reference environment" \
      org.opencontainers.image.description="Unmodified Why3 ${WHY3_VERSION} and Z3 ${Z3_VERSION}" \
      org.opencontainers.image.vendor="moonbit-community" \
      org.opencontainers.image.licenses="LGPL-2.1-only WITH OCaml-LGPL-linking-exception" \
      org.moonbit.why3.commit="${WHY3_COMMIT}" \
      org.moonbit.z3.version="${Z3_VERSION}"

USER root

RUN apt-get update \
    && apt-get install --yes --no-install-recommends \
      autoconf \
      build-essential \
      ca-certificates \
      curl \
      git \
      jq \
      nodejs \
      patch \
      unzip \
      xz-utils \
    && rm -rf /var/lib/apt/lists/*

RUN set -eux; \
    z3_archive=/tmp/z3-4.8.12-x64-glibc-2.31.zip; \
    curl --fail --location --retry 3 \
      https://github.com/Z3Prover/z3/releases/download/z3-4.8.12/z3-4.8.12-x64-glibc-2.31.zip \
      --output "$z3_archive"; \
    printf '%s  %s\n' "$Z3_ARCHIVE_SHA256" "$z3_archive" | sha256sum --check --strict; \
    unzip -q "$z3_archive" -d /tmp/z3-dist; \
    install -D -m 0755 \
      /tmp/z3-dist/z3-4.8.12-x64-glibc-2.31/bin/z3 \
      /opt/z3/bin/z3; \
    rm -rf "$z3_archive" /tmp/z3-dist

RUN set -eux; \
    install -d -o opam -g opam /opt/reference-env; \
    why3_archive=/opt/reference-env/why3-source.tar.gz; \
    curl --fail --location --retry 3 \
      "https://gitlab.inria.fr/why3/why3/-/archive/${WHY3_COMMIT}/why3-${WHY3_COMMIT}.tar.gz" \
      --output "$why3_archive"; \
    printf '%s  %s\n' "$WHY3_SOURCE_ARCHIVE_SHA256" "$why3_archive" \
      | sha256sum --check --strict; \
    chown opam:opam "$why3_archive"

USER opam

RUN set -eux; \
    opam install --yes menhir num ocamlfind; \
    build_root=/home/opam/why3-reference-build; \
    mkdir "$build_root"; \
    tar -xzf /opt/reference-env/why3-source.tar.gz \
      --strip-components=1 \
      -C "$build_root"; \
    cd "$build_root"; \
    ./autogen.sh; \
    ./configure \
      --prefix=/home/opam/.opam/4.14 \
      --disable-frama-c \
      --disable-coq-libs \
      --disable-js-of-ocaml \
      --disable-re \
      --enable-ocamlfind \
      --disable-zarith \
      --disable-mpfr \
      --disable-zip \
      --disable-hypothesis-selection \
      --disable-stackify \
      --disable-ide; \
    make -j4 all byte; \
    make install install-lib; \
    cd /home/opam; \
    rm -rf "$build_root"

USER root

RUN set -eux; \
    export OCAML_VERSION WHY3_VERSION WHY3_COMMIT WHY3_TREE \
      WHY3_SOURCE_ARCHIVE_SHA256 Z3_VERSION; \
    node -e 'const fs = require("node:fs"); const manifest = { schemaVersion: 1, ocaml: { version: process.env.OCAML_VERSION, runtime: { compiler: "/home/opam/.opam/4.14/bin/ocamlc", findlib: "/home/opam/.opam/4.14/bin/ocamlfind" } }, why3: { version: process.env.WHY3_VERSION, commit: process.env.WHY3_COMMIT, tree: process.env.WHY3_TREE, archive: { path: "/opt/reference-env/why3-source.tar.gz", sha256: process.env.WHY3_SOURCE_ARCHIVE_SHA256 }, runtime: { executable: "/home/opam/.opam/4.14/bin/why3", datadir: "/home/opam/.opam/4.14/share/why3" } }, z3: { version: process.env.Z3_VERSION, runtime: { executable: "/opt/z3/bin/z3" } } }; fs.writeFileSync("/opt/reference-env/manifest.json", JSON.stringify(manifest, null, 2) + "\n");'

RUN set -eux; \
    printf '%s  %s\n' "$REFERENCE_MANIFEST_SHA256" /opt/reference-env/manifest.json \
      | sha256sum --check --strict; \
    test "$(/home/opam/.opam/4.14/bin/ocamlc -version)" = "$OCAML_VERSION"; \
    test "$(/home/opam/.opam/4.14/bin/why3 --version)" = "Why3 platform, version ${WHY3_VERSION}"; \
    test "$(/opt/z3/bin/z3 --version)" = "Z3 version ${Z3_VERSION} - 64 bit"; \
    test "$(/home/opam/.opam/4.14/bin/why3 --print-datadir)" = /home/opam/.opam/4.14/share/why3; \
    /home/opam/.opam/4.14/bin/ocamlfind query -format '%v' why3 | grep -Fx "$WHY3_VERSION"

ENV PATH="/opt/z3/bin:/home/opam/.opam/4.14/bin:${PATH}" \
    OPAMROOT="/home/opam/.opam" \
    OPAMSWITCH="4.14" \
    WHY3_REFERENCE_ARCHIVE="/opt/reference-env/why3-source.tar.gz" \
    WHY3_REFERENCE_MANIFEST="/opt/reference-env/manifest.json" \
    LC_ALL="C" \
    LANG="C" \
    TZ="UTC"
