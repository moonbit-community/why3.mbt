# syntax=docker/dockerfile:1.7.0@sha256:dbbd5e059e8a07ff7ea6233b213b36aa516b4c53c645f1817a4dd18b83cbea56

# linux/amd64 manifest for ocaml/opam:ubuntu-24.04-ocaml-4.14, resolved
# 2026-07-21. The oracle profile supports no other platform.
FROM ocaml/opam:ubuntu-24.04-ocaml-4.14@sha256:bea12da0ea6d56cbaa254dd8bbfe010eebf4d6e315accd8ee2f397daad655bc6

ARG WHY3_VERSION=1.7.2
ARG WHY3_COMMIT=1343338d3bb1941c0d4f134283bb0790816113c4
ARG WHY3_SOURCE_ARCHIVE_SHA256=c7bf782933a5d8ef9e78638cbf18e480eef895dca95317ba50231f20d45e92c7
ARG WHY3_TRACE_PATCH_SHA256=6c41136b7912cafe45d91e0ec6ab247839c4dfbadf947f828d6aa59fb348823f
ARG Z3_VERSION=4.8.12
ARG Z3_ARCHIVE_SHA256=648e8a7afb57445440ad711b733bd675e3888da2767c14ae5122582c924d8d52

LABEL org.opencontainers.image.source="https://github.com/moonbit-community/why3.mbt" \
      org.opencontainers.image.title="why3.mbt fixed differential oracle" \
      org.opencontainers.image.description="Why3 ${WHY3_VERSION} and Z3 ${Z3_VERSION}" \
      org.opencontainers.image.vendor="moonbit-community" \
      org.opencontainers.image.licenses="LGPL-2.1-only WITH OCaml-LGPL-linking-exception" \
      org.moonbit.why3.commit="${WHY3_COMMIT}" \
      org.moonbit.why3.trace-patch.sha256="${WHY3_TRACE_PATCH_SHA256}" \
      org.moonbit.z3.version="${Z3_VERSION}"

USER root

RUN apt-get update \
    && apt-get install --yes --no-install-recommends \
      build-essential \
      autoconf \
      ca-certificates \
      curl \
      git \
      jq \
      nodejs \
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
    printf '%s  %s\n' 350bb28360df8694db72068a26fcb779797889599f584ed3146b899a98204824 /opt/z3/bin/z3 | sha256sum --check --strict; \
    rm -rf "$z3_archive" /tmp/z3-dist

RUN set -eux; \
    mkdir -p /opt/why3-reference; \
    why3_archive=/opt/why3-reference/why3-source.tar.gz; \
    curl --fail --location --retry 3 \
      "https://gitlab.inria.fr/why3/why3/-/archive/${WHY3_COMMIT}/why3-${WHY3_COMMIT}.tar.gz" \
      --output "$why3_archive"; \
    printf '%s  %s\n' "$WHY3_SOURCE_ARCHIVE_SHA256" "$why3_archive" | sha256sum --check --strict; \
    mkdir -p /opt/why3-reference/source; \
    tar -xzf "$why3_archive" \
      --strip-components=1 \
      -C /opt/why3-reference/source

COPY tools/why3_oracle/why3-1.7.2.opam /opt/why3-reference/source/why3.opam
COPY tools/why3_oracle/patches/driver-trace.patch /opt/why3-reference/driver-trace.patch

RUN set -eux; \
    printf '%s  %s\n' \
      24d4eae07494af13d313fd9ebb82e15d565c45d250dc04d5d029a06cf0534081 \
      /opt/why3-reference/source/why3.opam \
      | sha256sum --check --strict; \
    printf '%s  %s\n' \
      "$WHY3_TRACE_PATCH_SHA256" \
      /opt/why3-reference/driver-trace.patch \
      | sha256sum --check --strict; \
    cd /opt/why3-reference/source; \
    git apply --check /opt/why3-reference/driver-trace.patch; \
    git apply /opt/why3-reference/driver-trace.patch

USER opam

RUN opam pin add --yes --no-action \
      --kind=path \
      "why3.${WHY3_VERSION}" \
      /opt/why3-reference/source \
    && opam install --yes \
      sexplib \
      ppx_deriving \
      ppx_sexp_conv \
      yojson \
      digestif \
      "why3.${WHY3_VERSION}"

ENV PATH="/opt/z3/bin:/home/opam/.opam/4.14/bin:${PATH}" \
    WHY3_REFERENCE_ARCHIVE="/opt/why3-reference/why3-source.tar.gz" \
    LC_ALL="C" \
    LANG="C" \
    TZ="UTC"

USER root

RUN set -eux; \
    test "$(why3 --version)" = "Why3 platform, version ${WHY3_VERSION}"; \
    test "$(z3 --version)" = "Z3 version ${Z3_VERSION} - 64 bit"; \
    ocamlfind query yojson digestif.ocaml; \
    why3_datadir="$(why3 --print-datadir)"; \
    printf '%s  %s\n' e9a25b112d47c672757d9e25da2da420ad8ef53f9a93f2eb7dfcc3437ebb4ff0 "$why3_datadir/drivers/z3_487.drv" | sha256sum --check --strict; \
    printf '%s  %s\n' 73687a2e3626e569f4a2bf5cb74dfd6c33c7019f8d816150538840cb4fca878a "$why3_datadir/drivers/smt-libv2.gen" | sha256sum --check --strict; \
    printf '%s  %s\n' 9ac85a936a0526112fec236f1b32a0d1315422071a83f7ab52010168c0eadaed "$why3_datadir/drivers/why3.drv" | sha256sum --check --strict; \
    printf '%s  %s\n' 66101f2eea98ca0e772b29bcbec9f84896524e56c9bf8223044470b65ed9472a "$why3_datadir/drivers/why3_smt.drv" | sha256sum --check --strict; \
    printf '%s  %s\n' 4b27f49c6d17b8c66ac2187d0405373d73c7fc2d6aed0f1ae564b1906b1cb427 "$why3_datadir/provers-detection-data.conf" | sha256sum --check --strict; \
    printf 'theory Simple\n  goal trivial : true\nend\n' > /tmp/simple.mlw; \
    why3 pp --output=sexp /tmp/simple.mlw > /tmp/simple.sexp; \
    test -s /tmp/simple.sexp; \
    rm -f /tmp/simple.mlw /tmp/simple.sexp
