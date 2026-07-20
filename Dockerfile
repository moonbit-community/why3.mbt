# syntax=docker/dockerfile:1.7

FROM ocaml/opam:ubuntu-24.04-ocaml-4.14

ARG WHY3_VERSION=1.7.2

LABEL org.opencontainers.image.source="https://github.com/moonbit-community/why3.mbt" \
      org.opencontainers.image.title="Why3 for why3.mbt CI" \
      org.opencontainers.image.description="Why3 ${WHY3_VERSION} with S-expression output support"

USER root

RUN apt-get update \
    && apt-get install --yes \
      build-essential \
      ca-certificates \
      curl \
      git \
      nodejs \
      unzip \
      xz-utils

USER opam

RUN opam install --yes \
      sexplib \
      ppx_deriving \
      ppx_sexp_conv \
      "why3.${WHY3_VERSION}"

ENV PATH="/home/opam/.opam/4.14/bin:${PATH}"

USER root

RUN set -eux; \
    test "$(why3 --version)" = "Why3 platform, version ${WHY3_VERSION}"; \
    printf 'theory Simple\n  goal trivial : true\nend\n' > /tmp/simple.mlw; \
    why3 pp --output=sexp /tmp/simple.mlw > /tmp/simple.sexp; \
    test -s /tmp/simple.sexp; \
    rm -f /tmp/simple.mlw /tmp/simple.sexp
