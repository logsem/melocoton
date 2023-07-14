#!/bin/bash

# abort the script in case of errors
set -euo pipefail

# Create a fresh directory swith.
opam switch -y create . ocaml-base-compiler.4.14.1
eval $(opam env)

# Pin the local dependencies and install.
opam pin add -y coq-stdpp.dev coq-stdpp
opam update
opam install -y coq.8.16.1
opam install -y coqide
opam pin -y ./iris-parametric-index
opam pin -y ./transfinite-parametric-stepindex
opam pin -y coq-autosubst ./autosubst

cd melocoton
make
