#!/bin/bash

# abort the script in case of errors
set -euo pipefail

# Create a fresh directory switch in ./_opam
if [ -d "_opam" ]; then
    echo "Error: \"_opam\" already exists in the current folder."
    echo "If you are re-running this script after it failed a first time,"
    echo "first wipe out any leftovers by running \"rm -rf ./_opam\""
    exit 1
fi

opam switch -y create . ocaml-base-compiler.4.14.1
eval $(opam env)

# Pin the local dependencies and install.
opam update
opam install -y coq.8.16.1
opam pin -y coq-stdpp.dev ./stdpp
opam pin -y coq-autosubst ./autosubst
opam pin -y ./iris-parametric-index
opam pin -y ./transfinite-parametric-stepindex

cd melocoton
make
