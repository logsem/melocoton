#!/bin/bash

# abort the script in case of errors
set -euo

# the setup commands
opam switch -y create . ocaml-base-compiler.4.14.1
eval $(opam env)
opam repo add -y iris-dev git+https://gitlab.mpi-sws.org/iris/opam.git
opam update
opam install -y coq.8.16.1 coq-autosubst.dev
opam pin -y ./iris-parametric-index
opam pin -y ./transfinite-parametric-stepindex
opam pin -y coq-autosubst ./autosubst

cd melocoton
make
