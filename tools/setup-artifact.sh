#!/bin/bash

opam switch -y create . ocaml-base-compiler.4.14.1
eval $(opam env)
opam repo add -y iris-dev git+https://gitlab.mpi-sws.org/iris/opam.git
opam update
opam install -y coq.8.16.1 coq-autosubst.dev
opam pin -y ./iris-parametric-index

cd transfinite-parametric-stepindex
make -j8
make install
cd ..

cd melocoton
make
