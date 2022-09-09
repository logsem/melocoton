


# Installation Instructions

```
opam switch create melocoton 4.14.0
opam switch link melocoton .
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install --deps-only .
dune build
```