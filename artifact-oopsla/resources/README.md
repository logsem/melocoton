# Melocoton: supplementary material

This archive contains the Coq development for the paper "Melocoton: A Program
Logic for Verified Interoperability Between OCaml and C".

## The VM

We also ship a VM, where this script has already been run.
We encourage you to re-compile the code yourself, so that you can verify it is reproducible.

## Build instructions

Requirements: you need [opam](https://opam.ocaml.org/doc/Install.html) to be
installed on your computer (version 2.0.0 or newer), and have gone through the
initial `opam init` setup.

From the directory containing this README file, run the `build_artifact.sh`
script. This will create a new opam switch (called `melocoton`), which you
can remove afterwards with `opam switch remove melocoton`.

```
    ./build_artifact.sh
    eval $(opam env) # to use dune and Coq in the current terminal
```


**The build script** does the following automatically (which can also be done
manually):
1. It creates a new `opam` switch in the current directory (i.e., in the artifact folder)

```
opam switch -y create melocoton ocaml-base-compiler.4.14.1
opam switch melocoton
opam switch link melocoton
eval $(opam env)
```

2. It then installs the dependencies of this development: Coq, Iris, and Transfinite Iris (as a plugin to Iris),
   and Autosubst.

```
opam pin add -y coq-stdpp.dev coq-stdpp
opam update
opam install -y coq.8.16.1
opam install -y coqide
opam pin -y ./iris-parametric-index
opam pin -y ./transfinite-parametric-stepindex
opam pin -y coq-autosubst ./autosubst
```

3. Finally, it changes into the folder for the development of Melocoton, `melocoton`, and builds the development.

```
cd melocoton
make
```

## Overview
The Coq development accompanying our submission lives in the `melocoton`
subdirectory.

The other directories (`iris-parametric-index`,
`transfinite-parametric-stepindex`, `autosubst`) bundle the versions of
Transfinite Iris and Autosubst that our development uses. They are not part of
the submission.

See `melocoton/README.md` for more information about the structure of the
development and how it relates to the paper.


## Troubleshooting

- Once the artifact is build, and also when visiting the artifact from a new terminal session,
 one needs to call opam to re-setup the terminal environment. To do this, call:

```
    # From the directory containing this README
    eval $(opam env)
```


- If the setup script fails for some reason, to restart from the beginning, it
should be enough to remove the opam switch created by the script, and
launch the script again.

```
    opam switch remove melocoton
    rm _opam
    ./build_artifact.sh
```
