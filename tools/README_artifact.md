# Artifact for Melocoton: A Program Logic for Verified Interoperability Between OCaml and C

This is the artifact for the paper "Melocoton: A Program Logic for
Verified Interoperability Between OCaml and C". It contains a
VirtualBox virtual machine with the development already prebuilt and
manual installation instructions using opam.

## List of Claims
The main claim of this artifact is that the description in the paper corresponds
to the Coq development (modulo small simplifications for presentation purposes).
The mapping from concepts in the paper to the Coq development can be found below
under "Guide through the Coq development" and a recommendation for how to evaluate
the artifact can be found under "Evaluation instructions".

An additional claim is that Coq development only depends on the axioms
listed under "Axioms" below.

## Getting Started Guide
As part of the kick-the-tire process, we suggest that you set up the
virtual machine (as described in the next section), and that you roughly
familiarize yourself with the overall structure of our development by in
particular reading the section "Structure of the Coq development".
Additionally, we recommend you open one of the Coq files in our development,
for example `melocoton/theories/examples/swap_pair.v`, and check that
this file can properly be stepped through in CoqIde (which you can start
using the Desktop shortcut in the virtual machine).

## Browsing the development

An quick way to browse the development is to open
[melocoton/html/toc.html](melocoton/html/toc.html) in a web browser. The
webpages contains an HTML rendering of the Coq scripts of the development. They
are available both in the VM image and the `melocoton_artifact.tgz` archive.

Alternatively, one should use CoqIde (or any other IDE with Coq support) to open
the Coq files of the development.

## Installation instructions and sanity-testing
This artifact contains both the raw source-code of Melocoton
(`melocoton_artifact.tgz`) and a virtual machine containing the source-code
with all dependencies already installed (`artifact.ova`). We recommend using
the virtual machine unless you are an experienced opam user.

### Use the virtual machine (artifact.ova)
To use the virtual machine, please install
[VirtualBox](https://www.virtualbox.org/wiki/Downloads) (version 7.0.8
is tested) and open `artifact.ova`. This VM contains all necessary
dependencies of Melocoton and contains a prebuilt version of
`melocoton_artifact.tgz` in `~/Desktop/melocoton_artifact`. To check
that everything is installed correctly, please navigate with a shell
to `~/Desktop/melocoton_artifact/melocoton/` and run
```
make
```
It should output only the following, as everything is prebuilt:
```
dune build --display=short
```

The user of the VM image is "vagrant" and the password also "vagrant".
The VM comes with the VirtualBox Guest Additions installed, so the
screen size should change automatically when resizing the window. It
might be necessary to resize the window once for the automatic
resizing to kick in. To change the keyboard layout, go to
"Applications > Settings > Keyboard > Layout", add the desired variant
via "Add" and move it to the top.

The VM has coqide preinstalled in the opam switch in
`~/Desktop/melocoton_artifact/`. To open a `*.v` file in coqide, go to this
folder in the terminal and run e.g.
`coqide melocoton/theories/examples/compression/buffers_adequacy.v`.

Additionally, the Desktop shortcut can be used to open `coqide`
using the proper opam switch, then files can be opened using File -> Open.

Finally, note that the shipped VM is set to use 8GB of RAM by default.
You might want to modify the VM to decrease the amount of RAM assigned to it
(if your system does not have that much RAM).
When you do so, you also want to reduce the number of parallel compilation threads.
Thus, instead of `make`, replace the last step by `dune build --display=short -j2`
If you start the build with the full parallelism, and you get an Out of Memory error,
you can also continue it using this command (without causing a full rebuild),
as long as all dependencies have properly compiled.

### Installing the artifact locally (melocoton_artifact.tgz)
(Only tested on Linux. Likely works on MacOS. Might work on Windows using WSL.)

We also provide the sources of the artifact and a script `build-artifact.sh` to
compile them locally, as an alternative to the VM. As a prerequisite, you must
have [opam](https://opam.ocaml.org/doc/Install.html) installed on your computer.
Opam must be version 2.1.0 or newer, and you must have gone through the initial
`opam init` setup.

To build the artifact, run the following commands. Nothing will be installed or
written outside of the `melocoton_artifact` directory. The directory can be
safely removed afterwards.
```
    tar xvzf melocoton_artifact.tgz
    cd melocoton_artifact
    ./build-artifact.sh
    eval $(opam env) # to use dune and Coq in the current terminal
```

**The build script** does the following automatically (which can also be done
manually):
1. It creates a new `opam` switch in the current directory (i.e., in the artifact folder)

```
opam switch -y create . ocaml-base-compiler.4.14.1
eval $(opam env --switch=. --set-switch)
```

2. It then installs the dependencies of this development: Coq, stdpp, autosubst, Iris, and Transfinite Iris (as a plugin to Iris). 

```
opam update
opam install -y coq.8.16.1
opam pin -y coq-stdpp.dev ./stdpp
opam pin -y coq-autosubst ./autosubst
opam pin -y ./iris-parametric-index
opam pin -y ./transfinite-parametric-stepindex
```

3. Finally, it changes into the folder for the development of Melocoton, `melocoton`, and builds the development.

```
cd melocoton
make
```

### Troubleshooting

- Once the artifact is build, and also when visiting the artifact from a new terminal session,
 one needs to call opam to re-setup the terminal environment. To do this, call:
```
    # From the directory containing this README
    eval $(opam env)
```


- If the build script fails for some reason, to restart from the beginning, it
should be enough to remove the `_opam` subdirectory created by the script, and
launch the script again.
```
    rm -rf ./_opam
    ./build-artifact.sh
```


## Overview of the artifact folder

**The Coq development accompanying our submission lives in the `melocoton`
subdirectory.** It is further explained in the next section.

The other directories (`iris-parametric-index`,
`transfinite-parametric-stepindex`, `autosubst`, `stdpp`) bundle the versions of
Transfinite Iris, Autosubst and stdpp that our development uses. They are not part of
the submission.
(The development of Transfinite Iris is split into the two packages `iris-parametric-index`
and `transfinite-parametric-stepindex` due to an ongoing refactoring.)

The remaining files and folders of the directory are less relevant:
- File `build-artifact.sh` is a script used to build the artifact.
- Folder `_opam` (created during installation) contains a local installation
  of OCaml and the packages required by the artifact.
- File `generation_data.txt` tracks the git commits that were used to
  create this artifact.
- File `README.md` is, well, this file.

In the following, all paths are given relative to the `melocoton` folder
in the toplevel artifact directory.


## Evaluation instructions
To evaluate this artifact, we propose the following steps:
1. Confirm that the Coq development compiles without problems.
   To do so, run `make clean` in the `melocoton` folder if you have previously built the
   Coq development or are using the VM. Thereafter, run `make`.
2. Search for `admit` or `Admitted.` in the source code files. As you
   will see, the development does not have any admits.
3. Read the Section "Structure of the Coq development" and
   "Guide through the development following the paper" to familiarize
   yourself with structure of the Coq development in general, as well
   as the differences between the on-paper presentation and the Coq
   development.
4. Step through the Coq development (in the order outlined below)
   and compare the Theorems and Definitions with those from the paper.
   You can find the Coq files in the folder `melocoton`. To step
   through the proofs, you can use CoqIDE in the virtual machine.
   For each listed theorem, you should compare the Coq statement with
   the paper, and check that they agree (up to the differences
   listed below).
5. Check that the axioms used in the development are only the ones
   listed under "Axioms" below. Since the Axioms are actually used
   by transfinite Iris, and thus only included in our development,
   a textual search should not find any axioms. Nonetheless, you
   should conduct such a search to validate that we have not included
   any other axioms. To do so, you might want to run:
   ```
   grep Axiom $(find . -name "*.v")
   grep Admitted $(find . -name "*.v")
   ```
   (Make sure to execute this command in the `melocoton` folder, not
   the toplevel artifact folder as otherwise the command might return
   results from other packages.)
   To actually check our axioms, you can use `Print Assumptions` to show
   all axioms (and admits) used in key theorems. For example, add and
   execute `Print Assumptions buffers_adequate.` at the end of
   `melocoton/theories/examples/compression/buffers_adequacy.v`.

