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
To get started, read through this README.md, without following all instructions
yet. As part of the kick-the-tire process, we suggest that you set up the
virtual machine (as described in the next section), and that you roughly
familiarize yourself with the overall structure of our development by in
particular reading the section "Structure of the Coq development".
Additionally, we recommend you open one of the Coq files in our development,
for example `melocoton/theories/examples/swap_pair.v`, and check that
this file can properly be stepped through in CoqIde (which you can start
using the Desktop shortcut).

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

### Installing the artifact locally (melocoton_artifact.tgz)
(Only tested on Linux. Likely works on MacOS. Might work on Windows using WSL.)

To start using the artifact you must first install the dependencies
and also compile everything. To do this, we provide a script
`build_artifact.sh` which assumes that a suitable version of Opam
is available. To check this, you can run `opam --version`. You will
need at least version `2.1.0`. If you do not already have Opam then
follow [these instructions](https://opam.ocaml.org/doc/Install.html).

To build the artifact, run the following commands:
```bash
tar xf melocoton_artifact.tgz
cd melocoton_artifact
./build_artifact.sh
```
After the last command finishes everything has been compiled, and all
examples checked. The overall build might take an hour, depending on your
machine, so we suggest you do not do this as part of the kick-the-tire phase.

`./build_artifact.sh` creates an new opam switch in the artifact directory.
To make the Coq installation installed in this switch available,
run the following command inside the artifact directory:
```
eval $(opam env)
```
Afterwards, to test the installation, navigate to the `melocoton` folder and run
```
make
```
It should output only the following as everything is prebuilt:
```
dune build --display=short
```

## Overview of the artifact folder
The Coq development accompanying our submission lives in the `melocoton`
subdirectory. It is further explained in the next section.

The other directories (`iris-parametric-index`,
`transfinite-parametric-stepindex`, `autosubst`) bundle the versions of
Transfinite Iris and Autosubst that our development uses. They are not part of
the submission.

The remaining files and folders of the directory are less relevant:
- File `build_artifact.sh` is a script used to build the artifact.
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
   To do so, run `make clean` if you have previously built the Coq development or are using the VM.
   Thereafter, run `make`.
2. Search for `admit` or `Admitted.` in the source code files. As you
   will see, the development does not have any admits.
3. Read the Section "Structure of the Coq development" and
   "Guide through the development following the paper" to familiarize
   yourself with structure of the Coq development in general, as well
   as the differences between the on-paper presentation and the Coq
   developement.
4. Step through the Coq development and compare the Theorems and
   Definitions with those from the paper. You can find the Coq files
   in the folder `melocoton`. To step through the proofs, you can use
   CoqIDE in the virtual machine.
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
   `melocoton/theories/examples/buffers_adequacy.v`.
6. Check that the Gitlab https://github.com/logsem/melocoton
   hosting the project is publicly accessible, includes an issue
   tracker, and the code has an open source license. The commit that
   was used to generate the artifact is
   TODO.
   Additionally, you should verify that our dependencies,
   namely the in-development versions of Transfinite Iris, are public.
   These can be found at gitlab.mpi-sws.org/simonspies/iris-parametric-index
   and at https://gitlab.mpi-sws.org/simonspies/transfinite-parametric-stepindex/.


## Structure of the Coq development

The Coq development lives in the `theories/` directory.

### Languages λML and λC

- `ml_lang/`: a small OCaml-like language (λML in the paper).

- `c_interface/`: definition of C values, state and corresponding separation
  logic resources. All of the development (except for concrete examples) only
  depends on `c_interface`, not on the concrete semantics of `c_lang`.

- `c_lang/`: a small C-like language (λC in the paper). Uses types from
  `c_interface` for its values and state.

### Generic language interfaces

- `language/`: generic notion of language, with the usual relational operational
  semantics, plus external calls. Both λC and λML implement this interface.

- `mlanguage/`: a language interface similar to language but using
  multirelations for operational semantics with dual non-determinism. The
  linking and wrapper combinator instantiate this interface, and thus the final
  combined language also does.

- `lang_to_mlang/`: generic lifting of `language` semantics to `mlanguage`.

### Interoperability

- `linking/`: linking of programs; operates on `mlanguage`s
  + `linking/lang.v`: operational semantics of linking
  + `linking/weakestpre.v`: program logic and correctness of linking

- `interop/`: FFI semantics and program logic rules, as a `mlanguage`
  + `interop/basics.v`: definitions of the wrapper values, blocks, and various
    parts of its state
  + `interop/{state.v,lang.v}`: operational semantics of the wrapper
  + `interop/{basics_resources.v,gctoken.v}`: ghost state of the wrapper program logic
  + `interop/update_laws.v`: points-to update laws
  + `interop/prims_proto.v`: interfaces of the FFI primitives
  + `interop/wp_prims/*.v`: soundness proof of FFI primitives
  + `interop/wp_simulation.v`: toplevel soundness proof of the wrapper program logic
  + `interop/adequacy.v`: toplevel adequacy theorem for linked+wrapped programs

### Top-level rules

- `combined/`: definition of the combined language by composing linking and the
  wrapper; with a combined correctness theorem and adequacy proof relating to
  the operational semantics.

- `c_interop/`: Hoare triples for FFI primitives, instantiated on λC from their
  interfaces. Useful for verifying concrete examples.

### Cross-language concepts

- `language_commons.v`: definition of interfaces and operations on them
  (interfaces are called "protocols" in the development)

- `multirelations.v`: definition of multirelations for semantics with dual
  non-determinism

### Case studies

- `ml_lang/logrel`: logical relation for λML defining a semantic interpretation
  of λML types. Defined strictly on top of λML, but allows instantiating
  the semantic type of external calls with arbitrary Iris propositions.

- `examples/`: example programs leveraging the FFI

- `extra/`: Actual OCaml+C code implementing (and testing) some of the examples.

## Guide through the development following the paper

Section 2.1:

- λC (toy) implementation of the compression library functions (Fig 2): in `examples/compression/compression_proofs.v`
   + `snappy_max_compressed_length`: `buffy_max_len_code`
   + `snappy_compress`: `buffy_compress_code`.
- λML implementation of `is_compressible` (Fig 2): in `examples/compression/buffers_client.v`
  + `is_compressible`: `ML_client_code`.

Section 2.2:

- Definition of λC (Fig 3):
  + values and state are defined in `c_interface/defs.v` (`val` and `c_state`)
  + expressions and programs are defined in `c_lang/lang.v` (`expr`, `program`)

- Definition of λML (Fig 3):
  + values, expressions and state are defined in `ml_lang/lang.v` (`val`, `expr`, `state`)

- IrisC program logic rules (Fig 4):
  + `READ-C` is `wp_load` in `c_lang/primitive_laws.v`
  + `WRITE-C` is `wp_store` in `c_lang/primitive_laws.v`
  + `ALLOC-C` is `wp_Malloc_vec` in `c_lang/derived_laws.v`
  + `FREE-C` is `wp_free_array` in `c_lang/derived_laws.v`

- IrisML program logic rules (Fig 4):
  + `READ-ML` is `wp_loadN` in `ml_lang/primitive_laws.v`
  + `WRITE-ML` is `wp_storeN` in `ml_lang/primitive_laws.v`
  + `ALLOC-ML` is `wp_allocN` in `ml_lang/primitive_laws.v`

- `CALL-INTERNAL` (Fig 4) is `wp_call` in `language/weakestpre.v`
  (formulated as a rule on weakest preconditions instead of triples).
  It applies to both the WP of λML and λC.

- `CALL-EXTERNAL` (Fig 4) is `wp_extern'` in `language/weakestpre.v`
  (formulated as a rule on weakest preconditions instead of triples).
  It applies to both the WP of λML and λC.

- The triple for `snappy_max_compressed_length` and for `snappy_compress` is specified in
  `examples/compression/compression_specs.v`, the proofs are in
  `examples/compression/compression_proofs.v`

- The triple for `is_compressible` appears in `examples/compression/buffers_client.v`

- The triple for `buf_alloc` appears in `examples/compression/buffers_proof_alloc.v`

- The λML interface Ψbuf_alloc for `buf_alloc` is defined in `examples/compression/buffers_specs_simpler.v`.
  Note that the interface shown in the paper is derived from a stronger specification of
  `buf_alloc`, shown in `examples/compression/buffers_specs.v`.

- Note: we currently only have binary pairs in the Coq formalization, whereas
  the paper use tuples with 3 elements for representing λML buffers. In the Coq
  formalization we have nested pairs instead.

Section 2.3:

- The λC implementation for `buf_alloc` (Fig 5) appears in `examples/compression/buffers_code.v`.

Section 2.4:

- Runtime values are defined in `interop/basics.v` (`lval`)

- Separation logic runtime resources are defined in `interop/basics_resources.v`:
  + `γ ↦vblk[ m ] (t, vs)` is a standard block storing values `vs`, with tag `t`
    and mutability `m`
  + `γ ↦foreign a` is a custom block (custom blocks are called foreign blocks in
    the Coq development)

- The relation between runtime values and λC values (`v ~_C^θ w` in the paper)
  is defined in `interop/basics.v` as `repr_lval`.

- The type of θ maps is defined in `interop/basics.v` (`addr_map`)

- The interface of the alloc primitive Ψalloc is `alloc_proto` in `interop/prims_proto.v`.
- The interface of the FFI Ψ_FFI is `prims_proto` in `interop/prims_proto.v`
  (at this point of the paper its parameter is omitted, see §4).

- The Hoare triple for the λC `buf_alloc` function is `buf_alloc_spec_C` in
  `examples/compression/buffers_proof_alloc.v`.

Section 2.5:

- `ML-TO-FFI` (Fig 6) is `ml_to_mut` in `interop/update_laws.v`
- `FFI-TO-ML` (Fig 6) is `mut_to_ml` in `interop/update_laws.v`

- The view reconciliation rule for buffers is proved in `examples/compression/buffers_specs.v`.

Section 3:

- Small-step operational semantics of λML appear in `ml_lang/lang.v` (`head_step`)
- Small-step operational semantics of λC appear in `c_lang/lang.v` (`head_step`)
- The linking operational semantics appear in `linking/lang.v`
- The wrapper operational semantics appear in `interop/lang.v`
- [e]_FFI (as a program) is `wrap_prog` defined in `interop/lang.v`
- Linking of two programs is `link_prog` defined in `linking/lang.v`

Section 3.1:

- The runtime state of the wrapper is defined in `interop/lang.v` (`state`),
  using auxiliary definitions in `interop/state.v` and `interop/basics.v`
- The generic lifting from languages with relational semantics to multirelation
  semantics is defined in `lang_to_mlang/lang.v`
- The definition `closed` corresponds to `GC_correct` in `interop/basics.v`
- The definition `roots` corresponds to `roots_are_live` in `interop/basics.v`
- The list of runtime primitives is defined in `interop/prims.v`
- The operational semantics of runtime primitives is defined in `interop/lang.v`
  (`c_prim_step`), except for `callback` and `main` which are cases of
  `prim_step_mrel`.

Section 4.1:

- Theorem 4.1 is `combined_correct` in `combined/rules.v`
- The FFI wrapper for interfaces [.]_FFI is `wrap_proto` in `interop/prims_proto.v`
- The interface of the FFI Ψ_FFI^Π is `prims_proto` in `interop/prims_proto.v`

- `IntfImplement` (Fig 8) is `prove_prog_correct` in `language/weakestpre.v`
- `IntfConseq` (Fig 8) is `prog_triple_mono` in `language/weakestpre.v`
- `Link` (Fig 8) is `link_close_correct` in `linking/weakestpre.v`
- `EmbedML` (Fig 8) is `wrap_correct` in `interop/wp_simulation.v` (the Coq
  theorem is slightly more general, by setting `P` to true one gets the rule
  from the paper)
- `EmbedC` (Fig 8) is `combined_embed_c` in `combined/rules.v`


- Rules of Fig 9 are formulated in Coq as rules of the form "Ψ |- p : Π";
  they desugar to the rules given in the paper.
  + `AllocCustom` is `alloc_foreign_correct` in `interop/wp_prims/alloc_foreign.v`
  + `RegisterRoot` is `registerroot_correct` in `interop/wp_prims/registerroot.v`
  + `ExecCallback` is `callback_correct` in `interop/wp_simulation.v`

Section 4.2:
- The definition of the GC resource is in `interop/gctoken.v`

Section 4.3:

- Theorem 4.2 is `main_adequacy_trace` in `combined/adequacy.v`
- The coinductive definition of program executions is `umrel.trace`, defined in
  `multirelations.v`
- The definition (Fig 10) of the weakest-precondition predicate for
  multirelation semantics with external calls is `wp_pre`/`wp_pre_cases` in
  `mlanguage/weakestpre.v`
- The definition of the weakest-precondition predicate for usual relational
  semantics (used by IrisML and IrisC) is `wp_pre` in `language/weakestpre.v`

Section 5:

- The specification for `buf_upd` is in `examples/compression/buffers_specs_simpler.v`, again
  the on-paper version differs from the one originally verified (`examples/compression/buffers_specs.v`).
  The correctness proof is in `examples/compression/buffers_proof_update_.v`.

- The is-eq example is in `examples/is_eq`

- Logical relation is defined in `theories/ml_lang/logrel`
  + the interpretation of external calls is defined in `theories/ml_lang/logrel/logrel.v`, called `prog_env_proto`
  + the corresponding interface for external calls is  in `theories/ml_lang/logrel/logrel.v`, called `interp_prog_env`

- Landin's knot is in `examples/landins_knot.v`

- Event listeners are in `examples/listener.v`
  + This includes an application of adequacy using the logical relation,
    called `listener_client_1_adequacy.v`

## Axioms

This development uses Transfinite Iris, which itself relies on the following
non-constructive axioms:

- Propositional Extensionality (`Coq.Logic.PropExtensionality.propositional_extensionality`)
- Proof Irrelevance (`Coq.Logic.ProofIrrelevance.proof_irrelevance`)
- (Dependent) Functional extensionality (`Coq.Logic.FunctionalExtensionality.functional_extensionality_dep`)
- Excluded Middle (`Coq.Logic.Classical_Prop.classic`)
- A version of the axiom of choice (`Coq.Logic.Epsilon.epsilon_statement`)

These axioms [can be safely added to
Coq](https://github.com/coq/coq/wiki/The-Logic-of-Coq#what-axioms-can-be-safely-added-to-coq).
