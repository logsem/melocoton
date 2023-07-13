# Melocoton: a Coq model and separation logic for verified interoperability between OCaml and C

## Building

You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

The simplest option is to create a fresh *local* opam switch with everything
needed, by running the following commands:

```
opam switch create -y --repositories=default,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git . ocaml-base-compiler.4.14.1
eval $(opam env)
```

Then run:

```
make
make html # optional, builds an html rendering of the sources
```

### Troubleshooting

- When visiting the artifact from a new terminal session, one needs to call opam
 to re-setup the terminal environment. To do this, call `eval $(opam env)` from
 the root of the repository.

- If the `opam switch` invocation fails at some point, either remove the `_opam`
 directory and re-run the command (this will redo everything), or do `eval
 $(opam env)` and then `opam install -y .` (this will continue from where it
 failed).

## Browsing the development

An easy way to browse the development is to open [html/toc.html](html/toc.html)
in a web browser after running `make html`. The webpage contains an HTML
rendering of the Coq scripts of the development.

Alternatively, using an IDE with Coq support is recommended.

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

- The iseq example is in `examples/iseq`

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

### Verifying consistency
To check that these are the only axioms, and that we have not `Admitted.` any proofs, use the `Print Assumptions` command.

For example, execute `Print Assumptions buffers_adequate` at the end of `theories/examples/buffers_adequacy.v` to see that
the only assumptions used to validate the buffer examples are the ones above



