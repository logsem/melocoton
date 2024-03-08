## Guide through the development following the paper

All paths are relative to the `theories/` directory.

General notes: 
- Hoare-triples shown in the paper will sometimes omit "later" modalities (▷)
  that appear in front of *preconditions* of the Coq version. Later modalities
  in preconditions make the Coq statement *slightly stronger* than the paper
  version. In other words, omitting the "later" on paper is sound, and the
  on-paper rule is a *consequence* of the corresponding rule in Coq.
- The syntax `"foo_name" ∷ foo` is equivalent to `foo`. The extra string is 
  a naming hint for tactics and has no semantic meaning.
- The Coq scripts sometimes formulate rules in terms of weakest-preconditions
  (`WP e {{ Q }}`) where the paper uses Hoare-triples (`{ P } e { Q }`). To help
  matching the two, in first approach, a triple `{ P } e { Q }` can be read as
  sugar for (`P -∗ WP e {{ Q }}`). (The exact definition is slightly different
  and includes extra modalities, see "Texan triples" in iris, in
  `bi/weakestpre.v`.)

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
  (`ML_client_spec`, albeit with a stronger specification wrt the return boolean)

- The λML interface Ψbuf_alloc for `buf_alloc` is defined in `examples/compression/buffers_specs_simpler.v` (`buf_alloc_spec_ML_simple`).
  Note that the interface shown in the paper is derived from a stronger specification of
  `buf_alloc`, shown in `examples/compression/buffers_specs.v` (`buf_alloc_spec_ML`).

- Note: we currently only have binary pairs in the Coq formalization, whereas
  the paper use tuples with 3 elements for representing λML buffers. In the Coq
  formalization we have nested pairs instead.

Section 2.3:

- The λC implementation for `buf_alloc` (Fig 5) appears in `examples/compression/buffers_code.v`
  (`buf_alloc_code`).

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

- The view reconciliation rule for buffers is proved in `examples/compression/buffers_laws.v`
  (`bufToML`).

Section 3:

- Small-step operational semantics of λML appear in `ml_lang/lang.v` (`head_step`)
- Small-step operational semantics of λC appear in `c_lang/lang.v` (`head_step`)
- The linking operational semantics appear in `linking/lang.v` (`prim_step_mrel`)
- The wrapper operational semantics appear in `interop/lang.v` 
  (`prim_step_mrel`, using `c_prim_step` as an auxiliary definition)
- [e]_FFI (as a program) is `wrap_prog` defined in `interop/lang.v`
- Linking of two programs is `link_prog` defined in `linking/lang.v`

Section 3.1:

- The runtime state of the wrapper is defined in `interop/lang.v` (`state`),
  using auxiliary definitions in `interop/state.v` and `interop/basics.v`
- The generic lifting from languages with relational semantics to multirelation
  semantics is defined in `lang_to_mlang/lang.v` (`prim_step_mrel`)
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
- The definition of the GC resource is in `interop/gctoken.v` (`GC`)

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
