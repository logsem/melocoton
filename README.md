# Coq development for Melocoton

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
  + small-step operational semantics are in `c_lang/lang.v` (`head_step`)

- Definition of λML (Fig 3):
  + values, expressions and state are defined in `ml_lang/lang.v` (`val`, `expr`, `state`)
  + small-step operational semantics are in `ml_lang/lang.v` (`head_step`)

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

- The triple for `snappy_max_compressed_length` appears in TODO

- The triple for `snappy_compress` appears in TODO

- The triple for `is_compressible` appears in TODO

- The triple for `buf_alloc` appears in TODO

- The λML interface Ψbuf_alloc for `buf_alloc` is defined in TODO

Section 2.3:

- The λC implementation for `buf_alloc` (Fig 5) appears in TODO

Section 2.4:

Section 2.5:

Section 3:

Section 3.1:

Section 4.1:

Section 4.2:

Section 4.3:

Section 5:

- The specification for `buf_upd` is in TODO

- The iseq example is in TODO

- Logical relation is defined in TODO
  + the interpretation of external calls is defined in TODO
  + the corresponding interface for external calls is TODO

- Landin's knot is in TODO
  + code in TODO
  + semantic type safety theorem in TODO

- Even listeners are in TODO
  + code in TODO
  + semantic type safety theorem in TODO
