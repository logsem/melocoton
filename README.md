# Melocoton

## Build instructions

TODO

## Structure of the Coq development

The Coq development lives in the `theories/` directory.

- `language_commons.v`: type and combinators on interfaces
  (called "protocols" in the development)

- `multirelations.v`: definition of multirelations for semantics with dual
  non-determinism

- `c_interface/`: definition of C values, state and corresponding SL resources.
  All of the development (except for concrete examples) only depends on
  `c_interface`, not on the concrete semantics of `c_lang`.

- `c_interop/`: the toplevel program logic rules of the FFI, exported as
  convenient λC Hoare triples (useful for verifying concrete examples).

- `c_lang/`: a small C-like language (λC in the paper). Uses types from
  `c_interface` for its values and state.
  
- `ml_lang/`: a small OCaml-like language (λOCaml in the paper).

- `language/`: language interface with the usual relational operational
  semantics, plus external calls. Both λC and λOCaml implement this interface.
  
- `mlanguage/`: a language interface similar to language but using multirelations
  for operational semantics with dual non-determinism.

- `lang_to_mlang/`: generic lifting of `language` semantics to `mlanguage`.

- `linking/`: linking of programs; operates on `mlanguage`s

- `interop/`: FFI semantics and program logic, as a `mlanguage`
  + `interop/basics.v`: definitions of the wrapper values, blocks, and various
    parts of its state
  + `interop/{state.v,lang.v}`: operational semantics of the wrapper
  + `interop/{basics_resources.v,gctoken.v}`: ghost state of the wrapper program logic
  + `interop/update_laws.v`: points-to update laws
  + `interop/prims_proto.v`: interfaces of the FFI primitives
  + `interop/wp_prims/*.v`: soundness proof of FFI primitives
  + `interop/wp_simulation.v`: toplevel soundness proof of the wrapper program logic
  + `interop/adequacy.v`: toplevel adequacy theorem for linked+wrapped programs
