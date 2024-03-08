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
