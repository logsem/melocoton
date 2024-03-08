# Naming conventions

## Syntax and semantics

### Generic language

Conventions when talking about a generic language (= an instance of the
`language` or `mlanguage` interface), or when defining a specific language (is
in `ml_lang/lang.v` or `c_lang/lang.v`).

- `v`, `vs`: value, list of values
- `e`: expression
- `σ`: state/heap
- `K`, `C`: evaluation context / continuation
- `p`: program (has type `lang_prog` or `mlang_prog`)
- `Λ`: language (has type `language ?val` or `mlanguage ?val`)
- `X`: set of "next states" after a step in the semantics (has type `expr * ?state → Prop`)
- `fn`: function name (has type `string`)

### In an FFI context

Conventions followed in `interop/` and files importing `interop/` (i.e anything
multi-language), starting from `interop/basics.v`.

- `prm`: FFI primitive name (has type `prim`)

#### ML

- `v`, `vs`: ML value, list of values (have type `val`)
- `ℓ`: ML location (has type `loc`)
- `σ`: ML state/heap (has type `store`) 

#### C

- `w`, `ws`: C value, list of values (have type `word`)
- `a`: C address (has type `addr`)
- `mem`: C state/heap (has type `memory`)

#### FFI

- `lv`, `lvs`: block-level value, list of values (have type `lval`)
- `γ`: block-level location (has type `lloc`)
- `blk`, (sometimes `b`): block (has type `block`)
- `ρ`: entire state of the FFI semantics
- `ρml`, `ρc`: private state of the FFI semantics, on the ML/C side respectively
- `ζ`: block heap (has type `lstore`)
- `χ`: map of block-level locations to ML locations (has type `lloc_map`)
- `θ`: map of block-level locations to C addresses (has type `addr_map`)

(TODO: in some places `v/V` is used instead of `lv/v`; these should be
updated...)

## Program logic

- `Ψ`: "protocol" (i.e spec for external calls) (has type `protocol ?val ?Σ`)

## Inherited from Iris

(see also the [Iris naming conventions](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_guide.md#naming-conventions-for-variablesargumentshypotheses))

- `P`, `Q`: Iris assertions (of type `iProp ?Σ`) 
- `Φ`: post-condition or general Iris predicate (of type `?A → iProp ?Σ`)
- `E`: mask of fancy update or WP
- `Σ`: global camera functor management (of type `gFunctors`)
