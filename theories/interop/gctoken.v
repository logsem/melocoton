From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Export defs resources.
From melocoton.ml_lang Require Import lang_instantiation.
From melocoton.ml_lang Require Export lang primitive_laws.
From melocoton.interop Require Import basics_resources.

(** The [GC θ] resource.

   [GC θ] represents the collection of authoritative resources related to the ML
   runtime while running or interoperating with external C-like code. It is used
   e.g. in the points-to update laws that translate between ML and block-level
   pointsto.

   Its definition is best understood side-by-side with the wrapper state
   interpretation (in weakestpre.v), but is in its own separate file to make it
   possible to only import [GC θ] and relevant SL resources without depending on
   the wrapper WP and state interp.
 *)

Class wrapperGCtokGpre `{SI: indexT} Σ := WrapperGCtokGpre {
  wrapperG_locsetG :> ghost_varG Σ (gsetUR loc);
  wrapperG_addrmapG :> ghost_varG Σ (leibnizO addr_map);
  wrapperG_var_lstoreG :> ghost_varG Σ lstore;
  wrapperG_var_lloc_mapG :> ghost_varG Σ lloc_map;
  wrapperG_var_bool :> ghost_varG Σ (leibnizO bool);
}.

Class wrapperGCtokG `{SI: indexT} Σ := WrapperGCtokG {
  wrapperG_basics :> wrapperBasicsG Σ;
  wrapperG_inG :> wrapperGCtokGpre Σ;
  wrapperG_γζ : gname;
  wrapperG_γθ : gname;
  wrapperG_γχ : gname;
  wrapperG_γroots_set : gname;
  wrapperG_γat_init : gname;
}.

Definition wrapperGCtokΣ {SI: indexT} : gFunctors :=
  #[ghost_varΣ (gsetUR loc); ghost_varΣ (leibnizO addr_map);
    ghost_varΣ lstore; ghost_varΣ lloc_map; ghost_varΣ (leibnizO bool)].

Global Instance subG_wrapperGCtokGpre `{SI: indexT} Σ :
  subG wrapperGCtokΣ Σ → wrapperGCtokGpre Σ.
Proof. solve_inG. Qed.

Section GCtoken.
Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!wrapperGCtokG Σ}.

Definition SI_block_level_old (ζ_future : lstore) (χ_future : lloc_map) : iProp Σ :=
  ∃ (σMLvirt : store) (ζσ ζvirt : lstore),
    "GCζvirt" ∷ lstore_own_auth ζvirt
  ∗ "GCσMLv" ∷ state_interp (σMLvirt : language.language.state ML_lang)
  ∗ "GCχvirt" ∷ lloc_own_auth χ_future
  ∗ "GCχNone" ∷ ([∗ map] _↦ℓ ∈ pub_locs_in_lstore χ_future ζvirt, ℓ ↦M/)
  ∗ "%Hfreezeeq" ∷ ⌜ζ_future = ζσ ∪ ζvirt⌝
  ∗ "%Hfreezedj" ∷ ⌜ζσ ##ₘ ζvirt⌝
  ∗ "%Hstore_blocks" ∷ ⌜is_store_blocks χ_future σMLvirt ζσ⌝
  ∗ "%Hother_blocks" ∷ ⌜dom ζvirt ⊆ dom χ_future⌝
  ∗ "%Hstore" ∷ ⌜is_store χ_future ζ_future σMLvirt⌝.

Definition per_location_invariant (ζ_future : lstore) (σMLvirt : store)
     (γ : lloc) (ℓ : loc) : iProp Σ :=
  ∃ (vs : list val) tg lvs, 
    ( ℓ ↦M/ ∗ ⌜ζ_future !! γ = Some (Bvblock (Mut, (tg, lvs)))⌝)
  ∨ (⌜σMLvirt !! ℓ = Some (Some vs)⌝ ∗ (γ ↦mut (tg, lvs)) ∗ lvs ~~∗ vs ∗ ⌜tg = TagDefault⌝)
  ∨ (⌜σMLvirt !! ℓ = None⌝ ∗ ⌜ζ_future !! γ = None⌝)
  ∨ (⌜σMLvirt !! ℓ = Some None⌝ ∗ ⌜ζ_future !! γ = None⌝).
(* the last two are "phony cases" -- they should not exist, but we do not control χ good enough in the op sem *)

Definition SI_block_level (ζ_future : lstore) (χ_future : lloc_map) : iProp Σ :=
  ∃ (σMLvirt : store),
    "GCχauth" ∷ lloc_own_auth χ_future
  ∗ "GCζauth" ∷ lstore_own_auth ζ_future
  ∗ "%Hother_blocks" ∷ ⌜dom ζ_future ⊆ dom χ_future⌝
  ∗ "GCσMLv" ∷ state_interp (σMLvirt : language.language.state ML_lang)
  ∗ "GC_per_loc" ∷ ([∗ map] γ↦ℓ ∈ lloc_map_pubs χ_future,
      per_location_invariant ζ_future σMLvirt γ ℓ)
  ∗ "%Hstore" ∷ ⌜∀ ℓ, ℓ ∈ dom σMLvirt → ∃ γ, χ_future !! γ = Some (LlocPublic ℓ)⌝.

Definition SI_GC (ζ_future : lstore) (θ : addr_map) (roots_s : gset addr) : iProp Σ :=
  ∃ (roots_m : gmap addr lval),
    "GCrootsm" ∷ ghost_map_auth wrapperG_γroots_map 1 roots_m
  ∗ "GCrootspto" ∷ ([∗ map] a ↦ v ∈ roots_m, ∃ w, a ↦C w ∗ ⌜repr_lval θ v w⌝)
  ∗ "%Hrootsdom" ∷ ⌜dom roots_m = roots_s⌝
  ∗ "%Hrootslive" ∷ ⌜roots_are_live θ roots_m⌝
  ∗ "%HGCOK" ∷ ⌜GC_correct ζ_future θ⌝.

Definition GC (θ : addr_map) : iProp Σ :=
  ∃ (ζ ζ_future : lstore) (χ χ_future : lloc_map)
    (roots_s : gset addr),
    "GCζ" ∷ ghost_var wrapperG_γζ (1/2) ζ
  ∗ "GCχ" ∷ ghost_var wrapperG_γχ (1/2) χ
  ∗ "GCθ" ∷ ghost_var wrapperG_γθ (1/2) θ
  ∗ "GCroots" ∷ ghost_var wrapperG_γroots_set (1/2) roots_s
  ∗ "GCinit" ∷ ghost_var wrapperG_γat_init (1/2) false
  ∗ "HSI_block_level" ∷ SI_block_level ζ_future χ_future
  ∗ "HSI_GC" ∷ SI_GC ζ_future θ roots_s
  ∗ "%Hζfuture" ∷ ⌜freeze_lstore ζ ζ_future⌝
  ∗ "%Hχfuture" ∷ ⌜expose_llocs χ χ_future⌝.

Definition at_init := ghost_var wrapperG_γat_init (1/2) true.

End GCtoken.
