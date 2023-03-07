From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Import defs resources.
From melocoton.ml_lang Require Import lang lang_instantiation primitive_laws.
From melocoton.interop Require Import basics basics_resources.

(* The [GC θ] resource.

   [GC θ] represents the collection of authoritative resources related to the ML
   runtime while running or interoperating with external C-like code. It is used
   e.g. in the points-to update laws that translate between ML and block-level
   pointsto.

   Its definition is best understood side-by-side with the wrapper state
   interpretation (in weakestpre.v), but is in its own separate file to make it
   possible to only import [GC θ] and relevant SL resources without depending on
   the wrapper WP and state interp.
 *)

Class wrapperGCtokGS Σ := WrapperGCtokGS {
  wrapperGS_basics :> wrapperBasicsGS Σ;
  wrapperGS_locsetGS :> ghost_varG Σ (gsetUR loc);
  wrapperGS_addrmapGS :> ghost_varG Σ (leibnizO addr_map);
  wrapperGS_var_lstoreGS :> ghost_varG Σ lstore;
  wrapperGS_var_lloc_mapGS :> ghost_varG Σ lloc_map;
  wrapperGS_γζ : gname;
  wrapperGS_γθ : gname;
  wrapperGS_γχ : gname;
  wrapperGS_γroots_set : gname;
}.

Section GCtoken.
Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!wrapperGCtokGS Σ}.

Definition GC (θ : addr_map) : iProp Σ :=
  ∃ (ζ ζfreeze ζσ ζvirt : lstore) (χ χvirt : lloc_map) (σMLvirt : store)
    (roots_s : gset addr) (roots_m : gmap addr lval),
    "GCζ" ∷ ghost_var wrapperGS_γζ (1/2) ζ
  ∗ "GCχ" ∷ ghost_var wrapperGS_γχ (1/2) χ
  ∗ "GCθ" ∷ ghost_var wrapperGS_γθ (1/2) θ
  ∗ "GCroots" ∷ ghost_var wrapperGS_γroots_set (1/2) roots_s
  ∗ "GCζvirt" ∷ lstore_own_auth ζvirt
  ∗ "(GCσMLv & GCσdom)" ∷ state_interp (σMLvirt : language.language.state ML_lang)
  ∗ "GCχvirt" ∷ lloc_own_auth χvirt
  ∗ "GCχNone" ∷ ([∗ map] _↦ℓ ∈ pub_locs_in_lstore χvirt ζvirt, ℓ ↦M/)
  ∗ "GCrootsm" ∷ ghost_map_auth wrapperGS_γroots_map 1 roots_m
  ∗ "GCrootspto" ∷ ([∗ map] a ↦ v ∈ roots_m, ∃ w, a ↦C w ∗ ⌜repr_lval θ v w⌝)
  ∗ "%Hrootsdom" ∷ ⌜dom roots_m = roots_s⌝
  ∗ "%Hrootslive" ∷ ⌜roots_are_live θ roots_m⌝
  ∗ "%Hfreezeρ" ∷ ⌜freeze_lstore ζ ζfreeze⌝
  ∗ "%Hfreezeeq" ∷ ⌜ζfreeze = ζσ ∪ ζvirt⌝
  ∗ "%Hfreezedj" ∷ ⌜ζσ ##ₘ ζvirt⌝
  ∗ "%Hstore_blocks" ∷ ⌜is_store_blocks χvirt σMLvirt ζσ⌝
  ∗ "%Hother_blocks" ∷ ⌜dom ζvirt ⊆ dom χvirt⌝
  ∗ "%Hstore" ∷ ⌜is_store χvirt ζfreeze σMLvirt⌝
  ∗ "%Hχvirt" ∷ ⌜expose_llocs χ χvirt⌝
  ∗ "%Hχinj" ∷ ⌜lloc_map_inj χ⌝ (* TODO redundant? *)
  ∗ "%HGCOK" ∷ ⌜GC_correct ζfreeze θ⌝.

End GCtoken.
