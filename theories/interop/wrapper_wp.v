From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem wrapperstate.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.interop Require Import linking_wp basics basics_resources.
Import Wrap.

Class wrapperGS Σ := WrapperGS {
  wrapperGS_lstoreGS :> ghost_mapG Σ lloc block;
  wrapperGS_addr_lvalGS :> ghost_mapG Σ addr lval;
  wrapperGS_lloc_mapGS :> ghost_mapG Σ lloc lloc_visibility;
  wrapperGS_locsetGS :> ghost_varG Σ (gsetUR loc);
  wrapperGS_addrmapGS :> ghost_varG Σ (leibnizO addr_map);
  wrapperGS_at_boundary :> ghost_varG Σ (leibnizO bool);
  wrapperGS_var_lstoreGS :> ghost_varG Σ lstore;
  wrapperGS_var_lloc_mapGS :> ghost_varG Σ lloc_map;
  wrapperGS_γζ : gname;
  wrapperGS_γζvirt : gname;
  wrapperGS_γroots_set : gname;
  wrapperGS_γroots_map : gname;
  wrapperGS_γθ : gname;
  wrapperGS_γχ : gname;
  wrapperGS_γχvirt : gname;
  wrapperGS_γat_boundary : gname;
}.

Section Embed_logic.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Notation MLval := ML_lang.val.
Notation Cval := C_lang.val.

Implicit Types P : iProp Σ.

Definition C_state_interp (ζ : lstore) (χ : lloc_map) (θ : addr_map) (roots : gset addr) : iProp Σ :=
    "SIζ" ∷ ghost_var wrapperGS_γζ (1/2) ζ
  ∗ "SIχ" ∷ ghost_var wrapperGS_γχ (1/2) χ
  ∗ "SIθ" ∷ ghost_var wrapperGS_γθ (1/2) θ
  ∗ "SIroots" ∷ ghost_var wrapperGS_γroots_set (1/2) roots
  ∗ "SIbound" ∷ ghost_var wrapperGS_γat_boundary (1/4) false.

Definition GC (θ : addr_map) : iProp Σ :=
  ∃ (ζ ζfreeze ζσ ζvirt : lstore) (χ χvirt : lloc_map) (σMLvirt : store)
    (roots_s : gset addr) (roots_m : gmap addr lval) (nMLv : nat),
    "GCζ" ∷ ghost_var wrapperGS_γζ (1/2) ζ
  ∗ "GCχ" ∷ ghost_var wrapperGS_γχ (1/2) χ
  ∗ "GCθ" ∷ ghost_var wrapperGS_γθ (1/2) θ
  ∗ "GCroots" ∷ ghost_var wrapperGS_γroots_set (1/2) roots_s
  ∗ "GCζvirt" ∷ lstore_own_auth wrapperGS_γζvirt ζvirt
  ∗ "GCbound" ∷ ghost_var wrapperGS_γat_boundary (1/4) false
  ∗ "(GCσMLv & GCnMLv & GCσdom)" ∷ state_interp σMLvirt nMLv
  ∗ "GCχvirt" ∷ lloc_own_auth wrapperGS_γχvirt χvirt
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

(* TODO: custom notation (like l1 ~~ML l2 )? *)
(* l1 is a location in the ML heap. l2 is a block location.
   They are similar if identified by χ *)
Definition block_sim_raw (ℓ : loc) (γ : lloc) : iProp Σ :=
  lloc_own_pub wrapperGS_γχvirt γ ℓ.

Definition GC_token_remnant (ζ : lstore) (χ : lloc_map) (roots_m : roots_map) : iProp Σ :=
   "GCζ" ∷ ghost_var wrapperGS_γζ (1/2) ζ
 ∗ "GCχ" ∷ ghost_var wrapperGS_γχ (1/2) χ
 ∗ "GCθ" ∷ ghost_var wrapperGS_γθ (1/2) (∅:addr_map)
 ∗ "GCroots" ∷ ghost_var wrapperGS_γroots_set (1/2) (dom roots_m)
 ∗ "GCrootsm" ∷ ghost_map_auth wrapperGS_γroots_map 1 (roots_m : gmap loc lval)
 ∗ "GCrootspto" ∷ ([∗ set] a ∈ (dom roots_m), a O↦ None).

Definition ML_state_interp (ζvirt : lstore) (χ : lloc_map) (roots : roots_map) (memC : memory) : iProp Σ :=
  ∃ (nCv : nat),
    "SIζ" ∷ ghost_var wrapperGS_γζ (1/2) ζvirt
  ∗ "SIχ" ∷ ghost_var wrapperGS_γχ (1/2) χ
  ∗ "SIθ" ∷ ghost_var wrapperGS_γθ (1/2) (∅ : addr_map)
  ∗ "SIroots" ∷ ghost_var wrapperGS_γroots_set (1/2) (dom roots)
  ∗ "SIbound" ∷ ghost_var wrapperGS_γat_boundary (1/2) true
  ∗ "SIζvirt" ∷ lstore_own_auth wrapperGS_γζvirt ζvirt
  ∗ "(HσCv & HnCv)" ∷ (state_interp (memC ∪ (fmap (fun k => None) roots)) nCv)
  ∗ "SIAχ" ∷ lloc_own_auth wrapperGS_γχvirt χ
  ∗ "SIAχNone" ∷ ([∗ map] _↦ℓ ∈ pub_locs_in_lstore χ ζvirt, ℓ ↦M/)
  ∗ "SIGCrem" ∷ GC_token_remnant ζvirt χ roots
  ∗ "%Hχinj" ∷ ⌜lloc_map_inj χ⌝
  ∗ "%Hother_blocks" ∷ ⌜dom ζvirt ⊆ dom χ⌝
  ∗ "%HmemCdisj" ∷ ⌜dom memC ## dom roots⌝.

Definition public_state_interp : store -> iProp Σ := (λ σ, ∃ n, state_interp σ n)%I.
Definition private_state_interp : wrapstateML -> iProp Σ := (λ ρml, ML_state_interp (ζML ρml) (χML ρml) (rootsML ρml) (privmemML ρml))%I.

Definition wrap_state_interp (σ : Wrap.state) : iProp Σ :=
  match σ with
  | Wrap.CState ρc mem =>
      "(%nCv & HσC & HnC)" ∷ (∃ n, state_interp mem n) ∗
      "SIC"        ∷ C_state_interp (ζC ρc) (χC ρc) (θC ρc) (rootsC ρc)
  | Wrap.MLState ρml σ =>
      "(%nMLv & HσML & HvML & HσMLdom)" ∷ public_state_interp σ ∗
      "SIML"         ∷ private_state_interp ρml
end.

Global Program Instance wrapGS :
  mlanguage.weakestpre.mlangGS _ Σ wrap_lang
:= {
  state_interp := wrap_state_interp;
  at_boundary := (ghost_var wrapperGS_γat_boundary (1/2) true)%I;
}.

Definition not_at_boundary := (ghost_var wrapperGS_γat_boundary (1/2) false)%I.

Global Program Instance wrap_linkableGS : linkableGS wrap_lang public_state_interp := {
  private_state_interp := private_state_interp
}.
Next Obligation.
  iIntros (σ pubσ privσ Hlink) "Hσ !>". inversion Hlink; subst. iApply "Hσ".
Qed.
Next Obligation.
  iIntros (pubσ privσ) "Hpubσ Hprivσ !>".
  iExists (MLState privσ pubσ). cbn. iSplitL; by iFrame.
Qed.
Next Obligation.
  intros [ρc mem|ρml σ]; cbn; iIntros "Hb Hσ".
  + iExists _, _. iPureIntro. econstructor.
  + iExFalso. iAssert (⌜true = false⌝)%I as "%Hdone".
    * iApply (ghost_var_agree with "Hb [Hσ]").
      iNamed "Hσ". iNamed "SIC". iFrame.
    * iPureIntro. congruence.
Qed.



Context (σ : Wrap.state).
Notation SI := (weakestpre.state_interp σ).

Lemma GC_in_C {θ}: ⊢ (SI -∗ GC θ -∗ ⌜∃ ρc mem, σ = CState ρc mem⌝)%I.
Proof.
  destruct σ. 2: iIntros "_ _"; iPureIntro; do 2 eexists; done.
  iNamed 1. iNamed 1. iNamed "SIML".
  iPoseProof (ghost_var_agree with "SIbound GCbound") as "%Hc".
  congruence.
Qed.

Notation "l ↦fresh{ dq } b" := (lstore_own_mut wrapperGS_γζvirt l dq (Mut, b) ∗ lloc_own_priv wrapperGS_γχvirt l)%I
  (at level 20, format "l  ↦fresh{ dq }  b") : bi_scope.
Notation "l ↦fresh b" := (l ↦fresh{DfracOwn 1} b)%I
  (at level 20, format "l  ↦fresh  b") : bi_scope.
Notation "l ↦mut{ dq } b" := (lstore_own_mut wrapperGS_γζvirt l dq (Mut, b) ∗ ∃ ll, block_sim_raw ll l)%I
  (at level 20, format "l  ↦mut{ dq }  b") : bi_scope.
Notation "l ↦mut b" := (l ↦mut{DfracOwn 1} b)%I
  (at level 20, format "l  ↦mut  b") : bi_scope.
Notation "l ↦imm b" := (lstore_own_immut wrapperGS_γζvirt l (Immut, b))%I
  (at level 20, format "l  ↦imm  b") : bi_scope.
Notation "l ↦roots{ dq } w" := (l ↪[wrapperGS_γroots_map]{dq} w)%I
  (at level 20, format "l  ↦roots{ dq }  w") : bi_scope.
Notation "l ↦roots w" := (l ↪[wrapperGS_γroots_map] w)%I
  (at level 20, format "l  ↦roots  w") : bi_scope.

Fixpoint block_sim (v : MLval) (l : lval) : iProp Σ := match v with
  (ML_lang.LitV (ML_lang.LitInt x)) => ⌜l = (Lint x)⌝
| (ML_lang.LitV (ML_lang.LitBool b)) => ⌜l = (Lint (if b then 1 else 0))⌝
| (ML_lang.LitV ML_lang.LitUnit) => ⌜l = (Lint 0)⌝
| (ML_lang.LitV (ML_lang.LitLoc ℓ)) => ∃ γ, ⌜l = (Lloc γ)⌝ ∗ block_sim_raw ℓ γ
| (ML_lang.PairV v1 v2) => ∃ γ lv1 lv2, ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (TagDefault, [lv1;lv2]) ∗ block_sim v1 lv1 ∗ block_sim v2 lv2
| (ML_lang.InjLV v) => ∃ γ lv, ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (TagDefault, [lv]) ∗ block_sim v lv
| (ML_lang.InjRV v) => ∃ γ lv, ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (TagInjRV, [lv]) ∗ block_sim v lv 
| (ML_lang.RecV _ _ _) => True end. (* TODO: callbacks ?? *)

Global Instance block_sim_pers v l : Persistent (block_sim v l).
Proof.
  induction v as [[x|b| |]| | | |] in l|-*; cbn; unshelve eapply (_).
Qed.

Definition block_sim_arr (vs:list MLval) (ls : list lval) : iProp Σ := [∗ list] v;l ∈ vs;ls, block_sim v l.

End Embed_logic.

(* reexport notations *)
Notation "l ↦fresh{ dq } b" := (lstore_own_mut wrapperGS_γζvirt l dq (Mut, b) ∗ lloc_own_priv wrapperGS_γχvirt l)%I
  (at level 20, format "l  ↦fresh{ dq }  b") : bi_scope.
Notation "l ↦fresh b" := (l ↦fresh{DfracOwn 1} b)%I
  (at level 20, format "l  ↦fresh  b") : bi_scope.
Notation "l ↦mut{ dq } b" := (lstore_own_mut wrapperGS_γζvirt l dq (Mut, b) ∗ ∃ ll, block_sim_raw ll l)%I
  (at level 20, format "l  ↦mut{ dq }  b") : bi_scope.
Notation "l ↦mut b" := (l ↦mut{DfracOwn 1} b)%I
  (at level 20, format "l  ↦mut  b") : bi_scope.
Notation "l ↦imm b" := (lstore_own_immut wrapperGS_γζvirt l (Immut, b))%I
  (at level 20, format "l  ↦imm  b") : bi_scope.
Notation "l ↦roots{ dq } w" := (l ↪[wrapperGS_γroots_map]{dq} w)%I
  (at level 20, format "l  ↦roots{ dq }  w") : bi_scope.
Notation "l ↦roots w" := (l ↪[wrapperGS_γroots_map] w)%I
  (at level 20, format "l  ↦roots  w") : bi_scope.

Ltac SI_GC_agree :=
  iDestruct (ghost_var_agree with "GCζ SIζ") as %?;
  iDestruct (ghost_var_agree with "GCχ SIχ") as %?;
  iDestruct (ghost_var_agree with "GCθ SIθ") as %?;
  iDestruct (ghost_var_agree with "GCroots SIroots") as %?;
  simplify_eq.
