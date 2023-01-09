From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem wrapperstate.
From iris.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra Require Import gset gset_bij.
From melocoton Require Import big_sepM_limited.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.interop Require Import linking_wp basics.
Import Wrap.

Class wrapperGS Σ := WrapperGS {
  wrapperGS_lstoreGS :> ghost_mapG Σ lloc block;
  wrapperGS_freshGS :> ghost_mapG Σ lloc unit;
  wrapperGS_loc_lvalGS :> ghost_mapG Σ loc lval;
  wrapperGS_lloc_mapGS :> ghost_mapG Σ loc lloc;
  wrapperGS_locsetGS :> ghost_varG Σ (gsetUR loc);
  wrapperGS_addrmapGS :> ghost_varG Σ (leibnizO addr_map);
  wrapperGS_at_boundary :> ghost_varG Σ (leibnizO bool);
  wrapperGS_gsetbijGS :> gset_bijG Σ loc lloc;
  wrapperGS_γζblock : gname;
  wrapperGS_γfresh : gname;
  wrapperGS_γroots_set : gname;
  wrapperGS_γroots_map : gname;
  wrapperGS_γθ : gname;
  wrapperGS_γχbij : gname;
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

Definition GC (θ : addr_map) : iProp Σ :=
  ∃ (roots_s : gset addr) (roots_m : gmap loc lval),
    "HAGCθ" ∷ ghost_var wrapperGS_γθ (1/2) θ
  ∗ "HAGCbound" ∷ ghost_var wrapperGS_γat_boundary (1/4) false
  ∗ "HArootss" ∷ ghost_var wrapperGS_γroots_set (1/2) roots_s
  ∗ "HArootsm" ∷ ghost_map_auth wrapperGS_γroots_map 1 roots_m
  ∗ "%Hrootsdom" ∷ ⌜dom roots_m = roots_s⌝
  ∗ "%Hrootslive" ∷ ⌜roots_are_live θ roots_m⌝
  ∗ "Hrootspto" ∷ ([∗ map] a ↦ v ∈ roots_m, ∃ w, a ↦C w ∗ ⌜repr_lval θ v w⌝).

(* TODO: custom notation (like l1 ~~ML l2 )? *)
(* l1 is a location in the ML heap. l2 is a block location.
   They are similar if identified by χ *)
Definition block_sim_raw (l1 : loc) (l2 : lloc) : iProp Σ := (gset_bij_own_elem wrapperGS_γχbij l1 l2).

Definition C_state_interp (ζ : lstore) (χ : lloc_map) (θ : addr_map) (roots : gset addr) : iProp Σ :=
  ∃ (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (fresh : gmap lloc unit) (σMLvirt : store),
    "HAroots" ∷ ghost_var wrapperGS_γroots_set (1/2) roots
  ∗ "HAθ" ∷ ghost_var wrapperGS_γθ (1/2) θ
  ∗ "HAζbl" ∷ ghost_map_auth wrapperGS_γζblock 1 ζrest
  ∗ "(%nMLv & HAσMLv & HAnMLv & HAσdom & HAσsafe)" ∷ (∃ n, state_interp σMLvirt n)
  ∗ "HAχbij" ∷ gset_bij_own_auth wrapperGS_γχbij (DfracOwn 1) (map_to_set pair χvirt)
  ∗ "HAfresh" ∷ ghost_map_auth wrapperGS_γfresh 1 fresh
  ∗ "HAχNone" ∷ big_sepM_limited χvirt (dom ζrest) (fun ℓ _ => ℓ ↦M/)
  ∗ "#HAζpers" ∷ ([∗ map] l ↦ bb ∈ ζrest, ⌜mutability bb = Immut⌝ -∗ l ↪[ wrapperGS_γζblock ]□ bb)
  ∗ "HAbound" ∷ ghost_var wrapperGS_γat_boundary (1/4) false
  ∗ "%Hfreezeρ" ∷ ⌜freeze_lstore ζ ζfreeze⌝
  ∗ "%Hfreezeeq" ∷ ⌜ζfreeze = ζσ ∪ ζrest⌝
  ∗ "%Hfreezedj" ∷ ⌜ζσ ##ₘ ζrest⌝
  ∗ "%Hstore_blocks" ∷ ⌜is_store_blocks χvirt σMLvirt ζσ⌝
  ∗ "%Hstore" ∷ ⌜is_store χvirt ζfreeze σMLvirt⌝
  ∗ "%Hχvirt" ∷ ⌜lloc_map_mono χ χvirt⌝
  ∗ "%Hχinj" ∷ ⌜gmap_inj χ⌝
  ∗ "%Hfreezeχ" ∷ ⌜∀ x y, χvirt !! x = Some y → y ∈ dom ζfreeze⌝
  ∗ "%Hfreshχ" ∷ ⌜∀ x y, χvirt !! x = Some y → y ∉ dom fresh⌝
  ∗ "%HGCOK" ∷ ⌜GC_correct ζfreeze θ⌝.

(* TODO: names *)
Definition GC_token_remnant (roots_m : roots_map) : iProp Σ :=
   "HAGCθ" ∷ ghost_var wrapperGS_γθ (1/2) (∅:addr_map)
 ∗ "HArootss" ∷ ghost_var wrapperGS_γroots_set (1/2) (dom roots_m)
 ∗ "HArootsm" ∷ ghost_map_auth wrapperGS_γroots_map 1 (roots_m : gmap loc lval)
 ∗ "Hrootspto" ∷ ([∗ set] a ∈ (dom roots_m), a O↦ None).

Definition ML_state_interp (ζrest : lstore) (χ : lloc_map) (roots : roots_map) (memC : memory) : iProp Σ := 
  ∃  (ζσ ζ : lstore) (fresh : gmap lloc unit),
    "HAroots" ∷ ghost_var wrapperGS_γroots_set (1/2) (dom roots)
  ∗ "HAθ" ∷ ghost_var wrapperGS_γθ (1/2) (∅ : addr_map)
  ∗ "HAζbl" ∷ ghost_map_auth wrapperGS_γζblock 1 ζrest
  ∗ "(%nCv & HAσCv & HAnCv)" ∷ (∃ n, state_interp (memC ∪ (fmap (fun k => None) roots)) n)
  ∗ "#HAσdomF" ∷ dom_part (dom χ)
  ∗ "HAχbij" ∷ gset_bij_own_auth wrapperGS_γχbij (DfracOwn 1) (map_to_set pair χ)
  ∗ "HAfresh" ∷ ghost_map_auth wrapperGS_γfresh 1 fresh
  ∗ "HAχNone" ∷ big_sepM_limited χ (dom ζrest) (fun ℓ _ => ℓ ↦M/)
  ∗ "#HAζpers" ∷ ([∗ map] l ↦ bb ∈ ζrest, ⌜mutability bb = Immut⌝ -∗ l ↪[ wrapperGS_γζblock ]□ bb)
  ∗ "HAbound" ∷ ghost_var wrapperGS_γat_boundary (1/2) true
  ∗ "HAGCrem" ∷ GC_token_remnant roots
  ∗ "%Hfreezeeq" ∷ ⌜ζ = ζσ ∪ ζrest⌝
  ∗ "%Hfreezedj" ∷ ⌜ζσ ##ₘ ζrest⌝
  ∗ "%Hχinj" ∷ ⌜gmap_inj χ⌝
  ∗ "%Hfreezeχ" ∷ ⌜∀ x y, χ !! x = Some y → y ∈ dom ζ⌝
  ∗ "%Hfreshχ" ∷ ⌜∀ x y, χ !! x = Some y → y ∉ dom fresh⌝.

Definition public_state_interp : store -> iProp Σ := (λ σ, ∃ n, state_interp σ n)%I.
Definition private_state_interp : wrapstateML -> iProp Σ := (λ ρml, ML_state_interp (ζML ρml) (χML ρml) (rootsML ρml) (privmemML ρml))%I.

Definition wrap_state_interp (σ : Wrap.state) : iProp Σ :=
  match σ with
  | Wrap.CState ρc mem =>
      "(%nCv & HσC & HnC)" ∷ (∃ n, state_interp mem n) ∗
      "SIC"        ∷ C_state_interp (ζC ρc) (χC ρc) (θC ρc) (rootsC ρc)
  | Wrap.MLState ρml σ =>
      "(%nMLv & HσML & HvML & HσMLdom & HσMLval)" ∷ public_state_interp σ ∗
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
  iPoseProof (ghost_var_agree with "HAbound HAGCbound") as "%Hc".
  congruence.
Qed.

(* todo: version of the notations without dq *)
Notation "l ↦fresh{ dq } b" := (  ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l dq (Mut, b)
                                ∗ ghost_map_elem (K:=lloc) (V:=unit) wrapperGS_γfresh l dq (()))%I
  (at level 20, format "l  ↦fresh{ dq }  b") : bi_scope.
Notation "l ↦mut{ dq } b" := (  ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l dq (Mut, b)
                              ∗ ∃ ll, block_sim_raw ll l)%I
  (at level 20, format "l  ↦mut{ dq }  b") : bi_scope.
Notation "l ↦imm b" := (  ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l DfracDiscarded (Immut, b))%I
  (at level 20, format "l  ↦imm  b") : bi_scope.

Fixpoint block_sim (v : MLval) (l : lval) : iProp Σ := match v with
  (ML_lang.LitV (ML_lang.LitInt x)) => ⌜l = (Lint x)⌝
| (ML_lang.LitV (ML_lang.LitBool b)) => ⌜l = (Lint (if b then 1 else 0))⌝
| (ML_lang.LitV ML_lang.LitUnit) => ⌜l = (Lint 0)⌝
| (ML_lang.LitV ML_lang.LitPoison) => False (* TODO: remove poison? *)
| (ML_lang.LitV (ML_lang.LitLoc ℓ)) => ∃ γ, ⌜l = (Lloc γ)⌝ ∗ block_sim_raw ℓ γ
| (ML_lang.PairV v1 v2) => ∃ γ lv1 lv2, ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (TagDefault, [lv1;lv2]) ∗ block_sim v1 lv1 ∗ block_sim v2 lv2
| (ML_lang.InjLV v) => ∃ γ lv, ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (TagDefault, [lv]) ∗ block_sim v lv
| (ML_lang.InjRV v) => ∃ γ lv, ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (TagInjRV, [lv]) ∗ block_sim v lv 
| (ML_lang.RecV _ _ _) => True end. (* TODO: callbacks ?? *)

Global Instance block_sim_pers v l : Persistent (block_sim v l).
Proof.
  induction v as [[x|b| | |]| | | |] in l|-*; cbn; unshelve eapply (_).
Qed.

Definition block_sim_arr (vs:list MLval) (ls : list lval) : iProp Σ := [∗ list] v;l ∈ vs;ls, block_sim v l.

End Embed_logic.


(* todo: version of the notations without dq *)
Global Notation "l ↦fresh{ dq } b" := (  ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l dq (Mut, b)
                                ∗ ghost_map_elem (K:=lloc) (V:=unit) wrapperGS_γfresh l dq (()))%I
  (at level 20, format "l  ↦fresh{ dq }  b") : bi_scope.
Global Notation "l ↦mut{ dq } b" := (  ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l dq (Mut, b)
                              ∗ ∃ ll, block_sim_raw ll l)%I
  (at level 20, format "l  ↦mut{ dq }  b") : bi_scope.
Global Notation "l ↦imm b" := (  ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l DfracDiscarded (Immut, b))%I
  (at level 20, format "l  ↦imm  b") : bi_scope.




















