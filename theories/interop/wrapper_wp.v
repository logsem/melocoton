From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem wrapperstate.
From iris.base_logic.lib Require Export ghost_map ghost_var.
From iris.algebra.lib Require Import excl_auth gset_bij gmap_view.
From iris.algebra Require Import ofe.
From melocoton Require Import big_sepM_limited.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation  melocoton.primitive_laws.
From melocoton.interop Require Import linking_wp basics.
Import Wrap.

Class wrapperGS Σ := WrapperGS {
  wrapperGS_lstoreGS :> @ghost_mapG Σ lloc block Nat.eq_dec nat_countable;
  wrapperGS_freshGS :> @ghost_mapG Σ lloc unit Nat.eq_dec nat_countable;
  wrapperGS_loc_lvalGS :> @ghost_mapG Σ loc lval loc_eq_decision loc_countable;
  wrapperGS_lloc_mapGS :> @ghost_mapG Σ loc lloc loc_eq_decision loc_countable;
  wrapperGS_locsetGS :> ghost_varG Σ (gsetUR loc);
  wrapperGS_addrmapGS :> ghost_varG Σ (leibnizO addr_map);
  wrapperGS_at_boundary :> ghost_varG Σ (leibnizO bool);
  wrapperGS_gsetbihGS :> inG Σ (viewR (@gset_bij_view_rel loc loc_eq_decision loc_countable lloc Nat.eq_dec nat_countable));
  wrapperGS_γζblock : gname;
  wrapperGS_γfresh : gname;
  wrapperGS_γroots_set : gname;
  wrapperGS_γroots_map : gname;
  wrapperGS_γθ : gname;
  wrapperGS_γχbij : gname;
  wrapperGS_γχmap : gname;
  wrapperGS_γat_boundary : gname;
}.

Section Embed_logic.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context {HeapML : heapGS_ML Σ}.
Context {HeapC : heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.

Notation MLval := ML_lang.val.
Notation Cval := C_lang.val.

Implicit Types P : iProp Σ.

Context {WGS : wrapperGS Σ}.

Definition GC (θ : addr_map) : iProp Σ := 
     ghost_var wrapperGS_γθ (1/2) θ
   ∗ ghost_var wrapperGS_γat_boundary (1/4) false
   ∗ ∃ (roots : gset addr) (rootsmap : gmap loc lval),
       ghost_var wrapperGS_γroots_set (1/2) roots
     ∗ ghost_map_auth wrapperGS_γroots_map 1 rootsmap
     ∗ ⌜dom rootsmap = roots⌝
     ∗ ⌜roots_are_live θ rootsmap⌝
     ∗ ([∗ map] a ↦ v ∈ rootsmap, (∃ w, a ↦C w)).

(* TODO: custom notation (like l1 ~~ML l2 )? *)
(* l1 is a location in the ML heap. l2 is a block location.
   They are similar if identified by χ *)
Definition block_sim_raw (l1 : loc) (l2 : lloc) : iProp Σ := (l1 ↪[ wrapperGS_γχmap ]□ l2).

Definition C_state_interp (ζ : lstore) (χ : lloc_map) (θ : addr_map) (roots : gset addr) : iProp Σ :=
  ∃  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (fresh : gmap lloc unit) (σMLvirt : store),
    ghost_var wrapperGS_γroots_set (1/2) roots
  ∗ ghost_var wrapperGS_γθ (1/2) θ
  ∗ ghost_map_auth wrapperGS_γζblock 1 ζrest
  ∗ (∃ n, state_interp σMLvirt n)
  ∗ own wrapperGS_γχbij (gset_bij_auth (DfracOwn 1) (map_to_set pair χvirt))
  ∗ ghost_map_auth wrapperGS_γχmap 1 χvirt
  ∗ ghost_map_auth wrapperGS_γfresh 1 fresh
  ∗ big_sepM_limited χvirt (dom ζrest) (fun ℓ _ => ℓ ↦M/)
  ∗ ([∗ map] ℓ ↦ γ ∈ χvirt, block_sim_raw ℓ γ)
  ∗ ([∗ map] l ↦ bb ∈ ζrest, ⌜mutability bb = Immut⌝ -∗ l ↪[ wrapperGS_γζblock ]□ bb)
  ∗ ghost_var wrapperGS_γat_boundary (1/4) false
  ∗⌜freeze_lstore ζ ζfreeze
  ∧ ζfreeze = ζσ ∪ ζrest
  ∧ ζσ ##ₘ ζrest
  ∧ is_store_blocks χvirt σMLvirt ζσ
  ∧ is_store χvirt ζfreeze σMLvirt
  ∧ lloc_map_mono χ χvirt
  ∧ gmap_inj χ
  ∧ (∀ x y, χvirt !! x = Some y → y ∈ dom ζfreeze)
  ∧ (∀ x y, χvirt !! x = Some y → y ∈ dom fresh → False)
  ∧ GC_correct ζfreeze θ⌝.

Definition GC_token_remnant (roots : gset addr) : iProp Σ :=
   ghost_var wrapperGS_γθ (1/2) (∅:addr_map)
 ∗ ghost_var wrapperGS_γroots_set (1/2) roots
 ∗ ghost_map_auth wrapperGS_γroots_map 1 (∅:gmap loc lval)
 ∗ ([∗ set] a ∈ roots, a O↦ None).

Definition ML_state_interp (ζ : lstore) (χ : lloc_map) (roots : roots_map) (memC : memory) : iProp Σ := 
  ∃  (ζσ ζrest : lstore) (fresh : gmap lloc unit) (σCvirt : memory),
    ghost_var wrapperGS_γroots_set (1/2) (dom roots)
  ∗ ghost_var wrapperGS_γθ (1/2) (∅ : addr_map)
  ∗ ghost_map_auth wrapperGS_γζblock 1 ζrest
  ∗ (∃ n, state_interp σCvirt n)
  ∗ own wrapperGS_γχbij (gset_bij_auth (DfracOwn 1) (map_to_set pair χ))
  ∗ ghost_map_auth wrapperGS_γχmap 1 χ
  ∗ ghost_map_auth wrapperGS_γfresh (1/2) fresh
  ∗ big_sepM_limited χ (dom ζrest) (fun ℓ _ => ℓ ↦M/)
  ∗ ([∗ map] ℓ ↦ γ ∈ χ, block_sim_raw ℓ γ)
  ∗ ([∗ map] l ↦ bb ∈ ζrest, ⌜mutability bb = Immut⌝ -∗ l ↪[ wrapperGS_γζblock ]□ bb)
  ∗ ghost_var wrapperGS_γat_boundary (1/2) true
  ∗ GC_token_remnant (dom roots)
  ∗⌜ζ = ζσ ∪ ζrest
  ∧ ζσ ##ₘ ζrest
  ∧ gmap_inj χ
  ∧ (∀ x y, χ !! x = Some y → y ∈ dom ζ)
  ∧ (∀ x y, χ !! x = Some y → y ∈ dom fresh → False)⌝.

Definition public_state_interp : store -> iProp Σ := (λ σ, ∃ n, state_interp σ n)%I.
Definition private_state_interp : wrapstateML -> iProp Σ := (λ ρml, ML_state_interp (ζML ρml) (χML ρml) (rootsML ρml) (privmemML ρml))%I.

Definition wrap_state_interp (σ : Wrap.state) : iProp Σ := match σ with
  Wrap.CState ρc mem => (∃ n, state_interp mem n) ∗ C_state_interp (ζC ρc) (χC ρc) (θC ρc) (rootsC ρc)
| Wrap.MLState ρml σ => public_state_interp σ ∗ private_state_interp ρml
end.


Notation SIC_ip := "((%nCv & HσC) & (%ζfreeze & %ζσ & %ζrest & %χvirt & %fresh & %σMLvirt &
           HAroots & HAθ & HAζbl & (%nMLv & HAσMLv & HAnMLv) & HAχbij & HAχmap & HAfresh & HAχNone & #HAχpers & #HAζpers & HAbound &
          %Hfreezeρ & %Hfreezeeq & %Hfreezedj & %Hstore_blocks & %Hstore & %Hχvirt & %Hχinj & %Hfreezeχ & %Hfreshχ & %HGCOK))".

Notation SIML_ip := "((%nMLv & HσML) & (%ζσ & %ζrest & %fresh & %σCvirt &
           HAroots & HAθ & HAζbl & (%nCv & HAσCv & HAnCv) & HAχbij & HAχmap & HAfresh & HAχNone & #HAχpers & #HAζpers & HAbound & HAGCrem &
           %Hfreezeeq & %Hfreezedj & %Hχinj & %Hfreezeχ & %Hfreshχ))".

Notation GC_ip := "(HAGCθ & HAGCbound & (%roots_s & %roots_m & HArootss & HArootsm & %Hrootsdom & %Hrootslive & Hrootspto))".

Global Program Instance wrapGS :
  mlanguage.weakestpre.mlangGS _ Σ wrap_lang
:= {
  state_interp := wrap_state_interp;
  at_boundary := (ghost_var wrapperGS_γat_boundary (1/2) true)%I;
}.

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
      iDestruct "Hσ" as SIC_ip.  iFrame.
    * iPureIntro. congruence.
Qed.

Notation "l ↦fresh{ dq } b" := (  ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l dq b
                                ∗ ghost_map_elem (K:=lloc) (V:=unit) wrapperGS_γfresh l dq (())
                                ∗ ⌜mutability b = Mut⌝)%I
  (at level 20, format "l  ↦fresh{ dq } b") : bi_scope.
Notation "l ↦mut{ dq } b" := (  ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l dq b
                              ∗ ⌜mutability b = Mut⌝
                              ∗ ∃ ll, block_sim_raw ll l)%I
  (at level 20, format "l  ↦mut{ dq } b") : bi_scope.
Notation "l ↦imm b" := (  ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l DfracDiscarded b
                        ∗ ⌜mutability b = Immut⌝)%I
  (at level 20, format "l  ↦imm b") : bi_scope.

Fixpoint block_sim (v : MLval) (l : lval) : iProp Σ := match v with
  (ML_lang.LitV (ML_lang.LitInt x)) => ⌜l = (Lint x)⌝
| (ML_lang.LitV (ML_lang.LitBool b)) => ⌜l = (Lint (if b then 1 else 0))⌝
| (ML_lang.LitV ML_lang.LitUnit) => ⌜l = (Lint 0)⌝
| (ML_lang.LitV ML_lang.LitPoison) => False (* TODO: remove poison? *)
| (ML_lang.LitV (ML_lang.LitLoc ℓ)) => ∃ γ, ⌜l = (Lloc γ)⌝ ∗ block_sim_raw ℓ γ
| (ML_lang.PairV v1 v2) => ∃ γ lv1 lv2, ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (Immut, TagDefault, [lv1;lv2]) ∗ block_sim v1 lv1 ∗ block_sim v2 lv2
| (ML_lang.InjLV v) => ∃ γ lv, ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (Immut, TagDefault, [lv]) ∗ block_sim v lv
| (ML_lang.InjRV v) => ∃ γ lv, ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (Immut, TagInjRV, [lv]) ∗ block_sim v lv 
| (ML_lang.RecV _ _ _) => False end. (* Todo: callbacks *)

Global Instance block_sim_pers v l : Persistent (block_sim v l).
Proof.
  induction v as [[x|b| | |]| | | |] in l|-*; cbn; unshelve eapply (_).
Qed.

Definition block_sim_arr (vs:list MLval) (ls : list lval) : iProp Σ := [∗ list] v;l ∈ vs;ls, block_sim v l.

Context (σ : Wrap.state).
Notation SI := (weakestpre.state_interp σ).

Lemma GC_in_C {θ}: ⊢ (SI -∗ GC θ -∗ ⌜∃ ρc mem, σ = CState ρc mem⌝)%I.
Proof.
  destruct σ. 2: iIntros "_ _"; iPureIntro; do 2 eexists; done.
  iIntros SIML_ip. iIntros GC_ip.
  iAssert (⌜true = false⌝)%I as "%Hdone".
  1: iApply (ghost_var_agree with "HAbound HAGCbound").
  congruence.
Qed.


Lemma block_sim_of_ghost_state  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   v b :
     ([∗ map] ℓ ↦ γ ∈ χvirt, block_sim_raw ℓ γ)
  -∗ ([∗ map] l ↦ bb ∈ ζrest, ⌜mutability bb = Immut⌝ -∗ l ↪[ wrapperGS_γζblock ]□ bb)
  -∗⌜ζfreeze = ζσ ∪ ζrest⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζrest⌝
  -∗⌜is_val χvirt ζfreeze v b⌝
  -∗ block_sim v b.
Proof.
  iIntros "#Hχ #Hζ %Hfreeze %Hstorebl %Hstore %Hdisj %H".
  iInduction v as [[x|bo| | |]| | | |] "IH" forall (b H); cbn; inversion H; try done.
  1: iExists γ; iSplit; first done; iApply (big_sepM_lookup with "Hχ"); done.
  1: iExists γ, lv1, lv2; iSplit; first done; iSplit. 1: iSplit; last done.
  3-4: iExists γ, lv; iSplit; first done; iSplit; first (iSplit; last done).
  1,3,5: iApply (big_sepM_lookup with "Hζ"); try done.
  4: iSplit.
  4,6,7: iApply "IH". 7: iApply "IH1".
  4-7: iPureIntro; done.
  all: subst.
  1: rename H2 into H1.
  all: pose proof H1 as H1'. 
  all: rewrite lookup_union in H1.
  all: destruct (ζσ !! γ) eqn:Heq; rewrite Heq in H1; unfold union_with in H1; cbn in H1.
  all: destruct (ζrest !! γ) eqn:Heq2; rewrite Heq2 in H1; try congruence.
  1,4,7: exfalso; eapply map_disjoint_spec; done.
  2,4,6: rewrite Heq2; done.
  all: destruct Hstorebl as [Hstorebl1 Hstorebl2].
  all: unfold block in *.
  all: rewrite <- Heq in H1; apply elem_of_dom_2 in Heq; apply Hstorebl2 in Heq.
  all: destruct Heq as (ℓ & Vs & Hχ & Hσml).
  all: unfold is_store in Hstore.
  all: specialize (Hstore _ _ _ _ Hσml Hχ H1').
  all: inversion Hstore.
Qed.

Lemma block_sim_arr_of_ghost_state  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   vs b :
     ([∗ map] ℓ ↦ γ ∈ χvirt, block_sim_raw ℓ γ)
  -∗ ([∗ map] l ↦ bb ∈ ζrest, ⌜mutability bb = Immut⌝ -∗ l ↪[ wrapperGS_γζblock ]□ bb)
  -∗⌜ζfreeze = ζσ ∪ ζrest⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζrest⌝
  -∗⌜Forall2 (is_val χvirt ζfreeze) vs b⌝
  -∗ block_sim_arr vs b.
Proof.
  iIntros "#Hχ #Hζ %Hfreeze %Hstorebl %Hstore %Hdisj %H".
  iApply big_sepL2_intro; first by eapply Forall2_length.
  iIntros "!> %k %v %l %H1 %H2".
  iApply (block_sim_of_ghost_state with "Hχ Hζ"); try done.
  iPureIntro. eapply Forall2_lookup_lr; done.
Qed.

Lemma block_sim_to_ghost_state  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   v b :
     ghost_map_auth wrapperGS_γχmap 1 χvirt
  -∗ ghost_map_auth wrapperGS_γζblock 1 ζrest
  -∗⌜ζfreeze = ζσ ∪ ζrest⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζrest⌝
  -∗ block_sim v b
  -∗⌜is_val χvirt ζfreeze v b⌝.
Proof.
  iIntros "Hχ Hζ %Hfreeze %Hstorebl %Hstore %Hdis Hsim".
  iInduction v as [[x|bo| | |]| | | |] "IH" forall (b); cbn.
  all: try (iPure "Hsim" as Hsim; subst; iPureIntro; try econstructor; done).
  1: {iDestruct "Hsim" as "(%γ & -> & Hsim)". unfold block_sim_raw.
      iPoseProof (ghost_map_lookup with "Hχ Hsim") as "%HH".
      iPureIntro. econstructor. done. }
  1: iDestruct "Hsim" as "(%γ & %lv1 & %lv2 & -> & Hsim & Hlv1 & Hlv2)";
     iPoseProof ("IH" with "Hχ Hζ Hlv1") as "%Hr1";
     iPoseProof ("IH1" with "Hχ Hζ Hlv2") as "%Hr2".
  2-3: iDestruct "Hsim" as "(%γ & %lv & -> & Hsim & Hlv)";
       iPoseProof ("IH" with "Hχ Hζ Hlv") as "%Hr".
  1-3: iDestruct "Hsim" as "(Hsim & _)";
       iPoseProof (@ghost_map_lookup with "Hζ Hsim") as "%HH";
       iPureIntro; econstructor; eauto; subst;
       rewrite lookup_union; rewrite HH;
       destruct (ζσ !! γ) eqn:Heq; rewrite Heq; try done;
       eapply @map_disjoint_spec in Hdis; done.
Qed.

Lemma block_sim_arr_to_ghost_state  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   vs bb :
     ghost_map_auth wrapperGS_γχmap 1 χvirt
  -∗ ghost_map_auth wrapperGS_γζblock 1 ζrest
  -∗⌜ζfreeze = ζσ ∪ ζrest⌝
  -∗⌜is_store_blocks χvirt σMLvirt ζσ⌝
  -∗⌜is_store χvirt ζfreeze σMLvirt⌝
  -∗⌜ζσ ##ₘ ζrest⌝
  -∗ block_sim_arr vs bb
  -∗⌜Forall2 (is_val χvirt ζfreeze) vs bb⌝.
Proof.
  iIntros "Hχ Hζ %Hfreeze %Hstorebl %Hstore %Hdis Hsim".
  iPoseProof (big_sepL2_forall with "Hsim") as "(%Heq & Hsim)".
  iAssert (⌜(∀ i x y, vs !! i = Some x → bb !! i = Some y → is_val χvirt ζfreeze x y)⌝)%I as "%HF".
  2: iPureIntro; by apply Forall2_same_length_lookup_2.
  iIntros (i v b H1 H2).
  iApply (block_sim_to_ghost_state with "Hχ Hζ"); try done.
  iApply ("Hsim" $! i v b H1 H2).
Qed.

Definition SIupt (P:iProp Σ) : iProp Σ := SI -∗ ( |==> SI ∗ P).

Lemma ml_to_mut θ l vs: ⊢ (GC θ ∗ l ↦∗ vs ∗ SI ==∗ SI ∗ GC θ ∗ ∃ b γ, γ ↦mut{DfracOwn 1} (Mut,TagDefault,b) ∗ block_sim_raw l γ ∗ block_sim_arr vs b)%I.
Proof.
  iIntros "(HGC & Hl & Hσ)".
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iDestruct "Hσ" as SIC_ip.
  iDestruct (gen_heap_valid with "HAσMLv Hl") as %Hlσ.
  destruct (χvirt !! l) as [ll|] eqn:Hlχ.
  2: { exfalso. 
       apply not_elem_of_dom_2 in Hlχ.
       apply elem_of_dom_2 in Hlσ.
       destruct Hstore_blocks as [Hdom Hstore_blocks]. unfold lloc_map in Hdom. rewrite <- Hdom in Hlχ.
       by apply Hlχ. }
  iMod (gen_heap_update _ _ _ None with "HAσMLv Hl") as "[HAσMLv Hl]".
  assert (ll ∈ dom ζσ) as Hllζ.
  1: { destruct Hstore_blocks as [Hdom Hstore_blocks]. apply Hstore_blocks. exists l, vs. split; try done. }
  apply elem_of_dom in Hllζ. destruct Hllζ as [bb Hζσll].
  iMod (ghost_map_insert _ bb with "HAζbl") as "(HAζbl & Hzz)".
  1: { eapply map_disjoint_Some_l; done. }
  iModIntro. iFrame "HGC".
  unfold is_store in Hstore.
  assert (ζfreeze !! ll = Some bb) as Hfreezell.
  1: { rewrite Hfreezeeq. rewrite lookup_union. rewrite Hζσll. unfold union_with. cbn.
       destruct (ζrest !! ll) eqn:Heq; rewrite Heq; done. }
  specialize (Hstore l vs ll bb Hlσ Hlχ Hfreezell) as Hstorel.
  inversion Hstorel; subst vs0 bb.
  iAssert (block_sim_arr vs lvs) as "#Hblock".
  1: { iApply (block_sim_arr_of_ghost_state). 1: iApply "HAχpers". 1: iApply "HAζpers". all:done. }
  iAssert (block_sim_raw l ll) as "#Hraw".
  1: iApply (big_sepM_lookup with "HAχpers"); done.
  assert (ζrest !! ll = None) as HζllNone.
  1: eapply map_disjoint_Some_l; done.
  iAssert (⌜gset_bijective (map_to_set pair χvirt)⌝)%I as "%Hbij".
  1: { iPoseProof (own_valid with "HAχbij") as "%Hvalid". apply gset_bij_auth_valid in Hvalid. done. }
  iSplitR "Hzz". 1: iSplitL "HσC".
  + iExists _. iApply "HσC".
  + unfold C_state_interp. iExists (ζfreeze), (delete ll ζσ), (<[ll:=(Mut, TagDefault, lvs)]> ζrest).
    iExists χvirt, fresh, (<[l:=None]> σMLvirt). iFrame. iFrame "HAχpers".
    iSplitL "HAnMLv". 1: iExists _; iFrame.
    iSplitL. 
    1: { rewrite dom_insert_L.
         iApply (big_sepM_insert_inj with "[] [] [] [Hl] HAχNone"). 4: iApply "Hl".
         all: iPureIntro.
         + intros k v1 v2 H1 H2. eapply gset_bijective_eq_iff. 1: done. 1-2: eapply elem_of_map_to_set_pair; done. done.
         + by apply not_elem_of_dom_2.
         + done. }
    iSplitL.
    1: { iApply big_sepM_insert.
         + done.
         + iSplit. 2: iApply "HAζpers". cbn; iIntros "%Hne"; congruence. }
    iPureIntro. split_and!.
    all: eauto.
    - symmetry. subst. by apply union_delete_insert.
    - apply map_disjoint_insert_r_2. 1: apply lookup_delete.
      apply map_disjoint_delete_l. done.
    - destruct Hstore_blocks as [HL HR]. split.
      1: rewrite dom_insert_lookup_L; try done.
      intros ll'. destruct (decide (ll' = ll)); try subst ll'; split.
      * intros [x Hx]%elem_of_dom. rewrite lookup_delete in Hx. done.
      * intros (ℓ & Vs & HH1 & HH2).
        enough (l = ℓ) as <-. 2: eapply gset_bijective_eq_iff. 2: apply Hbij.
        2-3: by apply elem_of_map_to_set_pair. 2: done.
        rewrite lookup_insert in HH2. done.
      * intros [x Hx]%elem_of_dom. rewrite lookup_delete_ne in Hx. 2:done. 
        destruct (HR ll') as [(ℓ & Vs & HH1 & HH2) _].  1: by apply elem_of_dom.
        exists ℓ, Vs. split; first done.
        rewrite lookup_insert_ne; try done. intros Hn.
        eapply (gset_bijective_eq_iff _ _ _ _ _ Hbij) in Hn. 1: apply n; symmetry; apply Hn. 
        all: by apply elem_of_map_to_set_pair.
      * intros (ℓ & Vs & HH1 & HH2). apply elem_of_dom. rewrite lookup_delete_ne; last done.
        apply elem_of_dom.
        destruct (HR ll') as [_ Hdom]. apply Hdom.
        exists ℓ, Vs; split; try done.
        rewrite lookup_insert_ne in HH2; try done. intros Hn.
        eapply (gset_bijective_eq_iff _ _ _ _ _ Hbij) in Hn. 1: apply n; symmetry; apply Hn. 
        all: by apply elem_of_map_to_set_pair.
    - intros ℓ Vs γ blk HH1 HH2 HH3. eapply Hstore; try done. destruct (decide (ℓ = l)).
      1: subst ℓ; rewrite lookup_insert in HH1; done.
      rewrite lookup_insert_ne in HH1; try done.
  + iExists lvs, ll. cbn. iFrame. iFrame "Hblock Hraw". iSplitL; try done.
    iExists _; iApply "Hraw".
Qed.



Lemma mut_to_ml γ vs b θ: ⊢ (SI ∗ GC θ ∗ γ ↦mut{DfracOwn 1} (Mut,TagDefault,b) ∗ block_sim_arr vs b ==∗ SI ∗ GC θ ∗ ∃ l, l ↦∗ vs)%I.
Proof.
  iIntros "(Hσ & HGC & (Hl & (_ & %ℓ & #Hlℓ)) & #Hsim)".
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iDestruct "Hσ" as SIC_ip.
  iPoseProof (block_sim_arr_to_ghost_state with "HAχmap HAζbl [] [] [] [] Hsim ") as "%Hsim".
  1-4: iPureIntro; done.
  iPoseProof (@ghost_map_lookup with "HAχmap Hlℓ") as "%Hχℓ".
  iAssert (⌜gset_bijective (map_to_set pair χvirt)⌝)%I as "%Hbij".
  1: { iPoseProof (own_valid with "HAχbij") as "%Hvalid". apply gset_bij_auth_valid in Hvalid. done. }
  assert (gmap_inj χvirt) as Hinj.
  1: { intros k v1 v2 Hv1 Hv2. eapply Hbij. all: apply elem_of_map_to_set_pair; done. }
  unfold is_store_blocks in Hstore_blocks.
  unfold is_store in Hstore.
  iPoseProof (@ghost_map_lookup with "HAζbl Hl") as "%Hζl".
  iPoseProof (big_sepM_delete_S with "[] [] HAχNone") as "(Hℓ & HAχNone)".
  1: done.
  1: iPureIntro; eapply elem_of_dom_2; done.
  iPoseProof ("Hℓ" $! Hχℓ) as "Hℓ".
  iDestruct (gen_heap_valid with "HAσMLv Hℓ") as "%Hlσ".
  iMod (gen_heap_update _ _ _ (Some vs) with "HAσMLv Hℓ") as "[HAσMLv Hℓ]".
  iMod (ghost_map_delete with "HAζbl Hl") as "HAζbl".
  iModIntro. iFrame "HGC". iSplitR "Hℓ". 2: iExists ℓ; done.
  cbn. iSplitL "HσC".
  1: iExists _; iFrame.
  unfold C_state_interp. unfold lstore.
  iExists ζfreeze, (<[γ:=(Mut, TagDefault, b)]>ζσ), (delete γ ζrest).
  iExists χvirt, fresh, (<[ ℓ := Some vs ]> σMLvirt).
  iFrame. iFrame "HAχpers".
  iSplitL "HAnMLv". 2: iSplitL. 3: iSplitL. 4: iPureIntro; split_and!; eauto.
  + iExists _; done.
  + rewrite dom_delete_L. iFrame.
  + iPoseProof big_sepM_delete as "(HH & _)"; last iPoseProof ("HH" with "HAζpers") as "(_ & HAζpers2)"; done.
  + erewrite @union_insert_delete. 3: eapply map_disjoint_Some_r. 2: apply _. all: done.
  + apply map_disjoint_insert_l_2. 1: apply lookup_delete.
    apply map_disjoint_delete_r. done.
  + destruct Hstore_blocks as [Hsl Hsr]. split. 2: intros γ'; destruct (Hsr γ') as [Hsrl Hsrr]; split.
    * rewrite <- Hsl. apply dom_insert_lookup_L. done.
    * intros Hin. rewrite dom_insert_L in Hin. apply elem_of_union in Hin. destruct Hin as [->%elem_of_singleton|Hin2].
      - exists ℓ, vs. split; try done. by rewrite lookup_insert.
      - destruct (Hsrl Hin2) as (ℓ2 & Vs & H1 & H2); exists ℓ2, Vs; split; try done.
        rewrite lookup_insert_ne; first done; congruence.
    * intros (ℓ2 & Vs & H1 & H2). destruct (decide (ℓ2 = ℓ)) as [->|Hne].
      - rewrite Hχℓ in H1. injection H1; intros ->. rewrite dom_insert_L. apply elem_of_union; left. by apply elem_of_singleton.
      - rewrite dom_insert_L. apply elem_of_union; right. apply Hsrr. eexists _, _; split; try done. rewrite lookup_insert_ne in H2; done.
  + intros ℓ1 vs1 γ1 bl1 Hs1 Hs2 Hs3. destruct (decide (ℓ = ℓ1)) as [<- | Hne].
    * rewrite Hχℓ in Hs2. rewrite lookup_insert in Hs1. rewrite Hfreezeeq in Hs3.
      injection Hs2; intros ->.
      injection Hs1; intros ->.
      apply lookup_union_Some_inv_r in Hs3.
      2: eapply map_disjoint_Some_r; done.
      rewrite Hζl in Hs3. injection Hs3; intros <-. econstructor. done.
    * rewrite lookup_insert_ne in Hs1; last done. eapply Hstore; done.
Qed.

Lemma is_val_mono χ χL ζ ζL x y : χ ⊆ χL -> ζ ⊆ ζL -> is_val χ ζ x y → is_val χL ζL x y.
Proof.
  intros H1 H2; induction 1 in χL,ζL,H1,H2|-*; econstructor; eauto.
  all: eapply lookup_weaken; done.
Qed.

Lemma freeze_to_mut γ bb θ: ⊢ (SI ∗ GC θ ∗ γ ↦fresh{DfracOwn 1} bb ==∗ SI ∗ GC θ ∗ γ ↦mut{DfracOwn 1} bb)%I.
Proof.
  iIntros "(Hσ & HGC & (Hmtζ & Hmtfresh & %Hmut))". 
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iDestruct "Hσ" as SIC_ip.
  iPoseProof (@ghost_map_lookup with "HAζbl Hmtζ") as "%Hζγ".
  iPoseProof (@ghost_map_lookup with "HAfresh Hmtfresh") as "%Hfreshγ".
  pose (fresh_locs (dom χvirt)) as ℓ.
  assert (ℓ ∉ dom χvirt) as Hℓdom.
  1: { epose proof (fresh_locs_fresh (dom χvirt) 0) as Hfresh.
       unfold loc_add in Hfresh. rewrite Z.add_0_r in Hfresh. apply Hfresh. lia. }
  iMod (ghost_map_insert_persist ℓ γ with "HAχmap") as "(HAχmap & #Hℓγ)".
  1: by eapply not_elem_of_dom_1. unfold block_sim_raw.
  iPoseProof big_sepM_insert as "[_ Hr]"; last first.
  1: iPoseProof ("Hr" with "[Hℓγ HAχpers]") as "HAχpers2"; first iSplitL.
  2: iApply "HAχpers". 1: iApply "Hℓγ". 2: by eapply not_elem_of_dom_1.
  iClear "HAχpers". iRename "HAχpers2" into "HAχpers".
  iMod (gen_heap_alloc _ ℓ None with "HAσMLv") as "(HAσMLv & HℓNone & Hmeta)".
  1: eapply not_elem_of_dom_1; by destruct Hstore_blocks as [-> _].
  iPoseProof (big_sepM_insert_M _ _ _ ℓ γ with "[] [HℓNone] HAχNone") as "HAχNone".
  1: iPureIntro; by eapply not_elem_of_dom_1.
  1: iIntros "_"; done.
  iMod (ghost_map_delete with "HAfresh Hmtfresh") as "HAfresh".
  iAssert (|==> own wrapperGS_γχbij (gset_bij_auth (DfracOwn 1) (map_to_set pair (<[ℓ:=γ]> χvirt))))%I with "[HAχbij]" as "HAχbij".
  1: { rewrite map_to_set_insert_L; last by eapply not_elem_of_dom_1.
       iApply (own_update with "HAχbij").
       eapply gset_bij_auth_extend.
       + intros γ' Hγ'%elem_of_map_to_set_pair. apply Hℓdom. by eapply elem_of_dom.
       + intros ℓ' Hℓ'%elem_of_map_to_set_pair. apply (Hfreshχ _ _ Hℓ'). by eapply elem_of_dom. }
  iMod "HAχbij".
  iModIntro.
  iFrame "HGC".
  iSplitR "Hℓγ Hmtζ".
  2: { iFrame. iSplit. 1: done. iExists ℓ. unfold block_sim_raw. iApply "Hℓγ". }
  cbn. iSplitL "HσC"; first (iExists nCv; iFrame).
  unfold C_state_interp. unfold lstore.
  iExists ζfreeze, ζσ, ζrest.
  iExists (<[ℓ:=γ]> χvirt), (delete γ fresh), (<[ ℓ := None ]> σMLvirt).
  iFrame. iFrame "HAχpers HAζpers".
  iSplitL "HAnMLv". 2: iPureIntro; split_and!; eauto.
  + iExists nMLv; done.
  + destruct Hstore_blocks as [Hsl Hsr]; split.
    - rewrite ! dom_insert_L. rewrite Hsl; done.
    - intros γ1; destruct (Hsr γ1) as [Hsrl Hsrr]; split.
      * intros Hin. destruct (Hsrl Hin) as (ℓ1 & Vs & H1 & H2).
        exists ℓ1, Vs. destruct (decide (ℓ1 = ℓ)) as [-> | Hn].
        2: rewrite ! lookup_insert_ne; try done.
        exfalso. apply Hℓdom. by eapply elem_of_dom.
      * intros (ℓ2 & Vs & H1 & H2). destruct (decide (ℓ = ℓ2)) as [<- | Hn].
        1: rewrite lookup_insert in H2; congruence.
        apply Hsrr. exists ℓ2, Vs.
         rewrite lookup_insert_ne in H1; last done.  rewrite lookup_insert_ne in H2; done.
  + intros ℓ1 vs γ1 blk H1 H2 H3. destruct (decide (ℓ = ℓ1)) as [<- | Hn].
    1: rewrite lookup_insert in H1; congruence.
    rewrite lookup_insert_ne in H1; last done. rewrite lookup_insert_ne in H2; last done.
    specialize (Hstore _ _ _ _ H1 H2 H3).
    inversion Hstore; subst.
    econstructor. eapply Forall2_impl; first apply H.
    intros x y Hval. eapply is_val_mono; last done; eauto.
    apply insert_subseteq. by eapply not_elem_of_dom.
  + destruct Hχvirt as [H1 H2]. split.
    - etransitivity; first done.
      eapply insert_subseteq. eapply not_elem_of_dom; done.
    - intros k1 k2 v Hk1 Hk2.
      destruct (decide (k1 = ℓ)) as [-> | Hne1]; destruct (decide (k2 = ℓ)) as [-> | Hne2].
      1: congruence.
      all: rewrite ?lookup_insert in Hk1,Hk2.
      all: rewrite ?lookup_insert_ne in Hk1,Hk2; try done.
      1-2: exfalso; eapply Hfreshχ; first done; eapply elem_of_dom_2 in Hfreshγ; congruence.
      eapply H2; done.
  + intros x y Hxy; destruct (decide (x=ℓ)) as [->|Hne].
    - subst. rewrite lookup_insert in Hxy; injection Hxy; intros ->. rewrite dom_union_L; apply elem_of_union; right. by eapply elem_of_dom.
    - rewrite lookup_insert_ne in Hxy; last done. by eapply Hfreezeχ.
  + intros x y Hxy; destruct (decide (x=ℓ)) as [->|Hne].
    - subst. rewrite lookup_insert in Hxy; injection Hxy; intros ->. intros H%elem_of_dom. rewrite lookup_delete in H. destruct H; congruence.
    - rewrite lookup_insert_ne in Hxy; last done. intros H%elem_of_dom. destruct H as [xx [Hx1 Hx2]%lookup_delete_Some]. eapply Hfreshχ; first done.
      by eapply elem_of_dom.
Qed.

Lemma is_val_insert_immut χ ζ γ bb bb2 x y : ζ !! γ = Some bb2 → mutability bb2 = Mut → is_val χ ζ x y → is_val χ (<[γ := bb]> ζ) x y.
Proof.
  intros H1 H2; induction 1; econstructor; eauto.
  all: rewrite lookup_insert_ne; first done.
  all: intros ->; destruct bb2 as [[mut ?]?]; cbn in *.
  all: subst mut; rewrite H1 in H; congruence.
Qed.

Lemma freeze_to_immut γ bb1 bb2 θ: ⊢ (SI ∗ GC θ ∗ γ ↦fresh{DfracOwn 1} (Mut, bb1, bb2) ==∗ SI ∗ GC θ ∗ γ ↦imm (Immut, bb1, bb2))%I.
Proof.
  iIntros "(Hσ & HGC & (Hmtζ & Hmtfresh & _))". 
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iDestruct "Hσ" as SIC_ip.
  iPoseProof (@ghost_map_lookup with "HAζbl Hmtζ") as "%Hζγ".
  iPoseProof (@ghost_map_lookup with "HAfresh Hmtfresh") as "%Hfreshγ".
  iMod ((ghost_map_update (Immut,bb1,bb2)) with "HAζbl Hmtζ") as "(HAζbl & Hmtζ)".
  iMod (ghost_map_elem_persist with "Hmtζ") as "#Hmtζ".
  iMod (ghost_map_delete with "HAfresh Hmtfresh") as "HAfresh".
  iPoseProof (big_sepM_insert_override_2 with "HAζpers []") as "#HAζpers2"; first done.
  1: iIntros "_ _"; iApply "Hmtζ".
  iClear "HAζpers". iRename "HAζpers2" into "HAζpers".
  iModIntro.
  iFrame "HGC".
  iSplitL.
  2: by iSplit.
  cbn. iSplitL "HσC"; first (iExists nCv; iFrame).
  unfold C_state_interp. unfold lstore.
  iExists (<[γ:=(Immut, bb1, bb2)]> ζfreeze), ζσ, (<[γ:=(Immut, bb1, bb2)]> ζrest).
  iExists χvirt, (delete γ fresh), σMLvirt.
  iFrame. iFrame "HAχpers HAζpers".
  iSplitL "HAnMLv". 2: iSplitL. 3: iPureIntro; split_and!; eauto.
  + iExists nMLv; done.
  + rewrite dom_insert_L. rewrite subseteq_union_1_L. 1:done.
    intros ? ->%elem_of_singleton. by eapply elem_of_dom.
  + destruct Hfreezeρ as [HL HR]. split.
    - rewrite HL. rewrite dom_insert_L. rewrite subseteq_union_1_L. 1:done.
      intros ? ->%elem_of_singleton. subst. rewrite dom_union_L. rewrite elem_of_union. right. eapply elem_of_dom; done.
    - intros γ1 b1 b2 H1 H2. destruct (decide (γ = γ1)) as [<- |H3].
      * rewrite lookup_insert in H2. injection H2; intros <-.
        assert (ζfreeze !! γ = Some (Mut, bb1, bb2)) as H4.
        1: subst; apply lookup_union_Some_r; done.
        specialize (HR γ b1 (Mut, bb1, bb2) H1 H4).
        inversion HR; subst; econstructor.
      * rewrite lookup_insert_ne in H2; last done. by eapply HR.
  + subst. rewrite insert_union_r. 1: done. eapply map_disjoint_Some_l; done.
  + apply map_disjoint_insert_r. split; last done. by eapply map_disjoint_Some_l.
  + intros l vs γ1 bb H1 H2 H3. destruct (decide (γ = γ1)) as [<- | H4].
    * exfalso; eapply Hfreshχ; try done. by eapply elem_of_dom.
    * rewrite lookup_insert_ne in H3; last done.
      specialize (Hstore _ _ _ _ H1 H2 H3).
      inversion Hstore. subst vs0 bb.
      econstructor. eapply Forall2_impl; first done.
      intros x y H5.
      eapply is_val_insert_immut; last done.
      1: subst; rewrite lookup_union_r; first done. 2:done.
      eapply map_disjoint_Some_l; done.
  + intros x y H. rewrite dom_insert_L. apply elem_of_union; right. by eapply Hfreezeχ.
  + intros x y H1 H2. rewrite dom_delete_L in H2. apply elem_of_difference in H2.
    destruct H2; eapply Hfreshχ; done.
  + destruct HGCOK as [H1 H2]; split; first done.
    intros γ1 Hγ. destruct (H2 γ1 Hγ) as (m & tgt & vs & Hfreeze & Hlloc).
    destruct (decide (γ1 = γ)) as [-> | H3].
    * setoid_rewrite lookup_insert. do 3 eexists; split; first done.
      intros γ' H4. eapply Hlloc. subst. eapply lookup_union_Some_r in Hζγ.
      2: done. rewrite Hfreeze in Hζγ. congruence.
    * setoid_rewrite lookup_insert_ne; last done. do 3 eexists; done.
Qed.

End Embed_logic.





















