From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem wrapperstate.
From iris.base_logic.lib Require Export ghost_map ghost_var.
From iris.algebra.lib Require Import excl_auth gset_bij gmap_view.
From iris.algebra Require Import ofe.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation  melocoton.primitive_laws.
From melocoton.interop Require Import linking_wp basics.
Import Wrap.

Class wrapperGS (hlc : has_lc) Σ := WrapperGS {
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
Context {HeapML : heapGS_ML_gen hlc Σ}.
Context {HeapC : heapGS_C_gen hlc Σ}.

Notation MLval := ML_lang.val.
Notation Cval := C_lang.val.

Implicit Types P : iProp Σ.

Context {WGS : wrapperGS hlc Σ}.

Definition GC (θ : addr_map) : iProp Σ := 
     ghost_var wrapperGS_γθ (1/2) θ
   ∗ ghost_var wrapperGS_γat_boundary (1/4) false
   ∗ ∃ (roots : gset addr) (rootsmap : gmap loc lval),
       ghost_var wrapperGS_γroots_set (1/2) roots
     ∗ ghost_map_auth wrapperGS_γroots_map 1 rootsmap
     ∗ ⌜dom rootsmap = roots⌝
     ∗ ⌜roots_are_live θ rootsmap⌝
     ∗ ([∗ map] a ↦ v ∈ rootsmap, (∃ w, a ↦C w)).

Definition block_sim_raw l1 l2 : iProp Σ := (ghost_map_elem (K:=loc) (V:=lloc) wrapperGS_γχmap l1 DfracDiscarded l2).

Definition C_state_interp (ζ : lstore) (χ : lloc_map) (θ : addr_map) (roots : gset addr) : iProp Σ :=
  ∃  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (fresh : gmap lloc unit) (σMLvirt : store),
    ghost_var wrapperGS_γroots_set (1/2) roots
  ∗ ghost_var wrapperGS_γθ (1/2) θ
  ∗ ghost_map_auth wrapperGS_γζblock 1 ζrest
  ∗ (∃ n, state_interp σMLvirt n)
  ∗ own wrapperGS_γχbij (gset_bij_auth (DfracOwn 1) (map_to_set pair χvirt))
  ∗ ghost_map_auth wrapperGS_γχmap 1 χvirt
  ∗ ghost_map_auth wrapperGS_γfresh 1 fresh
  ∗ ([∗ map] ℓ ↦ γ ∈ χvirt, ⌜γ ∈ dom ζrest⌝ -∗ ℓ ↦M/)
  ∗ ([∗ map] ℓ ↦ γ ∈ χvirt, block_sim_raw ℓ γ)
  ∗ ([∗ map] l ↦ bb ∈ ζrest, match bb with  (i,t,b) => ⌜i = Immut⌝ -∗ ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l DfracDiscarded (i,t,b) end)
  ∗ ghost_var wrapperGS_γat_boundary (1/4) false
  ∗⌜freeze_lstore ζ ζfreeze
  ∧ ζfreeze = ζσ ∪ ζrest
  ∧ dom ζσ ## dom ζrest
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

Global Instance ζpers_pers (ζrest : lstore) : Persistent (([∗ map] l ↦ bb ∈ ζrest, match (bb:block) with  (i,t,b) => 
    ⌜i = Immut⌝ -∗ ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l DfracDiscarded (i,t,b) end)).
Proof.
  apply big_sepM_persistent. intros k ((i&t)&b). apply _.
Qed.



Definition ML_state_interp (ζ : lstore) (χ : lloc_map) (roots : roots_map) (memC : memory) : iProp Σ := 
  ∃  (ζσ ζrest : lstore) (fresh : gmap lloc unit) (σCvirt : memory),
    ghost_var wrapperGS_γroots_set (1/2) (dom roots)
  ∗ ghost_var wrapperGS_γθ (1/2) (∅ : addr_map)
  ∗ ghost_map_auth wrapperGS_γζblock 1 ζrest
  ∗ (∃ n, state_interp σCvirt n)
  ∗ own wrapperGS_γχbij (gset_bij_auth (DfracOwn 1) (map_to_set pair χ))
  ∗ ghost_map_auth wrapperGS_γχmap 1 χ
  ∗ ghost_map_auth wrapperGS_γfresh (1/2) fresh
  ∗ ([∗ map] ℓ ↦ γ ∈ χ, ⌜γ ∈ dom ζrest⌝ -∗ ℓ ↦M/)
  ∗ ([∗ map] ℓ ↦ γ ∈ χ, block_sim_raw ℓ γ)
  ∗ ([∗ map] l ↦ bb ∈ ζrest, match bb with  (i,t,b) => ⌜i = Immut⌝ -∗ ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l DfracDiscarded (i,t,b) end)
  ∗ ghost_var wrapperGS_γat_boundary (1/2) true
  ∗⌜ζ = ζσ ∪ ζrest
  ∧ dom ζσ ## dom ζrest
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

Global Program Instance wrapGS :
  mlanguage.weakestpre.mlangGS hlc _ Σ wrap_lang
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

Definition adjoin_mut (m : ismut) (p : tag * list lval) : block := match p with (p1,p2) => (m,p1,p2) end.

Notation "l ↦fresh{ dq } b" := (  ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l dq (adjoin_mut Mut b)
                                ∗ ghost_map_elem (K:=lloc) (V:=unit) wrapperGS_γfresh l dq (()))%I
  (at level 20, format "l  ↦fresh{ dq } b") : bi_scope.
Notation "l ↦mut{ dq } b" := (  ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l dq (adjoin_mut Mut b)
                              ∗ ∃ ll, block_sim_raw ll l)%I
  (at level 20, format "l  ↦mut{ dq } b") : bi_scope.
Notation "l ↦imm b" := (  ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l DfracDiscarded (adjoin_mut Immut b))%I
  (at level 20, format "l  ↦imm b") : bi_scope.

Fixpoint block_sim (v : MLval) (l : lval) : iProp Σ := match v with
  (ML_lang.LitV (ML_lang.LitInt x)) => ⌜l = (Lint x)⌝
| (ML_lang.LitV (ML_lang.LitBool b)) => ⌜l = (Lint (if b then 1 else 0))⌝
| (ML_lang.LitV ML_lang.LitUnit) => ⌜l = (Lint 0)⌝
| (ML_lang.LitV ML_lang.LitPoison) => False
| (ML_lang.LitV (ML_lang.LitLoc ℓ)) => ∃ γ, ⌜l = (Lloc γ)⌝ ∗ block_sim_raw ℓ γ
| (ML_lang.PairV v1 v2) => ∃ γ lv1 lv2, ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (TagDefault, [lv1;lv2]) ∗ block_sim v1 lv1 ∗ block_sim v2 lv2
| (ML_lang.InjLV v) => ∃ γ lv, ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (TagDefault, [lv]) ∗ block_sim v lv
| (ML_lang.InjRV v) => ∃ γ lv, ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (TagInjRV, [lv]) ∗ block_sim v lv 
| (ML_lang.RecV _ _ _) => False end.

Global Instance block_sim_pers v l : Persistent (block_sim v l).
Proof.
  induction v as [[x|b| | |]| | | |] in l|-*; cbn; unshelve eapply (_).
Qed.

Fixpoint block_sim_arr (v:list MLval) (l : list lval) : iProp Σ := match (v,l) with
  (nil,nil) => True
| (v::vr, l::lr) => block_sim v l ∗ block_sim_arr vr lr
| _ => False end.

Global Instance block_sim_arr_pers vl ll : Persistent (block_sim_arr vl ll).
Proof.
  induction vl in ll|-*; destruct ll; cbn; apply _.
Qed.

Context (σ : Wrap.state).
Notation SI := (weakestpre.state_interp σ).


Lemma GC_in_C {θ}: ⊢ (SI -∗ GC θ -∗ ⌜∃ ρc mem, σ = CState ρc mem⌝)%I.
Proof.
  destruct σ. 2: iIntros "_ _"; iPureIntro; do 2 eexists; done.
  iIntros "((%nCv & HσC) & (%ζσ & %ζrest & %fresh & %σCvirt & HH1 & HH2 & HH3 & HH4 & HH5 & HH6 & HH7 & HH8 & HH9 & HH10 & HH11 & HH12 & HH13))".
  iIntros "(HG1 & HG2 & HG3)". iExFalso.
  iAssert (⌜true = false⌝)%I as "%Hdone".
  1: iApply (ghost_var_agree with "HH11 HG2").
  congruence.
Qed.


Lemma block_sim_of_ghost_state  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   v b :
  ( ([∗ map] ℓ ↦ γ ∈ χvirt, block_sim_raw ℓ γ)
  ∗ ([∗ map] l ↦ bb ∈ ζrest, match bb with  (i,t,b) => ⌜i = Immut⌝ -∗ ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l DfracDiscarded (i,t,b) end)
  ∗⌜
  ζfreeze = ζσ ∪ ζrest
∧ is_store_blocks χvirt σMLvirt ζσ
∧ is_store χvirt ζfreeze σMLvirt
∧ is_val χvirt ζfreeze v b⌝
  ) -∗ block_sim v b.
Proof.
  iIntros "(H3 & H4 & %H5 & %H7 & %H8 & %HH)".
  unfold is_store_blocks in H7. unfold is_store in H8.
  iInduction v as [[x|bo| | |]| | | |] "IH" forall (b HH); cbn; inversion HH; try done.
  - iExists _. iSplit; first done. iApply (big_sepM_lookup with "H3"); done.
  - iExists γ, lv1, lv2. iSplit; first done. iSplit.
    * iApply (big_sepM_lookup _ _ _ (Immut, TagDefault, [lv1; lv2]) with "H4").
      eapply lookup_union_Some_inv_r. 3: done. 1: subst; apply H1.
      destruct (ζσ !! γ) eqn:Heq; try done. destruct H7 as [H71 H72].
      apply elem_of_dom_2 in Heq as Heq2. apply H72 in Heq2.
      destruct Heq2 as (ll' & C2 & Heq3 & Heq4).
      specialize (H8 _ _ _ _ Heq4 Heq3 H1). inversion H8.
    * inversion HH; subst. iSplit. 1: iApply ("IH" with "[] H3 H4"); done. iApply ("IH1" with "[] H3 H4"); done.
  - iExists γ, lv. iSplit; first done. iSplit.
    * iApply (big_sepM_lookup _ _ _ (Immut, TagDefault, [lv]) with "H4").
      eapply lookup_union_Some_inv_r. 3: done. 1: subst; apply H0.
      destruct (ζσ !! γ) eqn:Heq; try done. destruct H7 as [H71 H72].
      apply elem_of_dom_2 in Heq as Heq2. apply H72 in Heq2.
      destruct Heq2 as (ll' & C2 & Heq3 & Heq4).
      specialize (H8 _ _ _ _ Heq4 Heq3 H0). inversion H8.
    * iApply ("IH" with "[] H3 H4"); done.
  - iExists γ, lv. iSplit; first done. iSplit.
    * iApply (big_sepM_lookup _ _ _ (Immut, TagInjRV, [lv]) with "H4").
      eapply lookup_union_Some_inv_r. 3: done. 1: subst; apply H0.
      destruct (ζσ !! γ) eqn:Heq; try done. destruct H7 as [H71 H72].
      apply elem_of_dom_2 in Heq as Heq2. apply H72 in Heq2.
      destruct Heq2 as (ll' & C2 & Heq3 & Heq4).
      specialize (H8 _ _ _ _ Heq4 Heq3 H0). inversion H8.
    * iApply ("IH" with "[] H3 H4"); done.
Qed.

Lemma block_sim_arr_of_ghost_state  (ζfreeze ζσ ζrest : lstore) (χvirt : lloc_map) (σMLvirt : store)
   vs b :
  ( ([∗ map] ℓ ↦ γ ∈ χvirt, block_sim_raw ℓ γ)
  ∗ ([∗ map] l ↦ bb ∈ ζrest, match bb with  (i,t,b) => ⌜i = Immut⌝ -∗ ghost_map_elem (K:=lloc) (V:=block) wrapperGS_γζblock l DfracDiscarded (i,t,b) end)
  ∗⌜
  ζfreeze = ζσ ∪ ζrest
∧ is_store_blocks χvirt σMLvirt ζσ
∧ is_store χvirt ζfreeze σMLvirt
∧ Forall2 (is_val χvirt ζfreeze) vs b⌝
  ) -∗ block_sim_arr vs b.
Proof.
  iIntros "(H3 & H4 & %H5 & %H7 & %H8 & %H1)".
  unfold is_store_blocks in H7. unfold is_store in H8.
  iInduction vs as [|v vs] "IH" forall (b H1).
  1: apply Forall2_nil_inv_l in H1 as ->; done.
  destruct b as [|b bs]. 1: by apply Forall2_cons_nil_inv in H1.
  destruct (Forall2_cons_1 _ _ _ _ _ H1) as [HH H1']. cbn.
  iSplit.
  + iApply (block_sim_of_ghost_state with "[H3 H4]"). iFrame. iPureIntro. split; first apply H5. split; first apply H7. split; try done.
  + iApply ("IH" with "[] H3 H4"); done.
Qed.

Lemma ml_to_mut θ l vs: ⊢ (SI ∗ GC θ ∗ l ↦∗ vs ==∗ SI ∗ GC θ ∗ ∃ b γ, γ ↦mut{DfracOwn 1} (TagDefault,b) ∗ block_sim_raw l γ ∗ block_sim_arr vs b)%I.
Proof.
  iIntros "(Hσ & HGC & Hl)".
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iDestruct "Hσ" as SIC_ip.
  unfold state_interp. cbn.
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
  1: { edestruct @elem_of_disjoint as [eodj _]. specialize (eodj Hfreezedj).
       apply not_elem_of_dom. refine (eodj ll _). apply elem_of_dom. done. }
  iModIntro. iFrame "HGC".
  unfold is_store in Hstore.
  assert (ζfreeze !! ll = Some bb) as Hfreezell.
  1: { rewrite Hfreezeeq. rewrite lookup_union. rewrite Hζσll. unfold union_with. cbn.
       destruct (ζrest !! ll) eqn:Heq; rewrite Heq; done. }
  specialize (Hstore l vs ll bb Hlσ Hlχ Hfreezell) as Hstorel.
  inversion Hstorel; subst vs0 bb.
  iAssert (block_sim_arr vs lvs) as "#Hblock".
  1: { iApply (block_sim_arr_of_ghost_state). iSplitR; first iApply "HAχpers". iSplitR; first iApply "HAζpers".
       iPureIntro. split; first apply Hfreezeeq. split; first eauto. split; eauto. }
  iAssert (block_sim_raw l ll) as "#Hraw".
  1: iApply (big_sepM_lookup with "HAχpers"); done.
  iAssert (⌜gset_bijective (map_to_set pair χvirt)⌝)%I as "%Hbij".
  1: { iPoseProof (own_valid with "HAχbij") as "%Hvalid". apply gset_bij_auth_valid in Hvalid. done. }
  iSplitR "Hzz". 1: iSplitL "HσC".
  + iExists _. iApply "HσC".
  + unfold C_state_interp. iExists (ζfreeze), (delete ll ζσ), (<[ll:=(Mut, TagDefault, lvs)]> ζrest).
    iExists χvirt, fresh, (<[l:=None]> σMLvirt). iFrame.
    iSplitL "HAnMLv". 1: iExists _; iFrame.
    iSplitL. 
    1: {assert (χvirt = <[ l := ll ]> (delete l χvirt)) as Hχeq.
        + apply map_eq_iff. intros i. destruct (decide (i = l)); subst. 1: by rewrite lookup_insert.
          rewrite lookup_insert_ne. 1: rewrite lookup_delete_ne. all: done.
        + iPoseProof (big_sepM_delete _ _ _ _ Hlχ) as "(Hdel & _)". iPoseProof ("Hdel" with "HAχNone") as "(_ & Hdel')".
          rewrite {5} Hχeq. iApply (big_sepM_insert_2 with "[Hl]"). 1: iIntros "_"; done.
          iApply (big_sepM_impl with "Hdel'"). iIntros "%k %v %Hdeleq !>  Hin %Hdom".
          iApply "Hin". iPureIntro. apply elem_of_dom. apply elem_of_dom in Hdom. destruct Hdom as [x Hx]. destruct (decide (v = ll)).
          2: exists x; rewrite lookup_insert_ne in Hx; done.
          subst v. apply lookup_delete_Some in Hdeleq. destruct Hdeleq as [Hdelne Hkχ].
          enough (l = k) by congruence. eapply gset_bijective_eq_iff. 1: apply Hbij.
          1-2: by apply elem_of_map_to_set_pair. done. 
        }
    iSplitL; first iApply "HAχpers". iSplitL.
    1: { iApply big_sepM_insert.
         + apply not_elem_of_dom. apply elem_of_dom_2 in Hζσll.
           edestruct @elem_of_disjoint as [eodj _]. specialize (eodj Hfreezedj).
           exact (eodj _ Hζσll).
         + iSplit. 2: iApply "HAζpers". iIntros "%Hne"; congruence. }
    iPureIntro. split; last split; last split; last split; last split; last split; last split; last split; last split.
    all: try done; eauto.
    - symmetry. subst. by apply union_delete_insert.
    - apply map_disjoint_dom_1. apply map_disjoint_insert_r_2. 1: apply lookup_delete.
      apply map_disjoint_delete_l. apply map_disjoint_dom_2. done.
    - destruct Hstore_blocks as [HL HR]. split.
      1: rewrite dom_insert_lookup_L; try done. intros ll'.
      destruct (decide (ll' = ll)); try subst ll'; split.
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
  + iExists lvs, ll. iFrame. iFrame "Hblock". unfold block_sim_raw.
    iSplit; first iExists l. all: iApply  "Hraw".
Qed.

End Embed_logic.





















