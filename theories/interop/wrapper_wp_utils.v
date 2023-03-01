From Coq Require Import ssreflect.
From stdpp Require Import strings gmap list.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem basics_resources wrapperstate.
From iris.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra Require Import gset gset_bij.
From melocoton Require Import big_sepM_limited.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.interop Require Import linking_wp basics prims wrapper_wp wrapper_wp_block_sim.
Import Wrap.


Global Notation MLval := ML_lang.val.
Global Notation Cval := C_lang.val.


Section Utils.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Implicit Types P : iProp Σ.
Import mlanguage.
Notation mkPeC p T := ({| penv_prog := p; penv_proto := T |} : prog_environ _ Σ).
Notation mkPeW p T := ({| weakestpre.penv_prog := p; weakestpre.penv_proto := T |} : weakestpre.prog_environ wrap_lang Σ).

(* TODO: auxiliary definition? *)
Notation prim_proto := (prim -d> list Cval -d> (Cval -d> iPropO Σ) -d> iPropO Σ).
Notation C_proto := (string -d> list Cval -d> (Cval -d> iPropO Σ) -d> iPropO Σ).
Notation ML_proto := (string -d> list MLval -d> (MLval -d> iPropO Σ) -d> iPropO Σ).

(* TODO: move *)
Definition wrap_proto (T : ML_proto) : C_proto := (λ f ws Φ,
  ∃ θ vs lvs ψ,
    "HGC" ∷ GC θ ∗
    "%Hrepr" ∷ ⌜Forall2 (repr_lval θ) lvs ws⌝ ∗
    "Hsim" ∷ block_sim_arr vs lvs ∗
    "Hproto" ∷ T f vs ψ ∗
    "Cont" ∷ (∀ θ' vret lvret wret,
      GC θ' -∗
      ψ vret -∗
      block_sim vret lvret -∗
      ⌜repr_lval θ' lvret wret⌝ -∗
      Φ wret)
)%I.

Definition wrap_penv (pe : prog_environ ML_lang Σ) :
  mlanguage.weakestpre.prog_environ wrap_lang Σ
:=
  {| weakestpre.penv_prog := prims_prog;
     weakestpre.penv_proto := wrap_proto (penv_proto pe) |}.

Definition proto_int2val : prim_proto := (λ p vl Φ,
   ∃ θ z,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜p = Pint2val⌝ ∗
     "->" ∷ ⌜vl = [C_lang.LitV $ C_lang.LitInt $ z]⌝ ∗
     "Cont" ∷ (∀ w, GC θ -∗ ⌜repr_lval θ (Lint z) w⌝ -∗ Φ w))%I.

Definition proto_val2int : prim_proto := (λ p vl Φ,
   ∃ θ w z,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜p = Pval2int⌝ ∗
     "->" ∷ ⌜vl = [ w ]⌝ ∗
     "%Hrepr" ∷ ⌜repr_lval θ (Lint z) w⌝ ∗
     "Cont" ∷ (GC θ -∗ Φ (C_lang.LitV $ C_lang.LitInt $ z)))%I.

Definition proto_registerroot : prim_proto := (λ p vl Φ,
   ∃ θ l v w,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜p = Pregisterroot⌝ ∗
     "->" ∷ ⌜vl = [ C_lang.LitV $ C_lang.LitLoc $ l ]⌝ ∗
     "Hpto" ∷ l ↦C w ∗
     "%Hrepr" ∷ ⌜repr_lval θ v w⌝ ∗
     "Cont" ∷ (GC θ -∗ l ↦roots v -∗ Φ (C_lang.LitV $ C_lang.LitInt $ 0)))%I.

Definition proto_unregisterroot : prim_proto := (λ p vl Φ,
   ∃ θ l v,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜p = Punregisterroot⌝ ∗
     "->" ∷ ⌜vl = [ C_lang.LitV $ C_lang.LitLoc $ l ]⌝ ∗
     "Hpto" ∷ l ↦roots v ∗
     "Cont" ∷ (∀w, GC θ -∗ l ↦C w -∗ ⌜repr_lval θ v w⌝ -∗ Φ (C_lang.LitV $ C_lang.LitInt $ 0)))%I.

(* The most general spec, prove stuff for specific block-level pointstos later *)
Definition proto_modify : prim_proto := (λ p vl Φ,
  ∃ θ w i v' w' γ tg vs,
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜p = Pmodify⌝ ∗
    "->" ∷ ⌜vl = [ w; C_lang.LitV $ C_lang.LitInt $ i; w' ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hpto" ∷ lstore_own_mut wrapperGS_γζvirt γ (DfracOwn 1) (Bvblock (Mut, (tg, vs))) ∗
    "%Hreprw'" ∷ ⌜repr_lval θ v' w'⌝ ∗
    "%Hi1" ∷ ⌜0 ≤ i⌝%Z ∗
    "%Hi2" ∷ ⌜i < length vs⌝%Z ∗
    "Cont" ∷ (GC θ -∗
              lstore_own_mut wrapperGS_γζvirt γ (DfracOwn 1) (Bvblock (Mut, (tg, <[Z.to_nat i:=v']> vs))) -∗
              Φ (C_lang.LitV $ C_lang.LitInt $ 0)))%I.

(* The most general spec, prove stuff for specific block-level pointstos later *)
Definition proto_readfield : prim_proto := (λ p vl Φ,
   ∃ θ w i γ dq m tg vs,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜p = Preadfield⌝ ∗
     "->" ∷ ⌜vl = [ w; C_lang.LitV $ C_lang.LitInt $ i ]⌝ ∗
     "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
     "Hpto" ∷ lstore_own_elem wrapperGS_γζvirt γ dq (Bvblock (m, (tg, vs))) ∗
     "%Hi1" ∷ ⌜0 ≤ i⌝%Z ∗
     "%Hi2" ∷ ⌜i < length vs⌝%Z ∗
     "Cont" ∷ (∀ v' w', GC θ -∗
                        lstore_own_elem wrapperGS_γζvirt γ dq (Bvblock (m, (tg, vs))) -∗
                        ⌜vs !! (Z.to_nat i) = Some v'⌝ -∗
                        ⌜repr_lval θ v' w'⌝ -∗
                        Φ w'))%I.

Definition proto_callback (pe : prog_environ ML_lang Σ) (E : coPset) : prim_proto := (λ p vl Φ,
  ∃ θ w γ w' lv' v' f x e ψ,
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜p = Pcallback⌝ ∗
    "->" ∷ ⌜vl = [ w; w' ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hclos" ∷ γ ↦clos (f, x, e) ∗
    "%Hreprw'" ∷ ⌜repr_lval θ lv' w'⌝ ∗
    "Hsim'" ∷ block_sim v' lv' ∗
    "WPcallback" ∷ WP (App (Val (RecV f x e)) (Val v')) @ pe; E {{ ψ }} ∗
    "Cont" ∷ (∀ θ' vret lvret wret,
                GC θ' -∗
                ψ vret -∗
                block_sim vret lvret -∗
                ⌜repr_lval θ' lvret wret⌝ -∗
                Φ wret))%I.

(* non-callbacks primitives *)
Definition proto_base_prims : prim_proto := (λ p vl Φ,
    proto_int2val p vl Φ ∨ proto_val2int p vl Φ ∨ proto_registerroot p vl Φ ∨ proto_unregisterroot p vl Φ
  ∨ proto_modify p vl Φ ∨ proto_readfield p vl Φ)%I.

Definition proto_prims pe E : prim_proto := (λ p vl Φ,
  proto_base_prims p vl Φ ∨ proto_callback pe E p vl Φ)%I.

(*
Lemma WP_ext_call_sound s v2 T : WP_ext_call_spec s v2 T -∗ ⌜s ∈ forbidden_function_names⌝.
Proof.
  iIntros "[H|[H|[H|[H|[H|H]]]]]";
  unfold WP_int2val_spec; unfold WP_val2int_spec; unfold WP_registerroot_spec; unfold WP_unregisterroot_spec;
  unfold WP_modify_spec; unfold WP_readfield_spec;
  iNamed "H"; iPureIntro; unfold forbidden_function_names;
  repeat (try done; try left; right).
Qed.
*)

(* Notation wrap_return := (fun Φ (a:Cval) => (∃ θ' l v, GC θ' ∗ Φ v ∗ ⌜repr_lval θ' l a⌝ ∗ block_sim v l)%I). *)

Section RootsRepr.

(* We can decompose mem, the C heap, into a privmem, which is everything but the roots, and a memr, which are just the rooted cells *)
Lemma make_repr θ roots_m mem : 
    roots_are_live θ roots_m
 -> map_Forall (λ k v, ∃ w , mem !! k = Some (Storing w) ∧ repr_lval θ v w) roots_m
 -> ∃ privmem, repr θ roots_m privmem mem.
Proof.
  revert mem.
  induction roots_m as [|l a roots_m Hin IH] using map_ind; intros mem Hlive Hforall.
  + exists mem, ∅. split_and!.
    * econstructor.
    * eapply map_disjoint_empty_r.
    * by rewrite map_empty_union.
  + apply map_Forall_insert_1_1 in Hforall as Hforall2.
    destruct Hforall2 as (w & Hw & Hrep).
    specialize (IH (delete l mem)).
    destruct IH as (privmem & memr & IH & Hdisj & Hunion).
    1: intros l' g Hg; eapply Hlive; rewrite lookup_insert_ne; first done; intros ->; rewrite Hg in Hin; congruence.
    1: apply map_Forall_lookup; intros i x Hinix;
       eapply map_Forall_lookup_1 in Hforall.
    1: destruct Hforall as (w' & H1 & H2); exists w'; repeat split; try done.
    1: rewrite lookup_delete_ne; first done.
    2: rewrite lookup_insert_ne; first done.
    1-2: intros ->; rewrite Hin in Hinix; congruence.
    assert (memr !! l = None) as HNone1.
    1: apply not_elem_of_dom; erewrite <- repr_roots_dom; last done; by eapply not_elem_of_dom.
    assert (privmem !! l = None) as Hnone2.
    rewrite <- (lookup_union_r memr privmem); try done; rewrite <- Hunion; by apply lookup_delete.
    eexists privmem, (<[l:=Storing w]> memr). split_and!.
    * econstructor; try done; by eapply not_elem_of_dom.
    * by apply map_disjoint_insert_r.
    * erewrite <- insert_union_l. rewrite <- Hunion. rewrite insert_delete_insert.
      apply map_eq_iff. intros i. destruct (decide (i = l)) as [-> |]; (try by rewrite lookup_insert); by rewrite lookup_insert_ne.
Qed.

Lemma set_to_none θ mem roots_m privmem :
    repr θ roots_m privmem mem
 -> gen_heap_interp mem
 -∗ ([∗ map] a0↦v0 ∈ roots_m, ∃ w, a0 ↦C{DfracOwn 1} w ∗ ⌜repr_lval θ v0 w⌝)
==∗ (gen_heap_interp (privmem ∪ ((λ _ : lval, None) <$> roots_m))
    ∗[∗ set] a0 ∈ dom roots_m, a0 O↦ None).
Proof.
  intros (mm & Hrepr1 & Hrepr2 & Hrepr3).
  induction Hrepr1 in Hrepr2,Hrepr3,mem,privmem|-*.
  + iIntros "Hheap Hmap !>".
    rewrite fmap_empty. rewrite dom_empty_L. rewrite map_union_empty.
    rewrite map_empty_union in Hrepr3. subst mem. iFrame.
    iApply big_sepS_empty. done.
  + eapply not_elem_of_dom in H0,H1. iIntros "Hheap Hmap".
    iPoseProof (big_sepM_insert) as "(Hb1 & _)"; first apply H0.
    iPoseProof ("Hb1" with "Hmap") as "((%w' & Hw & %Hrepr4) & Hmap)".
    repr_lval_inj.
    iMod (gen_heap_update with "Hheap Hw") as "(Hheap & Hw)".
    specialize (IHHrepr1 (<[a:=None]> mem) (<[a:=None]> privmem)).
    iMod (IHHrepr1 with "Hheap Hmap") as "(Hheap & Hmap)".
    * eapply map_disjoint_insert_l_2; first done.
      erewrite <- (delete_insert mem0); last done.
      by eapply map_disjoint_delete_r.
    * subst mem. erewrite <- insert_union_l.
      rewrite insert_insert. by rewrite insert_union_r.
    * iModIntro. iSplitL "Hheap".
      - erewrite <- insert_union_l. rewrite insert_union_r.
        2: eapply map_disjoint_Some_r; try done; by rewrite lookup_insert.
        rewrite fmap_insert. iFrame.
      - rewrite dom_insert_L. iApply big_sepS_insert; first by eapply not_elem_of_dom. iFrame.
Qed.

Lemma find_repr_lval_vv θ v : 
   (forall γ, Lloc γ = v → γ ∈ dom θ)
 → exists l, repr_lval θ v l.
Proof.
  intros H. destruct v as [z|a].
  - eexists; by econstructor.
  - destruct (θ !! a) as [va|] eqn:Heq.
    2: eapply not_elem_of_dom in Heq; exfalso; apply Heq; apply H; done.
    eexists; econstructor; apply Heq.
Qed.

Lemma find_repr_lval_vs θ vs : 
   (forall γ, Lloc γ ∈ vs → γ ∈ dom θ)
 → exists ls, Forall2 (repr_lval θ) vs ls.
Proof.
  intros H; induction vs as [|v vs IH] in H|-*.
  - exists nil. econstructor.
  - destruct IH as [ls IH]; first (intros γ Hγ; eapply H; right; done).
    destruct (find_repr_lval_vv θ v) as [l Hl].
    1: intros γ <-; apply H; by left.
    eexists. econstructor; done.
Qed.

Lemma find_repr_roots θ roots privmem : 
   roots_are_live θ roots
 → dom privmem ## dom roots
 → exists mem, repr θ roots privmem mem.
Proof.
  revert privmem. unfold repr.
  induction roots as [|l a roots_m Hin IH] using map_ind; intros privmem Hlive Hdisj.
  - exists privmem, ∅. split_and!.
    + econstructor.
    + eapply map_disjoint_empty_r.
    + by rewrite map_empty_union.
  - destruct (IH privmem) as (mem1 & memr1 & Hrepr1 & Hdisj1 & Heq1).
    1: { intros a1 w1 H1; eapply Hlive; rewrite lookup_insert_ne; first done.
         intros ->; rewrite Hin in H1; congruence. }
    1: rewrite dom_insert_L in Hdisj; set_solver.
    destruct (find_repr_lval_vv θ a) as (w & Hw).
    1: intros γ <-; eapply Hlive; apply lookup_insert.
    exists (<[l:=Storing w]> mem1), (<[l:=Storing w]> memr1). split_and!.
    + econstructor. 1: done. 1:done. 2: erewrite <- repr_roots_dom; last apply Hrepr1. all: by eapply not_elem_of_dom.
    + apply map_disjoint_dom in Hdisj1. apply map_disjoint_dom.
      rewrite dom_insert_L. rewrite dom_insert_L in Hdisj. set_solver.
    + erewrite Heq1. now rewrite insert_union_l.
Qed.


Lemma set_to_some θ mem roots_m privmem :
    repr θ roots_m privmem mem
 -> gen_heap_interp (privmem ∪ ((λ _ : lval, None) <$> roots_m))
 -∗ ([∗ set] a ∈ dom roots_m, a O↦ None)
 ==∗ gen_heap_interp mem
     ∗ ([∗ map] a↦v ∈ roots_m, ∃ w, a ↦C{DfracOwn 1} w ∗ ⌜repr_lval θ v w⌝).
Proof.
  intros (mm & Hrepr1 & Hrepr2 & Hrepr3).
  induction Hrepr1 in Hrepr2,Hrepr3,mem,privmem|-*.
  + iIntros "Hheap Hset !>".
    rewrite fmap_empty. rewrite dom_empty_L. rewrite map_union_empty.
    rewrite map_empty_union in Hrepr3. subst mem. iFrame.
    iApply big_sepM_empty. done.
  + eapply not_elem_of_dom in H0,H1. iIntros "Hheap Hset".
    rewrite dom_insert_L.
    iPoseProof (big_sepS_insert) as "(Hb1 & _)"; first eapply not_elem_of_dom_2, H0.
    iPoseProof ("Hb1" with "Hset") as "(Hw & Hset)".
    rewrite fmap_insert. rewrite <- insert_union_r.
    2: eapply map_disjoint_Some_r; first done; by rewrite lookup_insert.
    iMod (gen_heap_update _ _ _ (Storing w) with "Hheap Hw") as "(Hheap & Hw)".
    rewrite insert_insert.
    rewrite insert_union_l.
    iMod (IHHrepr1 with "Hheap Hset") as "(Hheap & Hset)".
    * eapply map_disjoint_insert_l_2; first done.
      erewrite <- (delete_insert mem0); last done.
      by eapply map_disjoint_delete_r.
    * done.
    * rewrite <- insert_union_r; last done.
      subst mem. rewrite insert_union_l. iModIntro.
      iFrame.
      iApply (big_sepM_insert_2 with "[Hw] Hset").
      iExists w. iFrame. done.
Qed.

End RootsRepr.

Section ChiZetaConstruction.

Definition lookup_reversed (χ : lloc_map) ℓ := {γ | χ !! γ = Some (LlocPublic ℓ)}.

Definition find_in_χ (χ:lloc_map) ℓ : sum (lookup_reversed χ ℓ) (lookup_reversed χ ℓ -> False).
Proof.
  pose (map_to_set (fun γ ll => match ll with LlocPrivate => None | LlocPublic ℓ' => if decide (ℓ' = ℓ) then Some γ else None end) χ : gset _) as Hset.
  epose (filter (fun k => is_Some (k)) Hset) as Hset2.
  destruct (elements Hset2) as [|[γ|] ?] eqn:Heq.
  - right. intros (γ & Hγ).
    apply elements_empty_inv in Heq. apply gset_leibniz in Heq.
    eapply filter_empty_not_elem_of_L. 2: apply Heq. 1: apply _.
    2: eapply elem_of_map_to_set.
    2: exists γ, (LlocPublic ℓ); split; done.
    rewrite decide_True; done. Unshelve. all: apply _.
  - left. exists γ.
    assert (Some γ ∈ Hset2).
    1: eapply elem_of_elements; rewrite Heq; left.
    eapply elem_of_filter in H. destruct H as [_ H].
    eapply elem_of_map_to_set in H.
    destruct H as (i & ll & H1 & H2).
    destruct ll; try congruence.
    destruct decide; try congruence.
  - exfalso. assert (None ∈ Hset2).
    + eapply elem_of_elements. rewrite Heq. left.
    + apply elem_of_filter in H. destruct H as [[? Hc]?]. congruence.
Defined.

Lemma ensure_in_χ_pub χ ℓ : lloc_map_inj χ → exists χ' γ, lloc_map_mono χ χ' ∧ χ' !! γ = Some (LlocPublic ℓ) ∧ ∀ γ' r, γ' ≠ γ → χ' !! γ' = r → χ !! γ' = r.
Proof.
  intros Hinj.
  destruct (find_in_χ χ ℓ) as [[γ Hgam]|Hnot].
  1: exists χ, γ; done.
  eexists (<[fresh (dom χ) := LlocPublic ℓ]> χ), _.
  erewrite lookup_insert; split_and!. 2: done.
  2: intros γ' r Hne H1; by rewrite lookup_insert_ne in H1.
  split.
  1: eapply insert_subseteq, not_elem_of_dom, is_fresh.
  intros γ1 γ2 ℓ' [[? ?]|[? ?]]%lookup_insert_Some [[? ?]|[? ?]]%lookup_insert_Some; subst.
  1: done.
  3: by eapply Hinj.
  all: exfalso; eapply Hnot; eexists _; erewrite H0, H2; done.
Qed.

Definition extended_to (χold : lloc_map) (ζ : lstore) (χnew : lloc_map) :=
  lloc_map_mono χold χnew ∧ dom χold ## dom ζ ∧ is_private_blocks χnew ζ.

Lemma extended_to_inj χ1 ζ χ2 : extended_to χ1 ζ χ2 → lloc_map_inj χ2.
Proof.
  intros (H&_); apply H.
Qed.

Lemma extended_to_dom_subset χ1 ζ χ2 : extended_to χ1 ζ χ2 → dom ζ ⊆ dom χ2.
Proof.
  intros (H1&H2&H3).
  eapply elem_of_subseteq. intros γ Hx; eapply elem_of_dom_2. by apply H3.
Qed.

Definition allocate_in_χ_priv (χold : lloc_map) v : lloc_map_inj χold → exists χnew γ, extended_to χold {[γ := v]} χnew.
Proof.
  intros Hinj.
  eexists (<[fresh (dom χold) := LlocPrivate]> χold), (fresh (dom χold)).
  unfold extended_to; split_and!; first split.
  - eapply insert_subseteq, not_elem_of_dom, is_fresh.
  - intros γ1 γ2 ℓ' [[? ?]|[? ?]]%lookup_insert_Some [[? ?]|[? ?]]%lookup_insert_Some; subst; try congruence.
    by eapply Hinj.
  - rewrite dom_singleton_L. eapply disjoint_singleton_r. by apply is_fresh.
  - intros x. rewrite dom_singleton_L. intros ->%elem_of_singleton.
    eapply lookup_insert.
Qed.

Lemma disjoint_weaken T `{Countable T} (A1 A2 B1 B2 : gset T) : A1 ## B1 → A2 ⊆ A1 → B2 ⊆ B1 → A2 ## B2.
Proof.
  intros HD H1 H2.
  apply elem_of_disjoint.
  intros x HA HB.
  edestruct (@elem_of_disjoint) as [HL _]; eapply HL.
  - apply HD.
  - eapply elem_of_weaken; first apply HA. done.
  - eapply elem_of_weaken; first apply HB. done.
Qed.

Lemma extended_to_trans (χ1 χ2 χ3 : lloc_map) (ζ1 ζ2 : lstore) : 
  extended_to χ1 ζ1 χ2 →
  extended_to χ2 ζ2 χ3 →
  extended_to χ1 (ζ1 ∪ ζ2) χ3 /\ ζ1 ##ₘ ζ2.
Proof.
  intros (HA1 & HA2 & HA3) (HB1 & HB2 & HB3). unfold extended_to; split_and!.
  - split; last apply HB1. etransitivity; first apply HA1; apply HB1.
  - erewrite dom_union_L. eapply disjoint_union_r. split; first done.
    eapply disjoint_weaken. 1: apply HB2. 2: done. apply subseteq_dom, HA1.
  - intros γ. rewrite dom_union_L. intros [H|H]%elem_of_union; last by apply HB3.
    eapply lookup_weaken; first by apply HA3.
    apply HB1.
  - eapply map_disjoint_dom. eapply disjoint_weaken. 1: apply HB2. 2: done.
    eapply extended_to_dom_subset; done.
Qed.

Lemma extended_to_trans_2 (χ1 χ2 χ3 : lloc_map) (ζ1 ζ2 : lstore) : 
  extended_to χ1 ζ1 χ2 →
  extended_to χ2 ζ2 χ3 →
  extended_to χ1 (ζ2 ∪ ζ1) χ3 /\ ζ1 ##ₘ ζ2.
Proof.
  intros H1 H2.
  destruct (extended_to_trans χ1 χ2 χ3 ζ1 ζ2) as (H3&H4). 1-2: done.
  erewrite map_union_comm; done.
Qed.

Lemma extended_to_refl χ1 :
  lloc_map_inj χ1 →
  extended_to χ1 ∅ χ1.
Proof.
  by repeat split.
Qed.

Lemma extended_to_mono χ1 χ2 :
  lloc_map_mono χ1 χ2 →
  extended_to χ1 ∅ χ2.
Proof.
  intros (H1 & H2); by repeat split.
Qed.

Lemma is_val_extended_to_weaken χ1 χ2 ζ1 ζ2 v lv:
  is_val χ1 ζ1 v lv →
  extended_to χ1 ζ2 χ2 →
  is_val χ2 (ζ1 ∪ ζ2) v lv.
Proof.
  intros H1 (H21&H22&H23).
  eapply is_val_mono; last done.
  1: apply H21.
  apply map_union_subseteq_l.
Qed.

Lemma deserialize_ML_value χMLold v :  
  lloc_map_inj χMLold
→ ∃ χC ζimm lv,
    extended_to χMLold ζimm χC
  ∧ is_val χC ζimm v lv.
Proof.
  induction v as [[x|bo| |ℓ]| |v1 IHv1 v2 IHv2|v IHv|v IHv] in χMLold|-*; intros Hinj.
  1-3: eexists χMLold, ∅, _; split_and!; [by eapply extended_to_refl | econstructor ].
  - destruct (ensure_in_χ_pub χMLold ℓ) as (χ' & γ & Hχ' & Hγ & _); first done.
    exists χ', ∅, (Lloc γ); (split_and!; last by econstructor).
    by eapply extended_to_mono.
  - destruct (allocate_in_χ_priv χMLold (Bclosure f x e)) as (χ & γ & Hextend); first done.
    eexists _, _, (Lloc γ). split; eauto. econstructor. by simplify_map_eq.
  - destruct (IHv1 χMLold) as (χ1 & ζ1 & lv1 & Hext1 & Hlv1); first done.
    destruct (IHv2 χ1) as (χ2 & ζ2 & lv2 & Hext2 & Hlv2); first by eapply extended_to_inj.
    pose (Bvblock (Immut,(TagDefault,[lv1;lv2]))) as blk.
    edestruct (allocate_in_χ_priv χ2 blk) as (χ3 & γ & Hext3); first by eapply extended_to_inj.
    eassert (extended_to χMLold _ χ3).
    1: do 2 (eapply extended_to_trans; last done); done.
    do 3 eexists; split; first done.
    econstructor.
    + rewrite lookup_union_r; first by erewrite lookup_singleton.
      eapply map_disjoint_Some_r. 1: eapply extended_to_trans_2; first eapply extended_to_trans; done.
      apply lookup_singleton.
    + eapply is_val_extended_to_weaken; last done.
      eapply is_val_extended_to_weaken; done.
    + eapply is_val_extended_to_weaken; last done.
      eapply is_val_mono; last done; try done.
      eapply map_union_subseteq_r. eapply extended_to_trans; done.
  - destruct (IHv χMLold) as (χ1 & ζ1 & lv1 & Hext1 & Hlv1); first done.
    epose (Bvblock (Immut,(_,[lv1]))) as blk.
    edestruct (allocate_in_χ_priv χ1 blk) as (χ3 & γ & Hext3); first by eapply extended_to_inj.
    eassert (extended_to χMLold _ χ3).
    1: (eapply extended_to_trans; last done); done.
    do 3 eexists; split; first done.
    econstructor.
    + rewrite lookup_union_r; first by erewrite lookup_singleton.
      eapply map_disjoint_Some_r. 1: eapply extended_to_trans_2; done.
      apply lookup_singleton.
    + eapply is_val_extended_to_weaken; done.
  - destruct (IHv χMLold) as (χ1 & ζ1 & lv1 & Hext1 & Hlv1); first done.
    epose (Bvblock (Immut,(_,[lv1]))) as blk.
    edestruct (allocate_in_χ_priv χ1 blk) as (χ3 & γ & Hext3); first by eapply extended_to_inj.
    eassert (extended_to χMLold _ χ3).
    1: (eapply extended_to_trans; last done); done.
    do 3 eexists; split; first done.
    econstructor.
    + rewrite lookup_union_r; first by erewrite lookup_singleton.
      eapply map_disjoint_Some_r. 1: eapply extended_to_trans_2; done.
      apply lookup_singleton.
    + eapply is_val_extended_to_weaken; done.
Qed.

Lemma deserialize_ML_values χMLold vs :  
  lloc_map_inj χMLold
→ ∃ χC ζimm lvs,
    extended_to χMLold ζimm χC
  ∧ Forall2 (is_val χC ζimm) vs lvs.
Proof.
  induction vs as [|v vs IH] in χMLold|-*; intros Hinj.
  - eexists χMLold, ∅, _; split_and!; [by eapply extended_to_refl | econstructor ].
  - destruct (deserialize_ML_value χMLold v Hinj) as (χ1 & ζ1 & lv & Hext1 & Hlv1).
    destruct (IH χ1) as (χ2 & ζ2 & lvs & Hext2 & Hlv2); first by eapply extended_to_inj.
    eassert (extended_to χMLold _ χ2) by by eapply extended_to_trans.
    eexists _, _, (lv::lvs). split_and!; first done.
    econstructor.
    + by eapply is_val_extended_to_weaken.
    + eapply Forall2_impl; first done.
      intros v' lv' H1. eapply is_val_mono; last done; try done.
      eapply map_union_subseteq_r, extended_to_trans; done.
Qed.

Lemma deserialize_ML_block χMLold vs :  
  lloc_map_inj χMLold
→ ∃ χC ζimm blk,
    extended_to χMLold ζimm χC
  ∧ is_heap_elt χC ζimm vs blk.
Proof.
  intros H.
  destruct (deserialize_ML_values χMLold vs H) as (χC & ζimm & lvs & H1 & H2).
  by exists χC, ζimm, (Bvblock (Mut,(TagDefault,lvs))).
Qed.


Lemma is_store_blocks_mono_weaken χ1 χ2 ζ σ:
  is_store_blocks χ1 ζ σ →
  lloc_map_mono χ1 χ2 →
  is_store_blocks χ2 ζ σ.
Proof.
  intros (H1&H2) [Hsub H3]. split.
  - intros x Hx. destruct (H1 x Hx) as [y Hy]; exists y.
    eapply lookup_weaken; done.
  - intros γ; destruct (H2 γ) as [H2L H2R]; split.
    + intros H; destruct (H2L H) as (ℓ&Vs&HH1&HH2). do 2 eexists; repeat split; try done.
      eapply lookup_weaken; done.
    + intros (ℓ&Vs&HH1&HH2).
      apply H2R. do 2 eexists; repeat split; try done.
      destruct (H1 ℓ) as (γ2&Hγ2); first by eapply elem_of_dom_2.
      rewrite <- Hγ2.
      eapply lookup_weaken in Hγ2; last done.
      f_equiv. eapply H3; done.
Qed.

Lemma is_heap_elt_weaken χ ζ vs blk ζ' χ' :
  is_heap_elt χ ζ vs blk
→ χ ⊆ χ'
→ ζ ⊆ ζ'
→ is_heap_elt χ' ζ' vs blk.
Proof.
  intros H1 H2 H3.
  inversion H1; subst.
  econstructor. eapply Forall2_impl; first done.
  intros x y H4; eapply is_val_mono; last done. all:done.
Qed.

Lemma is_heap_elt_weaken_2 χ ζ vs blk ζ' χ' :
  is_heap_elt χ ζ vs blk
→ extended_to χ' ζ χ
→ dom ζ' ⊆ dom χ'
→ is_heap_elt χ (ζ' ∪ ζ) vs blk.
Proof.
  intros H1 H2 H3.
  eapply is_heap_elt_weaken. 1: done.
  1: done. eapply map_union_subseteq_r.
  eapply map_disjoint_dom. eapply disjoint_weaken.
  1: apply H2. 1-2:done.
Qed.

Lemma deserialize_ML_heap χMLold σ : 
  lloc_map_inj χMLold
→ ∃ χC ζσ ζnewimm,
    extended_to χMLold ζnewimm χC
  ∧ is_store_blocks χC σ ζσ
  ∧ is_store χC (ζσ ∪ ζnewimm) σ.
Proof.
  revert χMLold.
  induction σ as [|ℓ [vv|] σ Hin IH] using map_ind; intros χMLold HχMLold .
  - exists χMLold, ∅, ∅; split_and!. 2: econstructor.
    + by eapply extended_to_refl.
    + intros γ; rewrite dom_empty_L; done.
    + split; rewrite dom_empty_L. 1: done.
      intros (ℓ & Vs & H1 & H2). exfalso. rewrite lookup_empty in H2. done.
    + intros ℓ Vs γ blk Hc. exfalso. rewrite lookup_empty in Hc. done.
  - destruct (IH χMLold) as (χ0 & ζσ & ζi0 & Hext & Hstbl & Hstore). 1: done.
    destruct (ensure_in_χ_pub χ0 ℓ) as (χ1 & γ & Hχ1 & Hγ & Hold); first by eapply extended_to_inj.
    apply extended_to_mono in Hχ1.
    destruct (deserialize_ML_block χ1 vv) as (χ2 & ζi2 & lvs & Hext2 & Helt); first by eapply extended_to_inj.
    edestruct (extended_to_trans) as (HextA&Hdisj1). 1: exact Hext. 1: eapply extended_to_trans; done.
    rewrite map_empty_union in Hdisj1.
    rewrite map_empty_union in HextA.
    assert (is_store_blocks χ2 (<[ℓ:=Some vv]> σ) (<[γ:=lvs]> ζσ)) as Hstore2.
    1: {eapply is_store_blocks_restore_loc.
        * eapply is_store_blocks_mono_weaken; first done. eapply extended_to_trans; done.
        * apply Hext2.
        * eapply lookup_weaken. 1: done. apply Hext2.
        * by right. }
    assert (dom (<[γ:=lvs]> ζσ ∪ ζi0) ⊆ dom χ1) as Hsub3.
    { rewrite dom_union_L. eapply union_subseteq. split.
      * rewrite dom_insert_L. apply union_subseteq. split.
        eapply singleton_subseteq_l; first by eapply elem_of_dom_2.
        eapply elem_of_subseteq; intros k Hk.
        destruct Hstbl as (HH1&HH2). apply HH2 in Hk. destruct Hk as (?&?&H1&H2).
        eapply elem_of_dom_2. eapply lookup_weaken; first apply H1.
        eapply Hχ1.
      * etransitivity; last eapply subseteq_dom, Hχ1.
        eapply extended_to_dom_subset; done. }
    eexists χ2, (<[γ := lvs]> ζσ), (ζi0 ∪ ζi2). split_and!. 1-2:done.
    intros ℓ' vs γ' blk H1 H2 H3.  destruct HextA as (HH1&HH2&HH3).
    apply lookup_union_Some in H3. 1: destruct H3 as [H3|H3].
    3: { eapply map_disjoint_dom; eapply elem_of_disjoint.
         intros x Hx1 Hx2; specialize (HH3 x Hx2). destruct Hstore2 as [HHL HHR].
         apply HHR in Hx1. destruct Hx1 as (l1 & Vs1 & ? & ?); congruence. }
    2: { rewrite HH3 in H2; last by eapply elem_of_dom_2. congruence. }
    apply lookup_insert_Some in H3. destruct H3 as [[? ?]|[Hne H3]].
    + subst. rewrite map_union_assoc.
      eapply lookup_weaken in Hγ. 2: eapply Hext2. rewrite Hγ in H2. injection H2; intros ->.
      rewrite lookup_insert in H1. injection H1; intros ->.
      by eapply is_heap_elt_weaken_2.
    + eapply lookup_insert_Some in H1. destruct H1 as [[-> H]|[Hne1 H1]].
      1: {exfalso. apply Hne. eapply HH1. 2: done. eapply lookup_weaken; first done. apply Hext2. }
      assert (χ0 !! γ' = Some (LlocPublic ℓ')) as H2'.
      1: {destruct Hstbl as [HHL HHR]. destruct (HHL ℓ') as (gg&Hgg); first by eapply elem_of_dom_2.
          rewrite <- Hgg; f_equal. eapply HH1. 1: done. eapply lookup_weaken; first done. etransitivity; last eapply Hext2; eapply Hχ1. }
      eapply is_heap_elt_weaken.
      1: eapply Hstore. 1: done. 3: etransitivity; first eapply Hχ1; last apply Hext2.
      2: erewrite lookup_union_l; first done. 1: done.
      1: eapply not_elem_of_dom; intros H; eapply Hext in H; congruence.
      etransitivity; first eapply map_union_mono_l.
      2: etransitivity; first eapply map_union_mono_r. 4: done.
      1: eapply map_union_subseteq_l.
      1: eapply is_store_blocks_is_private_blocks_disjoint; done.
      eapply insert_subseteq, not_elem_of_dom.
      intros H. destruct Hstbl as [HHL HHR]. eapply HHR in H.
      destruct H as (?&?&Heq1&HeqF). eapply lookup_weaken in Heq1; first erewrite Hγ in Heq1. 2: apply Hχ1.
      injection Heq1; intros ->; rewrite HeqF in Hin; congruence.
  - destruct (IH χMLold) as (χ0 & ζσ & ζi0 & Hext & Hstbl & Hstore). 1: done.
    destruct (ensure_in_χ_pub χ0 ℓ) as (χ1 & γ & Hχ1 & Hγ & Hold); first by eapply extended_to_inj.
    edestruct (extended_to_trans) as (HextA&Hdisj1); first exact Hext. 1: eapply extended_to_mono, Hχ1.
    exists χ1, ζσ, ζi0. split_and!. 2: destruct Hstbl as [HL HR]; split.
    + rewrite map_union_empty in HextA. done.
    + rewrite dom_insert_L. intros ℓ0 [->%elem_of_singleton|H]%elem_of_union.
      1: eexists; done.
      destruct (HL ℓ0 H) as (γ1&Hγ1). exists γ1; eapply lookup_weaken; first done.
      eapply Hχ1.
    + intros γ0; specialize (HR γ0) as (HRL&HRR). split.
      1: intros H; destruct (HRL H) as (ℓ0 & Vs & H3 & H5); do 2 eexists;
        split; first (eapply lookup_weaken; first done; eapply Hχ1);
        rewrite lookup_insert_ne; first done;
        intros ->; rewrite Hin in H5; congruence.
      intros (ℓ0&Vs&HH1&HH2).
      rewrite lookup_insert_Some in HH2; destruct HH2 as [[? ?]|[Hne HH2]].
      1: congruence.
      eapply HRR. eexists ℓ0, Vs. split; last done.
      eapply elem_of_dom_2 in HH2.
      destruct (HL ℓ0 HH2) as (γ1&Hγ1). rewrite <- Hγ1. f_equal.
      eapply Hχ1; try done. eapply lookup_weaken, Hχ1; done.
    + intros ℓ1 vs γ1 blk [[? ?]|[? H1]]%lookup_insert_Some H2 H3; try congruence.
      eapply is_heap_elt_weaken. 1: eapply Hstore; try done.
      3: done. 2: eapply Hχ1.
      destruct Hstbl as [HHL HHR].
      destruct (HHL ℓ1) as (k1&Hk1); first by eapply elem_of_dom_2.
      rewrite <- Hk1. f_equal. eapply Hχ1; try done. eapply lookup_weaken, Hχ1; done.
Qed.

Lemma deserialize_ML_heap_extra ζMLold χMLold σ : 
  lloc_map_inj χMLold
→ dom ζMLold ⊆ dom χMLold
→ (map_Forall (fun _ ℓ => σ !! ℓ = Some None) (pub_locs_in_lstore χMLold ζMLold))
→ ∃ χC ζσ ζnewimm,
    extended_to χMLold ζnewimm χC
  ∧ is_store_blocks χC σ ζσ
  ∧ ζMLold ##ₘ (ζσ ∪ ζnewimm)
  ∧ is_store χC (ζMLold ∪ ζσ ∪ ζnewimm) σ.
Proof.
  intros H1 H2 H3.
  destruct (deserialize_ML_heap χMLold σ) as (χC&ζσ&ζi&HA1&HA2&HA3). 1: apply H1.
  assert (ζMLold ##ₘ ζσ ∪ ζi) as Hdisj.
  1: eapply map_disjoint_union_r; split; last (eapply map_disjoint_dom, disjoint_weaken; first apply HA1; done).
  1: { eapply map_disjoint_spec. intros γ b1 b2 HH1 HH2.
       destruct HA2 as [_ HA2R]. eapply elem_of_dom_2 in HH2. apply HA2R in HH2.
       destruct HH2 as (ℓ & Vs & HH7 & HH8).
       erewrite (map_Forall_lookup_1 _ _ _ _ H3) in HH8.
       2: { eapply elem_of_dom_2 in HH1. erewrite pub_locs_in_lstore_lookup; first done; first done.
            eapply elem_of_weaken in H2; last done.
            eapply elem_of_dom in H2; destruct H2 as [k Hk]. rewrite Hk. 
            eapply lookup_weaken in Hk; first erewrite HH7 in Hk. 2: eapply HA1. done. }
       congruence. }
  do 3 eexists; split_and!; try done.
  - intros ℓ vs γ b He1 He2 He3.
    eapply is_heap_elt_weaken. 1: eapply HA3; try done. 2: done.
    + rewrite <- map_union_assoc in He3. eapply lookup_union_Some in He3; destruct He3; try done.
      destruct (HA2) as [HL HR]. destruct (HR γ) as [HRL HRR]. eapply elem_of_dom in HRR. destruct HRR as [vv Hvv].
      2: do 2 eexists; done.
      exfalso. erewrite map_disjoint_Some_r in H; try congruence. 1: done.
      erewrite lookup_union_Some_l; last done; first done.
    + erewrite <- map_union_assoc. eapply map_union_subseteq_r. done.
Qed.

Lemma interp_ML_discarded_locs_pub χpub σ :
    gen_heap_interp σ
 -∗ ([∗ map] ℓ ∈ χpub, ℓ ↦M/)
 -∗ ⌜map_Forall (λ (_ : nat) (ℓ : loc), σ !! ℓ = Some None) χpub⌝.
Proof.
  induction χpub as [|k l χpub Hin IH] using map_ind; iIntros "HH HK".
  - iPureIntro. apply map_Forall_empty.
  - iPoseProof (big_sepM_insert) as "[HL _]". 1: apply Hin.
    iPoseProof ("HL" with "HK") as "[H1 H2]".
    iPoseProof (IH with "HH H2") as "%HIH". 1: iFrame.
    iPoseProof (gen_heap_valid with "HH H1") as "%Hv".
    iPureIntro. apply map_Forall_insert. 1: done. split; done.
Qed.


End ChiZetaConstruction.

Section ThetaConstruction.

Lemma collect_dom_θ_vs (θdom : gset lloc) (vs : list lval) :
  exists θdom' : gset lloc,
    ∀ γ, Lloc γ ∈ vs ∨ γ ∈ θdom ↔ γ ∈ θdom'.
Proof.
  induction vs as [|[|ℓ] vs (θdom1 & IH)].
  - exists θdom. intros γ. split; last eauto. by intros [H%elem_of_nil|].
  - exists θdom1. intros γ. etransitivity; last by eapply IH.
    split; (intros [H|]; last by eauto); left.
    + apply elem_of_cons in H as [|]; done.
    + apply elem_of_cons; eauto.
  - exists (θdom1 ∪ {[ ℓ ]}). intros γ. split.
    + intros [[Hc|H]%elem_of_cons|?]; eapply elem_of_union.
      1: right; eapply elem_of_singleton; congruence.
      all: left; apply IH. 1: by left. by right.
    + intros [[H|H]%IH| ->%elem_of_singleton]%elem_of_union.
      1: left; by right. 1: by right.
      left; by left.
Qed.

Lemma collect_dom_θ_block (θdom : gset lloc) (blk : block) :
  exists θdom' : gset lloc,
    ∀ γ, lval_in_block blk (Lloc γ) ∨ γ ∈ θdom ↔ γ ∈ θdom'.
Proof.
  destruct blk as [[m [tg vs]]|]; last first.
  { (* Bclosure *)
    exists θdom. intros γ. split; eauto. intros [H|]; auto.
    by inversion H. }
  { (* Bvblock *)
    destruct (collect_dom_θ_vs θdom vs) as (θdom' & H).
    exists θdom'. intros γ. split.
    - intros [HH|]; first inversion HH; subst; apply H; eauto.
    - intros [?|?]%H; eauto. left; by constructor. }
Qed.

Lemma collect_dom_θ_ζ_blocks (θdom : gset lloc) (ζ : lstore) :
  exists θdom' : gset lloc,
    forall γ, ((exists γ1 blk, ζ !! γ1 = Some blk ∧ lval_in_block blk (Lloc γ))
               ∨ γ ∈ θdom)
              ↔ γ ∈ θdom'.
Proof.
  induction ζ as [|k blk ζ Hne (θdom1 & Hdom1)] using map_ind.
  - exists θdom; split; auto. intros [(γ1&blk&H1&_)|]; auto.
    simplify_map_eq.
  - destruct (collect_dom_θ_block θdom1 blk) as (θdom2 & Hdom2).
    exists θdom2. intros γ; split.
    + intros [(γ1&blk'&[[-> ->]|[Hne2 Hin]]%lookup_insert_Some&H2)|Hold].
      { apply Hdom2; left; congruence. }
      { apply Hdom2. right. apply Hdom1. left. by do 2 eexists. }
      { apply Hdom2; right; apply Hdom1; right; done. }
    + intros [H|[(γ1&blk'&H1&H2)|H]%Hdom1]%Hdom2.
      1: left; do 2 eexists; split; first eapply lookup_insert; done.
      2: by right.
      left; do 2 eexists; split; last done; first rewrite lookup_insert_ne; first done.
      intros ->; rewrite Hne in H1; congruence.
Qed.

Lemma collect_dom_θ_ζ (θdom : gset lloc) (ζ : lstore) :
  exists θdom' : gset lloc,
    forall γ, (γ ∈ dom ζ ∨ (exists γ1 blk, ζ !! γ1 = Some blk ∧ lval_in_block blk (Lloc γ))
               ∨ γ ∈ θdom)
              ↔ γ ∈ θdom'.
Proof.
  destruct (collect_dom_θ_ζ_blocks θdom ζ) as (θdom1 & Hdom1).
  exists (dom ζ ∪ θdom1). intros γ; split.
  - (intros [H|H]; apply elem_of_union); first by left.
    right; apply Hdom1; done.
  - intros [H|H]%elem_of_union; first by left. right; by apply Hdom1.
Qed.

Lemma collect_dom_θ_roots (θdom : gset lloc) (roots : roots_map) : exists θdom' : gset lloc,
    forall γ, ((exists k, roots !! k = Some (Lloc γ)) ∨ γ ∈ θdom) ↔ γ ∈ θdom'.
Proof.
  induction roots as [|k [z|l] roots Hne (θdom1 & IH)] using map_ind.
  - exists θdom. intros γ. split; last eauto. intros [[? H%lookup_empty_Some]|?]; done.
  - exists θdom1. intros γ. split.
    + intros [[k1 [[-> ?]|[H1 H2]]%lookup_insert_Some]|?]; try congruence; apply IH. 2: by right. left. by eexists.
    + intros [[k' Hk]|H]%IH; last by right. left. exists k'. rewrite lookup_insert_ne; first done. intros ->; rewrite Hne in Hk; done.
  - exists (θdom1 ∪ {[ l ]}). intros γ. split.
    + intros [[k1 [[-> ?]|[H1 H2]]%lookup_insert_Some]|?]; try congruence; eapply elem_of_union. 1: right; eapply elem_of_singleton; congruence.
      all: left; apply IH. 2: by right. left; by eexists.
    + intros [[[k' Hk]|H]%IH| ->%elem_of_singleton]%elem_of_union. 2: by right. 2: left; exists k; by rewrite lookup_insert.
      left; exists k'; rewrite lookup_insert_ne; first done. intros ->; rewrite Hne in Hk; congruence.
Qed.

Lemma injectivify_map (S : gset lloc) : exists M : addr_map, dom M = S ∧ gmap_inj M.
Proof.
  induction S as [|s S Hne (M & <- & Hinj)] using set_ind_L.
  - exists ∅; split; first by rewrite dom_empty_L. intros ??? H1; exfalso. rewrite lookup_empty in H1; done.
  - exists (<[s := fresh (codom M)]> M). split.
    1: by rewrite dom_insert_L.
    apply gmap_inj_extend; try done.
    intros k' v' H%codom_spec_2 <-. unshelve eapply is_fresh; last exact H. all: apply _.
Qed.

End ThetaConstruction.

Section CallFacts.


Implicit Type (p : language.prog C_lang).

Notation fillCCall K s vv := (language.fill K (language.of_class C_lang (ExprCall s vv))).

(* Lemma call_no_StepCS vv p s K mem ec' mem' T : *)
(*   p !! s = None → *)
(*   ~ (language.language.prim_step p (fillCCall K s vv) mem ec' mem' T). *)
(* Proof. *)
(*   intros Hno H4. *)
(*   eapply prim_step_inv in H4. *)
(*   destruct H4 as (K' & e1' & e2' & Heq1 & Heq2 & Hhead). *)
(*   subst ec'. symmetry in Heq1. epose proof Heq1 as Heq2. *)
(*   eapply (language.call_in_ctx K' K e1' s vv) in Heq1 as [(K'' & ->)|(v & <-)]. *)
(*   2: eapply language.val_head_step, Hhead. *)
(*   rewrite <- language.fill_comp in Heq2. *)
(*   eapply language.fill_inj in Heq2. subst e1'. epose proof Hhead as Hhead2. *)
(*   eapply language.head_ctx_step_val in Hhead as [H|[x H]]. 2: apply language.language.of_to_val in H; cbn in H; done. *)
(*   subst K''. rewrite language.fill_empty in Hhead2. *)
(*   eapply (language.call_head_step p s vv) in Hhead2 as (fn & Hne & _). *)
(*   cbn in Hno. rewrite Hno in Hne. congruence. *)
(* Qed. *)


(* Lemma call_no_RetS vv p s K r : *)
(*   p !! s = None → *)
(*   ~ (C_lang.to_val (fillCCall K s vv) = Some r). *)
(* Proof. *)
(*   intros Hno H4%C_lang.of_to_val. *)
(*   edestruct (language.fill_class K) as [-> | [v Hv]]. *)
(*   - exists (ExprVal r); erewrite <- H4; done. *)
(*   - cbn in H4. congruence. *)
(*   - unfold language.language.to_val in Hv. by rewrite language.to_of_class in Hv. *)
(* Qed. *)

(* Lemma call_inversion vv p s K K' ec s' vv' : *)
(*   p !! s = None → *)
(*   language.fill K' ec = fillCCall K s vv → *)
(*   language.to_call ec = Some (s', vv') *)
(*   → s' = s ∧ vv' = vv ∧ K' = K. *)
(* Proof. *)
(*   intros H1 H2 H3. epose proof H2 as H2'. *)
(*   eapply language.call_in_ctx in H2' as [(K'' & ->)|(v & Hv)]. *)
(*   - rewrite <- language.fill_comp in H2. apply language.fill_inj in H2. *)
(*     subst ec. unfold language.to_call in H3. *)
(*     edestruct (language.to_class) as [[|]|] eqn:Heq; try congruence. *)
(*     edestruct (language.fill_class' K'') as [->|[v Hv]]; first by eexists. *)
(*     2: rewrite language.to_of_class in Hv; done. *)
(*     cbn in Heq. rewrite c_toy_lang.melocoton.lang_instantiation.map_unmap_val in Heq. *)
(*     split_and!; cbn; congruence. *)
(*   - subst ec. cbn in H3. done. *)
(* Qed. *)

End CallFacts.

(* XXX this should perhaps be moved someplace else? *)
Lemma ml_to_c_exists vs ρml σ :
  lloc_map_inj (χML ρml) →
  dom (ζML ρml) ⊆ dom (χML ρml) →
  map_Forall (λ (_ : nat) (ℓ : loc), σ !! ℓ = Some None) (pub_locs_in_lstore (χML ρml) (ζML ρml)) →
  dom (privmemML ρml) ## dom (rootsML ρml) →
  ∃ ws ρc mem, ml_to_c vs ρml σ ws ρc mem.
Proof.
  intros Hχinj Hζdom Hpublocs Hprivmem.
  destruct (deserialize_ML_heap_extra (ζML ρml) (χML ρml) σ) as (χ1 & ζσ & ζσimm & Hext & Hstorebl & Hdisj & Hstore).
  1: done.
  1: done.
  1: done.
  destruct (deserialize_ML_values χ1 vs) as (χ2 & ζimm & lvs & Hext2 & Hvs).
  1: apply Hext.

  assert (ζML ρml ∪ ζσ ∪ ζσimm ##ₘ ζimm) as Hdis1.
  1: { eapply map_disjoint_dom. eapply disjoint_weaken. 1: eapply Hext2. 2: done.
       rewrite dom_union_L. eapply union_subseteq. split. 2: by eapply extended_to_dom_subset.
       rewrite dom_union_L. eapply union_subseteq; split.
       1: etransitivity; first by eapply elem_of_subseteq. 1: eapply subseteq_dom, Hext.
       intros γ Hγ. destruct Hstorebl as [_ HR]. apply HR in Hγ. destruct Hγ as (ℓ & ? & HH & _); by eapply elem_of_dom_2. }

  pose (ζML ρml ∪ ζσ ∪ (ζσimm ∪ ζimm)) as ζC.

  destruct (collect_dom_θ_ζ ∅ ζC) as (θdom1 & Hθdom1).
  destruct (collect_dom_θ_vs θdom1 lvs) as (θdom2 & Hθdom2).
  destruct (collect_dom_θ_roots θdom2 (rootsML ρml)) as (θdom3 & Hθdom3).
  destruct (injectivify_map θdom3) as (θC & Hdom & Hinj).
  destruct (find_repr_lval_vs θC lvs) as (ws & Hws).
  1: intros γ Hγ; subst θdom3; apply Hθdom3; right; apply Hθdom2; left; done.
  assert (roots_are_live θC (rootsML ρml)) as Hrootslive.
  1: { intros a γ ?. subst θdom3. apply Hθdom3. left. by eexists. }
  destruct (find_repr_roots θC (rootsML ρml) (privmemML ρml)) as (mem & Hrepr); [done..|].

  eexists ws, (WrapstateC χ2 ζC θC _), mem. unfold ml_to_c; cbn.
  exists ζσ, (ζσimm ∪ ζimm), lvs. split_and!; try done.
  { eapply extended_to_trans; done. }
  { destruct Hstorebl as [HL HR]; split.
    { intros ℓ  Hℓ. destruct (HL ℓ Hℓ) as (γ & Hγ). exists γ. eapply lookup_weaken; first done. apply Hext2. }
    { intros γ; destruct (HR γ) as [HRL HRH]; split.
       1: intros H; destruct (HRL H) as (ℓ & Vs & H1 & H2); exists ℓ, Vs; split; try done; eapply lookup_weaken; first done; apply Hext2.
       intros (ℓ & Vs & H1 & H2). apply HRH. exists ℓ, Vs. split; try done. eapply elem_of_dom_2 in H2. destruct (HL _ H2) as (γ2 & Hγ2).
       enough (γ2 = γ) as -> by done. eapply Hext2. 2: done. eapply lookup_weaken; first done; eapply Hext2. } }
  { intros γ. rewrite dom_union_L. intros [H|H]%elem_of_union; eapply lookup_weaken.
    1: by eapply Hext. 2: by eapply Hext2. 2: done. 1: apply Hext2. }
  { rewrite map_union_assoc. apply map_disjoint_union_r_2. 1: done.
    eapply map_disjoint_dom, disjoint_weaken; first eapply map_disjoint_dom, Hdis1; try done.
    erewrite ! dom_union_L; set_solver. }
  { intros ℓ vs' γ b H1 H2 H3. unfold ζC in *. rewrite ! map_union_assoc. rewrite ! map_union_assoc in H3.
    apply lookup_union_Some_inv_l in H3.
    2: apply not_elem_of_dom; intros Hc; apply Hext2 in Hc; congruence.
    eapply is_heap_elt_weaken. 1: eapply Hstore; try done.
    2: apply Hext2.
    + destruct Hstorebl as [HL HR]; destruct (HL ℓ) as [v Hv]; first by eapply elem_of_dom_2.
      rewrite <- Hv; f_equal; eapply Hext2; try done; eapply lookup_weaken, Hext2; try done.
    + eapply map_union_subseteq_l. }
  { eapply Forall2_impl; first done. intros ? ? H; eapply is_val_mono; last done; first done.
    unfold ζC. rewrite ! map_union_assoc. eapply map_union_subseteq_r. done. }
  { split; first done. subst θdom3. intros γ blk γ' _ H2 H3.
    apply Hθdom3. right. apply Hθdom2. right. apply Hθdom1. right. left. do 2 eexists; done. }
Qed.

End Utils.
