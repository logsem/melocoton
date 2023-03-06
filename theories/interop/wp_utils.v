From Coq Require Import ssreflect.
From stdpp Require Import strings gmap list.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import state lang basics_resources.
From melocoton.interop Require Export basics_constructions.
From iris.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra Require Import gset gset_bij.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.interop Require Import basics prims weakestpre wp_block_sim.
Import Wrap.


Global Notation MLval := ML_lang.val.
Global Notation Cval := C_lang.val.


Notation mkPeC p T := ({| penv_prog := p; penv_proto := T |} : prog_environ C_lang (_ : gFunctors)).
Notation mkPeML p T := ({| penv_prog := p; penv_proto := T |} : prog_environ ML_lang (_ : gFunctors)).
Notation mkPeW p T := ({| weakestpre.penv_prog := p; weakestpre.penv_proto := T |} : weakestpre.prog_environ wrap_lang (_ : gFunctors)).

Section Utils.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Implicit Types P : iProp Σ.
Import mlanguage.

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

(* The most general spec, prove stuff for specific block-level pointstos later *)
Definition proto_alloc : prim_proto := (λ p vl Φ,
   ∃ θ tg sz,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜p = Palloc⌝ ∗
     "->" ∷ ⌜vl = [ C_lang.LitV $ C_lang.LitInt $ vblock_tag_as_int $ tg; C_lang.LitV $ C_lang.LitInt $ sz ]⌝ ∗
     "%Hsz" ∷ ⌜0 ≤ sz⌝%Z ∗
     "Cont" ∷ (∀ θ' γ w, GC θ' -∗
                         γ ↦fresh (tg, List.repeat (Lint 0) (Z.to_nat sz)) -∗
                         ⌜repr_lval θ' (Lloc γ) w⌝ -∗
                         Φ w))%I.


Definition proto_callback (E : coPset) T : prim_proto := (λ p vl Φ,
  ∃ θ w γ w' lv' v' f x e ψ,
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜p = Pcallback⌝ ∗
    "->" ∷ ⌜vl = [ w; w' ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hclos" ∷ γ ↦clos (f, x, e) ∗
    "%Hreprw'" ∷ ⌜repr_lval θ lv' w'⌝ ∗
    "Hsim'" ∷ block_sim v' lv' ∗
    "WPcallback" ∷ ▷ WP (App (Val (RecV f x e)) (Val v')) @ mkPeML ∅ T ; E {{ ψ }} ∗
    "Cont" ∷ (∀ θ' vret lvret wret,
                GC θ' -∗
                ψ vret -∗
                block_sim vret lvret -∗
                ⌜repr_lval θ' lvret wret⌝ -∗
                Φ wret))%I.



(* non-callbacks primitives *)
Definition proto_base_prims : prim_proto := (λ p vl Φ,
    proto_int2val p vl Φ ∨ proto_val2int p vl Φ ∨ proto_registerroot p vl Φ ∨ proto_unregisterroot p vl Φ
  ∨ proto_modify p vl Φ ∨ proto_readfield p vl Φ ∨ proto_alloc p vl Φ)%I.

Definition proto_prims E T : prim_proto := (λ p vl Φ,
  proto_base_prims p vl Φ ∨ proto_callback E T p vl Φ)%I.

Lemma proto_prims_mask_mono E1 E2 T : E1 ⊆ E2 →
  ∀ p vl Φ, proto_prims E1 T p vl Φ -∗ proto_prims E2 T p vl Φ.
Proof.
  iIntros (H p vl Φ) "[HL|HR]".
  1: by iLeft.
  iNamed "HR". iRight.
  do 10 iExists _; unfold named.
  iFrame. do 4 (iSplit; first done).
  iNext. iApply @wp_mask_mono. 1: done.
  iFrame.
Qed.

Definition proto_prims_in_C E T : C_proto := (λ f vs Φ,
  ∃ p, ⌜is_prim f p⌝ ∗ proto_prims E T p vs Φ
)%I.


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

Lemma repr_roots_repr_lval θ roots m : repr_roots θ roots m -> forall k v, roots !! k = Some v -> exists w, m !! k = Some (Storing w) /\ repr_lval θ v w.
Proof.
  induction 1; intros ??.
  - intros H. rewrite lookup_empty in H. done.
  - intros [[<- <-]|[Hn1 Hn2]]%lookup_insert_Some.
    + rewrite lookup_insert. econstructor. done.
    + rewrite lookup_insert_ne. 2: done. apply IHrepr_roots. done.
Qed.

Lemma repr_dom_eq θ mem roots_1 roots_2 p1 p2 m1 m2 : 
   dom roots_1 = dom roots_2
 → gmap_inj θ
 → repr_raw θ roots_1 p1 mem m1
 → repr_raw θ roots_2 p2 mem m2
 → p1 = p2 ∧ m1 = m2 ∧ roots_1 = roots_2.
Proof.
  intros H1 Hinj (Hr1&Hd1&Hu1) (Hr2&Hd2&Hu2).
  assert (m1 = m2) as ->.
  { apply repr_roots_dom in Hr1,Hr2. rewrite H1 in Hr1. rewrite Hr1 in Hr2.
    eapply map_eq_iff. intros i. destruct (m1 !! i) as [v|] eqn:Heq.
    + eapply elem_of_dom_2 in Heq as Hdom. eapply lookup_union_Some_l in Heq.
      erewrite <- Hu1 in Heq. erewrite <- Heq. erewrite Hu2.
      rewrite Hr2 in Hdom.
      eapply lookup_union_l. apply elem_of_dom in Hdom as [vv Hvv]. 
      eapply map_disjoint_Some_l. 1: done. apply Hvv.
    + symmetry. eapply not_elem_of_dom. rewrite <- Hr2. by eapply not_elem_of_dom. }
  assert (p1 = p2) as ->.
  { eapply map_eq_iff. intros i. destruct (p1 !! i) as [v|] eqn:Heq.
    + eapply elem_of_dom_2 in Heq as Hdom. eapply lookup_union_Some_r in Heq.
      erewrite <- Hu1 in Heq. erewrite <- Heq. erewrite Hu2.
      eapply lookup_union_r. 2: done.
      eapply not_elem_of_dom. eapply map_disjoint_dom in Hd1. set_solver.
    + destruct (mem !! i) as [v'|] eqn:Heqmem.
      * pose proof Heqmem as Heq2. rewrite Hu1 in Heqmem.
        apply lookup_union_Some_inv_l in Heqmem. 2: done. symmetry.
        eapply map_disjoint_Some_r. 1: done. done.
      * rewrite Hu2 in Heqmem. apply lookup_union_None_1 in Heqmem. symmetry. apply Heqmem. }
  split_and!; try done.
  pose proof (repr_roots_repr_lval _ _ _ Hr2) as Hr2'.
  clear Hd1 Hu1 Hd2 Hu2 Hr2.
  induction Hr1 in Hinj, roots_2, H1, Hr2'|-*.
  { rewrite dom_empty_L in H1. symmetry in H1. apply dom_empty_inv_L in H1. done. }
  destruct (roots_2 !! a) as [v2|] eqn:Heq.
  2: { eapply not_elem_of_dom in Heq. rewrite <- H1 in Heq. erewrite dom_insert_L in Heq. set_solver. }
  erewrite <- (insert_delete roots_2 a v2); last done. f_equiv.
  - destruct (Hr2' a v2 Heq) as (ww & Heqw & Hrepr).
    rewrite lookup_insert in Heqw. injection Heqw; intros ->.
    inversion H; subst; inversion Hrepr; subst; try congruence.
    f_equiv. eapply Hinj; done.
  - eapply IHHr1.
    + rewrite dom_delete_L. rewrite <- H1. set_solver.
    + done.
    + intros k1 v1 [H3 H4]%lookup_delete_Some.
      destruct (Hr2' _ _ H4) as (ww&[[??]|[? ?]]%lookup_insert_Some&Hww2).
      1: done.
      by exists ww.
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

Lemma interp_ML_discarded_locs_pub χpub (σ:store) :
    gen_heap_interp σ
 -∗ ([∗ map] ℓ ∈ χpub, ℓ ↦M/)
 -∗ ⌜map_Forall (λ (_ : nat) (ℓ : loc), σ !! ℓ = Some None) χpub⌝.
Proof.
  induction χpub as [|k l χpub Hin IH] using map_ind; iIntros "HH HK".
  - iPureIntro. apply map_Forall_empty.
  - iPoseProof (big_sepM_insert) as "[HL _]". 1: apply Hin.
    iPoseProof ("HL" with "HK") as "[H1 H2]".
    iPoseProof (IH with "HH H2") as "%HIH".
    iPoseProof (gen_heap_valid with "HH H1") as "%Hv".
    iPureIntro. apply map_Forall_insert. 1: done. split; done.
Qed.

End Utils.


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
