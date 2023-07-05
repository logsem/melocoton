(** A "ghost map" (or "ghost heap") with a proposition controlling authoritative
ownership of the entire heap, and a "points-to-like" proposition for (mutable,
fractional, or persistent read-only) ownership of individual elements. *)
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Export dfrac.
From transfinite.base_logic.lib Require Export own.
From iris.prelude Require Import options.
From melocoton.interop.extra_ghost_state Require Import gmap_view_pluspers.

(** The CMRA we need.
FIXME: This is intentionally discrete-only, but
should we support setoids via [Equiv]? *)
Class PGMData : Type := {
  K : Type;
  V : Type;
  Vpers : Type;
  Fpers : V → Vpers;
  HEq :> EqDecision K;
  HCount :> Countable K;
  Pmap : gmap K V → Prop;
  Pmap_mono (m1 m2 : gmap K V) : Pmap m1 → m2 ⊆ m1 → Pmap m2;
  Pmap_init : Pmap ∅
}.

Global Program Instance EGV_PGM `{SI: indexT} `{D : PGMData} : ExtendedGmapView := {|
  gmap_view_pluspers.K := K;
  gmap_view_pluspers.V := leibnizO V;
  gmap_view_pluspers.Vpers := leibnizO Vpers;
  gmap_view_pluspers.Fpers := Fpers;
  gmap_view_pluspers.Pmap n := Pmap;
|}.
Next Obligation.
Proof.
  intros SI D n1 n2 m1 m2 H1 _ Helem; cbn.
  eapply Pmap_mono; first exact H1.
  eapply map_subseteq_spec.
  intros k v Hin.
  specialize (Helem k v Hin); inversion Helem; simplify_eq.
  cbv in H2. simplify_eq. done.
Defined.
Next Obligation. intros ???; exists ∅; apply Pmap_init. Defined.

Global Instance EGV_Discrete `{SI: indexT} `{D : PGMData} : PmapDiscrete (EGV_PGM).
Proof. by intros m n Hm. Qed.


Class pgmG `{SI: indexT} Σ (D : PGMData) := GhostMapG {
  pgm_inG : inG Σ (gmap_view_plusR _);
}.
Local Existing Instance pgm_inG.

Definition pgmΣ `{SI: indexT} (D' : PGMData) : gFunctors :=
  #[ GFunctor (gmap_view_plusR _) ].

Global Instance subG_pgmΣ `{SI: indexT} Σ (D : PGMData) :
  subG (pgmΣ D) Σ → pgmG Σ D.
Proof. solve_inG. Qed.

Section definitions.
  Context `{pgmG Σ}.

  Local Definition pgm_auth_def
      (γ : gname) (q : Qp) (m : gmap K V) : iProp Σ :=
    own γ (gmap_view_plus_auth (DfracOwn q) m).
  Local Definition pgm_auth_aux : seal (@pgm_auth_def).
  Proof. by eexists. Qed.
  Definition pgm_auth := pgm_auth_aux.(unseal).
  Local Definition pgm_auth_unseal :
    @pgm_auth = @pgm_auth_def := pgm_auth_aux.(seal_eq).

  Local Definition pgm_elem_def
      (γ : gname) (k : K) (dq : dfrac) (v : V) : iProp Σ :=
    own γ (gmap_view_plus_frag k dq v).
  Local Definition pgm_elem_aux : seal (@pgm_elem_def).
  Proof. by eexists. Qed.
  Definition pgm_elem := pgm_elem_aux.(unseal).
  Local Definition pgm_elem_unseal :
    @pgm_elem = @pgm_elem_def := pgm_elem_aux.(seal_eq).

  Local Definition pgm_pers_def
      (γ : gname) (k : K) (vp : Vpers) : iProp Σ :=
    own γ (gmap_view_plus_pers k vp).
  Local Definition pgm_pers_aux : seal (@pgm_pers_def).
  Proof. by eexists. Qed.
  Definition pgm_pers := pgm_pers_aux.(unseal).
  Local Definition pgm_pers_unseal :
    @pgm_pers = @pgm_pers_def := pgm_pers_aux.(seal_eq).
End definitions.

(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "k □↪[ γ ]{ dq } v" := (pgm_elem γ k dq v)
  (at level 20, γ at level 50, dq at level 50, format "k  □↪[ γ ]{ dq }  v") : bi_scope.
Notation "k □↪[ γ ]{# q } v" := (k □↪[γ]{DfracOwn q} v)%I
  (at level 20, γ at level 50, q at level 50, format "k  □↪[ γ ]{# q }  v") : bi_scope.
Notation "k □↪[ γ ] v" := (k □↪[γ]{#1} v)%I
  (at level 20, γ at level 50, format "k  □↪[ γ ]  v") : bi_scope.
Notation "k □↪[ γ ]□ v" := (k □↪[γ]{DfracDiscarded} v)%I
  (at level 20, γ at level 50) : bi_scope.
Notation "k □↪[ γ ]= vp" := (pgm_pers γ k vp)%I
  (at level 20, γ at level 50) : bi_scope.

Local Ltac unseal := rewrite
  ?pgm_auth_unseal /pgm_auth_def
  ?pgm_elem_unseal /pgm_elem_def
  ?pgm_pers_unseal /pgm_pers_def.

Section lemmas.
  Context `{pgmG Σ}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V) (vp : Vpers).

  (** * Lemmas about the map elements *)
  Global Instance pgm_elem_timeless k γ dq v : Timeless (k □↪[γ]{dq} v).
  Proof. unseal. apply _. Qed.
  Global Instance pgm_elem_persistent k γ v : Persistent (k □↪[γ]□ v).
  Proof. unseal. apply _. Qed.
  Global Instance pgm_elem_fractional k γ v : Fractional (λ q, k □↪[γ]{#q} v)%I.
  Proof. unseal. intros p q. rewrite -own_op gmap_view_plus_frag_add //. Qed.
  Global Instance pgm_elem_as_fractional k γ q v :
    AsFractional (k □↪[γ]{#q} v) (λ q, k □↪[γ]{#q} v)%I q.
  Proof. split; first done. apply _. Qed.

  Global Instance pgm_pers_timeless k γ vp : Timeless (k □↪[γ]= vp).
  Proof. unseal. apply _. Qed.
  Global Instance pgm_pers_persistent k γ vp : Persistent (k □↪[γ]= vp).
  Proof. unseal. apply _. Qed.

  Local Lemma pgm_elems_unseal γ m dq :
    ([∗ map] k ↦ v ∈ m, k □↪[γ]{dq} v) ==∗
    own γ ([^op map] k↦v ∈ m, gmap_view_plus_frag k dq v).
  Proof.
    unseal. destruct (decide (m = ∅)) as [->|Hne].
    - rewrite !big_opM_empty. iIntros "_". iApply own_unit.
    - rewrite big_opM_own //. iIntros "?". done.
  Qed.

  Local Lemma pgm_perms_unseal γ (mpers : gmap K Vpers) dq :
    ([∗ map] k ↦ vp ∈ mpers, k □↪[γ]= vp) ==∗
    own γ ([^op map] k↦vp ∈ mpers, gmap_view_plus_pers k vp).
  Proof.
    unseal. destruct (decide (mpers = ∅)) as [->|Hne].
    - rewrite !big_opM_empty. iIntros "_". iApply own_unit.
    - rewrite big_opM_own //. iIntros "?". done.
  Qed.

  Lemma pgm_elem_valid k γ dq v : k □↪[γ]{dq} v -∗ ⌜✓ dq⌝.
  Proof.
    unseal. iIntros "Helem".
    iDestruct (own_valid with "Helem") as %(?&?)%gmap_view_plus_frag_valid.
    done.
  Qed.
  Lemma pgm_elem_valid_2 k γ dq1 dq2 v1 v2 :
    k □↪[γ]{dq1} v1 -∗ k □↪[γ]{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %(?&?&?)%gmap_view_plus_frag_op_valid_L.
    done.
  Qed.
  Lemma pgm_elem_agree k γ dq1 dq2 v1 v2 :
    k □↪[γ]{dq1} v1 -∗ k □↪[γ]{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (pgm_elem_valid_2 with "Helem1 Helem2") as %[_ ?].
    done.
  Qed.
  Lemma pgm_elem_pers_agree k γ dq1 v1 vp2 :
    k □↪[γ]{dq1} v1 -∗ k □↪[γ]= vp2 -∗ ⌜Fpers v1 = vp2⌝.
  Proof.
    unseal. iIntros "Helem1 Helem2".
    iDestruct (own_valid_2 with "Helem1 Helem2") as %(?&?&?)%gmap_view_plus_frag_pers_op_valid_L.
    iPureIntro; done.
  Qed.
  Lemma pgm_pers_agree k γ vp1 vp2 :
    k □↪[γ]= vp1 -∗ k □↪[γ]= vp2 -∗ ⌜vp1 = vp2⌝.
  Proof.
    unseal. iIntros "Helem1 Helem2".
    iDestruct (own_valid_2 with "Helem1 Helem2") as %(?&Hn)%gmap_view_plus_pers_op_valid_L.
    iPureIntro; done.
  Qed.

  (** Get the persistent part. *)
  Lemma pgm_elem_to_pers k γ dq v :
    k □↪[γ]{dq} v -∗ k □↪[γ]= (Fpers v).
  Proof.
    unseal. iIntros "H".
    rewrite gmap_view_plus_frag_get_persistent.
    iPoseProof (own_op with "H") as "(_&$)".
  Qed.

  Lemma pgm_elem_combine k γ dq1 dq2 v1 v2 :
    k □↪[γ]{dq1} v1 -∗ k □↪[γ]{dq2} v2 -∗ k □↪[γ]{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (pgm_elem_agree with "Hl1 Hl2") as %->.
    unseal. iCombine "Hl1 Hl2" as "Hl". eauto with iFrame.
  Qed.

  Lemma pgm_elem_frac_ne γ k1 k2 dq1 dq2 v1 v2 :
    ¬ ✓ (dq1 ⋅ dq2) → k1 □↪[γ]{dq1} v1 -∗ k2 □↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof.
    iIntros (?) "H1 H2"; iIntros (->).
    by iDestruct (pgm_elem_valid_2 with "H1 H2") as %[??].
  Qed.
  Lemma pgm_elem_ne γ k1 k2 dq2 v1 v2 :
    k1 □↪[γ] v1 -∗ k2 □↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof. apply pgm_elem_frac_ne. apply: exclusive_l. Qed.

  (** Make an element read-only. *)
  Lemma pgm_elem_persist k γ dq v :
    k □↪[γ]{dq} v ==∗ k □↪[γ]□ v.
  Proof. unseal. iApply own_update. apply gmap_view_plus_frag_persist. Qed.

  Lemma pgm_elem_recover k γ v :
    k □↪[γ]□ v ==∗ ∃ q, k □↪[γ]{# q} v.
  Proof.
    unseal. iIntros "Hown". iMod (own_updateP with "Hown") as "Hown".
    1: apply gmap_view_plus_frag_dfractional, dfrac_update_recover.
    iDestruct "Hown"  as "(%&(%&->&(%q&->))&Hown)".
    by iExists q.
  Qed.

  (** * Lemmas about [pgm_auth] *)
  Lemma pgm_alloc_strong P m :
    Pmap m →
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ pgm_auth γ 1 m ∗ [∗ map] k ↦ v ∈ m, k □↪[γ] v.
  Proof.
    unseal. intros.
    iMod (own_alloc_strong (gmap_view_plus_auth (DfracOwn 1) ∅) P)
      as (γ) "[% Hauth]"; first done.
    { apply gmap_view_plus_auth_valid. intros ?. apply Pmap_init. }
    iExists γ. iSplitR; first done.
    rewrite -big_opM_own_1 -own_op. iApply (own_update with "Hauth").
    etrans; first eapply (gmap_view_plus_alloc_big EGV_PGM ∅ m (DfracOwn 1)).
    - apply map_disjoint_empty_r.
    - done.
    - intros ??. by rewrite map_union_empty.
    - rewrite right_id -big_opM_op.
      setoid_rewrite <- gmap_view_plus_frag_get_persistent.
      done.
  Qed.
  Lemma pgm_alloc_strong_empty P :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ pgm_auth γ 1 (∅ : gmap K V).
  Proof.
    intros. iMod (pgm_alloc_strong P ∅) as (γ) "(% & Hauth & _)"; eauto.
    apply Pmap_init.
  Qed.
  Lemma pgm_alloc m :
    Pmap m →
    ⊢ |==> ∃ γ, pgm_auth γ 1 m ∗ [∗ map] k ↦ v ∈ m, k □↪[γ] v.
  Proof.
    intros HPmap.
    iMod (pgm_alloc_strong (λ _, True) m) as (γ) "[_ Hmap]".
    - done.
    - by apply pred_infinite_True.
    - eauto.
  Qed.
  Lemma pgm_alloc_empty :
    ⊢ |==> ∃ γ, pgm_auth γ 1 (∅ : gmap K V).
  Proof.
    intros. iMod (pgm_alloc ∅) as (γ) "(Hauth & _)"; eauto.
    eapply Pmap_init.
  Qed.

  Global Instance pgm_auth_timeless γ q m : Timeless (pgm_auth γ q m).
  Proof. unseal. apply _. Qed.
  Global Instance pgm_auth_fractional γ m : Fractional (λ q, pgm_auth γ q m)%I.
  Proof. intros p q. unseal. rewrite -own_op -gmap_view_plus_auth_dfrac_op //. Qed.
  Global Instance pgm_auth_as_fractional γ q m :
    AsFractional (pgm_auth γ q m) (λ q, pgm_auth γ q m)%I q.
  Proof. split; first done. apply _. Qed.

  Lemma pgm_auth_valid_prop γ q m : pgm_auth γ q m -∗ ⌜Pmap m⌝%Qp.
  Proof.
    unseal. iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %(?&?)%gmap_view_plus_auth_dfrac_valid.
    iPureIntro. apply (H1 zero).
  Qed.
  Lemma pgm_auth_valid γ q m : pgm_auth γ q m -∗ ⌜q ≤ 1⌝%Qp.
  Proof.
    unseal. iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %(?&?)%gmap_view_plus_auth_dfrac_valid.
    done.
  Qed.
  Lemma pgm_auth_valid_2 γ q1 q2 m1 m2 :
    pgm_auth γ q1 m1 -∗ pgm_auth γ q2 m2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ m1 = m2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %(?&?&?)%gmap_view_plus_auth_dfrac_op_valid_L.
    done.
  Qed.
  Lemma pgm_auth_agree γ q1 q2 m1 m2 :
    pgm_auth γ q1 m1 -∗ pgm_auth γ q2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (pgm_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  (** * Lemmas about the interaction of [pgm_auth] with the elements *)
  Lemma pgm_lookup {γ q m k dq v} :
    pgm_auth γ q m -∗ k □↪[γ]{dq} v -∗ ⌜m !! k = Some v⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    iDestruct (own_valid_2 with "Hauth Hel") as %[?[?(?&?)]]%gmap_view_plus_both_dfrac_valid_L.
    eauto.
  Qed.

  Lemma pgm_lookup_pers {γ q m k vp} :
    pgm_auth γ q m -∗ k □↪[γ]= vp -∗ ⌜∃ v, vp = Fpers v ∧ m !! k = Some v⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    iDestruct (own_valid_2 with "Hauth Hel") as %HH.
    unshelve eapply cmra_valid_validN in HH. 1: exact zero.
    eapply gmap_view_plus_pers_both_dfrac_validN in HH as (Hq&v&Hv1&Hv2&Hprop).
    apply discrete in Hv1,Hv2. 2-3: apply _.
    apply leibniz_equiv in Hv1,Hv2.
    iPureIntro. by eexists.
  Qed.

  Lemma pgm_insert {γ m} k v :
    m !! k = None →
    (Pmap m → Pmap (<[k := v]> m)) →
    pgm_auth γ 1 m ==∗ pgm_auth γ 1 (<[k := v]> m) ∗ k □↪[γ] v.
  Proof.
    unseal. intros ??. rewrite -own_op.
    iApply own_update. rewrite gmap_view_plus_frag_get_persistent. 
    apply: gmap_view_plus_alloc; done.
  Qed.
  Lemma pgm_insert_persist {γ m} k v :
    m !! k = None →
    (Pmap m → Pmap (<[k := v]> m)) →
    pgm_auth γ 1 m ==∗ pgm_auth γ 1 (<[k := v]> m) ∗ k □↪[γ]□ v.
  Proof.
    iIntros (??) "Hauth".
    iMod (pgm_insert k with "Hauth") as "[$ Helem]"; try done.
    iApply pgm_elem_persist. done.
  Qed.

  Lemma pgm_update {γ m k v} w :
    Fpers v = Fpers w →
    (Pmap m → Pmap (<[k := w]> m)) →
    pgm_auth γ 1 m -∗ k □↪[γ] v ==∗ pgm_auth γ 1 (<[k := w]> m) ∗ k □↪[γ] w.
  Proof.
    unseal. intros Hpers Hprop. apply bi.wand_intro_r. rewrite -!own_op.
    apply own_update. apply: gmap_view_plus_update; first done.
    intros n; apply Hprop.
  Qed.

  (** Big-op versions of above lemmas *)
  Lemma pgm_lookup_big {γ q m} m0 :
    pgm_auth γ q m -∗
    ([∗ map] k↦v ∈ m0, k □↪[γ] v) -∗
    ⌜m0 ⊆ m⌝.
  Proof.
    iIntros "Hauth Hfrag". rewrite map_subseteq_spec. iIntros (k v Hm0).
    iDestruct (pgm_lookup with "Hauth [Hfrag]") as %->.
    { rewrite big_sepM_lookup; done. }
    done.
  Qed.

  Lemma pgm_insert_big {γ m} m' :
    m' ##ₘ m →
    (Pmap m → Pmap (m' ∪ m)) →
    pgm_auth γ 1 m ==∗
    pgm_auth γ 1 (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k □↪[γ] v).
  Proof.
    unseal. intros ??. rewrite -big_opM_own_1 -own_op.
    apply own_update. setoid_rewrite gmap_view_plus_frag_get_persistent.
    rewrite big_opM_op.
    apply: gmap_view_plus_alloc_big; done.
  Qed.

  Lemma pgm_insert_persist_big {γ m} m' :
    m' ##ₘ m →
    (Pmap m → Pmap (m' ∪ m)) →
    pgm_auth γ 1 m ==∗
    pgm_auth γ 1 (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k □↪[γ]□ v).
  Proof.
    iIntros (Hdisj Hprop) "Hauth".
    iMod (pgm_insert_big m' with "Hauth") as "[$ Helem]"; try done.
    iApply big_sepM_bupd. iApply (big_sepM_impl with "Helem").
    iIntros "!#" (k v) "_". iApply pgm_elem_persist.
  Qed.

  Theorem pgm_update_big {γ m} m0 m1 :
    dom m0 = dom m1 →
    (∀ k v0 v1, m0 !! k = Some v0 → m1 !! k = Some v1 → Fpers v0 = Fpers v1) →
    (Pmap (m1 ∪ m)) →
    pgm_auth γ 1 m -∗
    ([∗ map] k↦v ∈ m0, k □↪[γ] v) ==∗
    pgm_auth γ 1 (m1 ∪ m) ∗
        [∗ map] k↦v ∈ m1, k □↪[γ] v.
  Proof.
    iIntros (???) "Hauth Hfrag". iMod (pgm_elems_unseal with "Hfrag") as "Hfrag".
    unseal. rewrite -big_opM_own_1 -own_op.
    iApply (own_update_2 with "Hauth Hfrag").
    apply: gmap_view_plus_update_big; done.
  Qed.

  Lemma pgm_lookup_prop {γ q m} m0 :
    ([∗ map] k↦v ∈ m0, ∃ dq, k □↪[γ]{dq} v) -∗
    ⌜Pmap m0⌝.
  Proof.
    iIntros "Hfrag". unseal.
    epose (∃ (m1 : gmap K (prod V dfrac)), ⌜dom m1 = dom m0⌝ ∧ ⌜∀ k v dq, m1 !! k = Some (v,dq) → m0 !! k = Some v⌝ ∧ (⌜m1 = ∅⌝ ∨ own γ (◯V (fmap (λ '(v,dq), (Some (dq, to_agree v), to_agree (Fpers v))) m1)
            : gmap_view_pluspers.gmap_view_plusUR _)))%I.
    iAssert b with "[Hfrag]" as "(%m1&%Hdom&%Hcont&[->|Hm1])"; unfold b; clear b.
    - iStopProof.
      induction m0 as [|k v m0 Hne IH] using map_ind; iStartProof; iIntros "Hfrag".
      { iExists ∅; iSplit. 1: rewrite !dom_empty_L //.
        iSplit; last by iLeft.
        iPureIntro. intros k v ? []%lookup_empty_Some. }
      iPoseProof (big_sepM_insert with "Hfrag") as "((%dq&Hpto)&Hfrag)"; first done.
      iPoseProof (IH with "Hfrag") as "(%m1&%Hdom&%Hcont&[->|IH])".
      + iExists {[ k := (v,dq) ]}. iSplit.
        1: iPureIntro; rewrite dom_empty_L in Hdom; rewrite dom_insert_L dom_singleton_L -Hdom; set_solver.
        iSplit; last (iRight; erewrite map_fmap_singleton; iApply "Hpto").
        iPureIntro. intros k' v' dq' [<- [= <- <-]]%lookup_singleton_Some. by rewrite lookup_insert.
      + iExists (<[ k := (v,dq) ]> m1). iSplit.
        1: iPureIntro; rewrite dom_insert_L; set_solver.
        iSplit.
        { iPureIntro; intros k' v' dq' [[-> [= -> ->]]|[Hne1 HH]]%lookup_insert_Some.
          1: by rewrite lookup_insert.
          rewrite lookup_insert_ne; first by eapply Hcont. done. }
        iRight.
        iPoseProof (own_op with "[$Hpto $IH]") as "HH".
        unfold gmap_view_plus_frag. rewrite -view_frag_op.
        rewrite fmap_insert.
        rewrite (@insert_singleton_op _ _ _ _ ((prodR (optionR (prodR dfracR (agreeR (leibnizO V)))) (agreeR (leibnizO Vpers))))).
        2: { rewrite lookup_fmap. destruct (m1 !! k) eqn:Heqn; last done.
             eapply elem_of_dom_2 in Heqn. eapply not_elem_of_dom in Hne. by rewrite Hdom in Heqn. }
        done.
    - iPureIntro. enough (m0 = ∅) as -> by eapply Pmap_init.
      rewrite dom_empty_L in Hdom. eapply dom_empty_inv_L. done.
    - iDestruct (own_valid with "Hm1") as %Hm1.
      iPureIntro.
      apply view_frag_valid in Hm1.
      specialize (Hm1 zero) as (mv&Hmv&Hmprop).
      cbn in *.
      eapply Pmap_mono; first done.
      eapply map_subseteq_spec.
      intros k v Hin.
      destruct (m1 !! k) as [[v' dq]|] eqn:Heq; last first.
      { exfalso. apply elem_of_dom_2 in Hin. eapply not_elem_of_dom in Heq. by rewrite Hdom in Heq. }
      epose proof (Hcont _ _ _ Heq) as Heq2. simplify_eq.
      eapply (map_Forall_lookup_1 _ _ k) in Hmv; last first.
      { rewrite lookup_fmap Heq; done. }
      destruct Hmv as (v'&Hmv'&Hagr1&Hagr2&Hdv). cbn in *.
      rewrite Hmv'. f_equal.
      eapply @to_agree_injN, discrete_iff in Hagr2; last apply _.
      done.
  Qed.

End lemmas.
