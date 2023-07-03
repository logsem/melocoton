From Coq.QArith Require Import Qcanon.
From iris.algebra Require Export view gmap frac dfrac.
From iris.algebra Require Import local_updates proofmode_classes big_op.
From iris.prelude Require Import options.

(** * CMRA for a "view of a gmap" with a persistent part. *)

Local Definition gmap_view_plus_fragUR (K : Type) `{Countable K} `{SI: indexT} (V Vpers : ofe) : ucmra :=
  gmapUR K (prodR (optionR (prodR dfracR (agreeR V))) (agreeR Vpers)).

(** View relation. *)
Section rel.
  Context (K : Type) `{Countable K} `{SI: indexT} (V Vpers : ofe) (Fpers : V → Vpers) {HF : NonExpansive Fpers}.
  Set Default Proof Using "HF".
  Implicit Types (m : gmap K V) (k : K) (v : V) (n : index).
  Implicit Types (f : gmap K (option (dfrac * agree V) * agree Vpers)).

  Local Definition gmap_view_plus_rel_raw n m f : Prop :=
    map_Forall (λ k '(dvo, vp), ∃ v, m !! k = Some v ∧ vp ≡{n}≡ to_agree (Fpers v) ∧
                                from_option (λ dv, dv.2 ≡{n}≡ to_agree v ∧ ✓ dv.1) True dvo) f.

  Local Lemma gmap_view_plus_rel_raw_mono n1 n2 m1 m2 f1 f2 :
    gmap_view_plus_rel_raw n1 m1 f1 →
    m1 ≡{n2}≡ m2 →
    f2 ≼{n2} f1 →
    n2 ⪯ᵢ n1 →
    gmap_view_plus_rel_raw n2 m2 f2.
  Proof.
    intros Hrel Hm Hf Hn k [dvo vp] Hk.
    (* For some reason applying the lemma in [Hf] does not work... *)
    destruct (lookup_includedN n2 f2 f1) as [Hf' _]. specialize (Hf' Hf). clear Hf.
    specialize (Hf' k). rewrite Hk in Hf'.
    apply option_includedN in Hf'.
    destruct Hf' as [[=]|(? & [dvo' vp'] & [= <-] & Hf1 & Hincl)].
    specialize (Hrel _ _ Hf1) as (v & Hm1 & Hpval & Hopt). simpl in *.
    specialize (Hm k).
    edestruct (dist_Some_inv_l _ _ _ _ Hm Hm1) as (v' & Hm2 & Hv).
    exists v'. split; first done.
    destruct Hincl as [[Heqdvo Heqvp]|[Hincldvo Hinclvp]%pair_includedN].
    - simpl in *. split.
      + rewrite Heqvp -HF; last eassumption.
        by eapply dist_le.
      + destruct dvo as [[q va]|]; last done.
        destruct dvo' as [[q' va']|]; apply dist_option_Forall2 in Heqdvo.
        2: exfalso; by inversion Heqdvo.
        apply Some_dist_inj in Heqdvo.
        apply pair_dist_inj in Heqdvo as [Heqq Heqva].
        destruct Hopt as [Hq Hva].
        split; last by rewrite Heqq.
        cbn. rewrite Heqva -Hv. by eapply dist_le.
    - simpl in *. split.
      + rewrite -Hv. etrans; last first.
        { eapply dist_le; last eassumption. done. }
        eapply agree_valid_includedN; last done.
        eapply cmra_validN_le; last eassumption.
        rewrite Hpval. done.
      + destruct dvo as [[q va]|]; last done.
        destruct dvo' as [[q' va']|]; last by eapply is_Some_includedN in Hincldvo as [x Hx].
        apply Some_includedN in Hincldvo as [[Heqq Heqva]|[Hinclq Hinclva]%pair_includedN].
        * destruct Hopt as [Hq Hva].
          split; last by rewrite Heqq.
          cbn in *|-*. rewrite Heqva -Hv. by eapply dist_le.
        * cbn in *|-*. destruct Hopt as [Hva Hq].
          rewrite <-cmra_discrete_included_iff in Hinclq.
          split; last by eapply cmra_valid_included.
          rewrite -Hv.
          eapply agree_valid_includedN. 2: etrans; first done.
          1: done. eapply @cmra_includedN_le; last done.
          by rewrite Hva.
  Qed.

  Local Lemma gmap_view_plus_rel_raw_valid n m f :
    gmap_view_plus_rel_raw n m f → ✓{n} f.
  Proof.
    intros Hrel k. destruct (f !! k) as [[[[q va]|] vp]|] eqn:Hf; rewrite Hf; last done.
    all: specialize (Hrel _ _ Hf) as (v & Hm1 & Hpval & Hopt ); simpl in *.
    1: destruct Hopt as [Hva Hq].
    all: split; first split; simpl.
    - apply Hq.
    - rewrite Hva. done.
    - rewrite Hpval. done.
    - rewrite Hpval. done.
  Qed.

  Local Lemma gmap_view_plus_rel_raw_unit n :
    ∃ m, gmap_view_plus_rel_raw n m ε.
  Proof. exists ∅. apply: map_Forall_empty. Qed.

  Local Canonical Structure gmap_view_plus_rel : view_rel (gmapO K V) (gmap_view_plus_fragUR K V Vpers) :=
    ViewRel gmap_view_plus_rel_raw gmap_view_plus_rel_raw_mono
            gmap_view_plus_rel_raw_valid gmap_view_plus_rel_raw_unit.

  Local Lemma gmap_view_plus_rel_exists_1 n f:
    (∃ m, gmap_view_plus_rel n m f) → ✓{n} f.
  Proof.
    intros [m Hrel]. eapply gmap_view_plus_rel_raw_valid, Hrel.
  Qed.
  
  Local Lemma gmap_view_plus_rel_exists n f:
    map_Forall (λ _ '(dvo, vp), ∃ vax, vp ≡{n}≡ to_agree (Fpers vax) ∧
        from_option  (λ '(_, va),  to_agree vax ≡{n}≡ va ) True dvo) f →
    (∃ m, gmap_view_plus_rel n m f) ↔ ✓{n} f.
  Proof.
    intros Hprop.
    split.
    { intros [m Hrel]. eapply gmap_view_plus_rel_raw_valid, Hrel. }
    intros Hf.
    cut (∃ m, gmap_view_plus_rel n m f ∧ ∀ k, f !! k = None → m !! k = None).
    { naive_solver. }
    revert Hprop.
    induction f as [|k [dvo vp] f Hk' IH] using map_ind; intros Hprop.
    { exists ∅. split; [|done]. apply: map_Forall_empty. }
    apply map_Forall_insert in Hprop as [Hopt1 Hprop]; last done.
    move: (Hf k). rewrite lookup_insert=> -[/= Ha Hb].
    destruct (to_agree_uninjN n vp) as [vpv ?]; [done|].
    destruct IH as (m & Hm & Hdom).
    { intros k'. destruct (decide (k = k')) as [->|?]; [by rewrite Hk'|].
      move: (Hf k'). by rewrite lookup_insert_ne. }
    { done. }
    destruct Hopt1 as (vax & Hvax1 & Hvax2).
    exists (<[k:=vax]> m).
    rewrite /gmap_view_plus_rel /= /gmap_view_plus_rel_raw map_Forall_insert //=. split_and!.
    - exists vax. rewrite lookup_insert. split_and!; try done.
      destruct dvo as [[q va]|]; try done.
      cbn. split; last apply Ha. symmetry; apply Hvax2.
    - eapply map_Forall_impl; [apply Hm|]; simpl.
      intros k' [dvo' vp'] (v'&?&?&?). exists v'.
      rewrite lookup_insert_ne; naive_solver.
    - intros k'. rewrite !lookup_insert_None. naive_solver.
  Qed.

  Local Lemma gmap_view_plus_rel_unit n m : gmap_view_plus_rel n m ε.
  Proof. apply: map_Forall_empty. Qed.

  Local Lemma gmap_view_plus_rel_discrete :
    OfeDiscrete V → OfeDiscrete Vpers → ViewRelDiscrete gmap_view_plus_rel.
  Proof.
    intros ? ? n m f Hrel k [dvo vp] Hk.
    destruct (Hrel _ _ Hk) as (v & Hm & Hvo & Hopt).
    exists v. split; first done.
    destruct dvo as [[q va]|]; (split; last split).
    - by do 2 (eapply discrete_iff; first by apply _).
    - do 2 (eapply discrete_iff; first by apply _). apply Hopt.
    - apply Hopt.
    - by do 2 (eapply discrete_iff; first by apply _).
  Qed.
End rel.

Local Existing Instance gmap_view_plus_rel_discrete.
(** [gmap_view_plus] is a notation to give canonical structure search the chance
to infer the right instances (see [auth]). *)
Notation gmap_view_plus K V Fpers := (view (@gmap_view_plus_rel_raw K _ _ _ V _ Fpers)).
Definition gmap_view_plusO (K : Type) `{Countable K} `{SI: indexT} (V Vpers : ofe) (Fpers : V → Vpers) {HF:NonExpansive Fpers} : ofe :=
  viewO (gmap_view_plus_rel K V _ Fpers).
Definition gmap_view_plusR (K : Type) `{Countable K} `{SI: indexT} (V Vpers : ofe) (Fpers : V → Vpers) {HF:NonExpansive Fpers} : cmra :=
  viewR (gmap_view_plus_rel K V _ Fpers).
Definition gmap_view_plusUR (K : Type) `{Countable K} `{SI: indexT} (V Vpers : ofe) (Fpers : V → Vpers) {HF:NonExpansive Fpers} : ucmra :=
  viewUR (gmap_view_plus_rel K V _ Fpers).

Section definitions.
  Context {K : Type} `{Countable K} `{SI: indexT} {V Vpers : ofe} {Fpers : V → Vpers} {HF : NonExpansive Fpers}.

  Definition gmap_view_plus_auth (dq : dfrac) (m : gmap K V) : gmap_view_plusR K V _ Fpers :=
    ●V{dq} m.
  Definition gmap_view_plus_frag (k : K) (dq : dfrac) (v : V) : gmap_view_plusR K V _ Fpers :=
    ◯V {[k := (Some (dq, to_agree v), to_agree (Fpers v))]}.
  Definition gmap_view_plus_pers (k : K) (vp : Vpers) : gmap_view_plusR K V _ Fpers :=
    ◯V {[k := (None, to_agree vp)]}.
End definitions.

Section lemmas.
  Context {K : Type} `{Countable K} `{SI: indexT} {V Vpers : ofe} {Fpers : V → Vpers} {HF : NonExpansive Fpers}.
  Implicit Types (m : gmap K V) (k : K) (q : Qp) (dp dq : dfrac) (v : V) (vp : Vpers).

  Global Instance : Params (@gmap_view_plus_auth) 6 := {}.
  Global Instance gmap_view_plus_auth_ne dq : NonExpansive (gmap_view_plus_auth (K:=K) (V:=V) dq).
  Proof. solve_proper. Qed.
  Global Instance gmap_view_plus_auth_proper dq : Proper ((≡) ==> (≡)) (gmap_view_plus_auth (K:=K) (V:=V) dq).
  Proof. apply ne_proper, _. Qed.

  Global Instance : Params (@gmap_view_plus_frag) 7 := {}.
  Global Instance gmap_view_plus_frag_ne k oq : NonExpansive (gmap_view_plus_frag (V:=V) k oq).
  Proof. solve_proper. Qed.
  Global Instance gmap_view_plus_frag_proper k oq : Proper ((≡) ==> (≡)) (gmap_view_plus_frag (V:=V) (Fpers:=Fpers) k oq).
  Proof. apply ne_proper, _. Qed.

  Global Instance : Params (@gmap_view_plus_pers) 8 := {}.
  Global Instance gmap_view_plus_pers_ne k : NonExpansive (gmap_view_plus_pers (Fpers:=Fpers) k).
  Proof. solve_proper. Qed.
  Global Instance gmap_view_plus_pers_proper k : Proper ((≡) ==> (≡)) (gmap_view_plus_pers (V:=V) (Fpers:=Fpers) k).
  Proof. apply ne_proper, _. Qed.

  Local Notation gmap_view_plus_auth := (gmap_view_plus_auth (Fpers:=Fpers)).
  Local Notation gmap_view_plus_frag := (gmap_view_plus_frag (Fpers:=Fpers)).
  Local Notation gmap_view_plus_pers := (gmap_view_plus_pers (Fpers:=Fpers)).

  (* Helper lemmas *)
  Local Lemma gmap_view_plus_rel_lookup_Some n m k dq v vp :
    gmap_view_plus_rel K V Vpers Fpers n m {[k := (Some (dq, to_agree v), to_agree vp)]} ↔ ✓ dq ∧ m !! k ≡{n}≡ Some v ∧ Fpers v ≡{n}≡ vp.
  Proof.
    split.
    - intros Hrel.
      edestruct (Hrel k (Some (dq, to_agree v), to_agree vp)) as (v' & Hm & Hvp & Hva & Hq).
      { by rewrite lookup_singleton. }
      simpl in *. apply (inj _) in Hva,Hvp. rewrite Hva Hvp Hm.
      done.
    - intros (Hdq & (v' & Hm & Hv')%dist_Some_inv_r' & Hvp) j [dvo vp'].
      destruct (decide (k = j)) as [<-|Hne]; last by rewrite lookup_singleton_ne.
      rewrite lookup_singleton. intros [= <- <-]. simpl.
      exists v'. rewrite -Hvp Hv'. split_and!; try done.
  Qed.

  Local Lemma gmap_view_plus_rel_lookup_None n m k vp :
    gmap_view_plus_rel K V Vpers Fpers n m {[k := (None, to_agree vp)]} ↔ ∃ v, m !! k ≡{n}≡ Some v ∧ Fpers v ≡{n}≡ vp.
  Proof.
    split.
    - intros Hrel.
      edestruct (Hrel k (None, to_agree vp)) as (v' & Hm & Hvp & _).
      { rewrite lookup_singleton. done. }
      simpl in *. apply (inj _) in Hvp. exists v'. rewrite Hvp Hm.
      done.
    - intros (v' & (v'' & Hm & Hv')%dist_Some_inv_r' & Hvp) j [dvo vp'].
      destruct (decide (k = j)) as [<-|Hne]; last by rewrite lookup_singleton_ne.
      rewrite lookup_singleton. intros [= <- <-]. simpl.
      exists v''. rewrite -Hvp Hv'. split_and!; try done.
  Qed.

  (** Composition and validity *)
  Lemma gmap_view_plus_auth_dfrac_op dp dq (m:gmap K V) :
    gmap_view_plus_auth (dp ⋅ dq) m ≡
    gmap_view_plus_auth dp m ⋅ gmap_view_plus_auth dq m.
  Proof. by rewrite /gmap_view_plus_auth view_auth_dfrac_op. Qed.
  Global Instance gmap_view_plus_auth_dfrac_is_op dq dq1 dq2 m :
    IsOp dq dq1 dq2 → IsOp' (gmap_view_plus_auth dq m) (gmap_view_plus_auth dq1 m) (gmap_view_plus_auth dq2 m).
  Proof. rewrite /gmap_view_plus_auth. apply _. Qed.

  Lemma gmap_view_plus_auth_dfrac_op_invN n dp m1 dq m2 :
    ✓{n} (gmap_view_plus_auth dp m1 ⋅ gmap_view_plus_auth dq m2) → m1 ≡{n}≡ m2.
  Proof. apply view_auth_dfrac_op_invN. Qed.
  Lemma gmap_view_plus_auth_dfrac_op_inv dp m1 dq m2 :
    ✓ (gmap_view_plus_auth dp m1 ⋅ gmap_view_plus_auth dq m2) → m1 ≡ m2.
  Proof. apply view_auth_dfrac_op_inv. Qed.
  Lemma gmap_view_plus_auth_dfrac_op_inv_L `{!LeibnizEquiv V} dq m1 dp m2 :
    ✓ (gmap_view_plus_auth dp m1 ⋅ gmap_view_plus_auth dq m2) → m1 = m2.
  Proof. apply view_auth_dfrac_op_inv_L, _. Qed.

  Lemma gmap_view_plus_auth_dfrac_validN m n dq : ✓{n} gmap_view_plus_auth dq m ↔ ✓ dq.
  Proof.
    rewrite view_auth_dfrac_validN. intuition eauto using gmap_view_plus_rel_unit.
  Qed.
  Lemma gmap_view_plus_auth_dfrac_valid m dq : ✓ gmap_view_plus_auth dq m ↔ ✓ dq.
  Proof.
    rewrite view_auth_dfrac_valid. intuition eauto using gmap_view_plus_rel_unit.
  Qed.
  Lemma gmap_view_plus_auth_valid m : ✓ gmap_view_plus_auth (DfracOwn 1) m.
  Proof. rewrite gmap_view_plus_auth_dfrac_valid. done. Qed.

  Lemma gmap_view_plus_auth_dfrac_op_validN n dq1 dq2 m1 m2 :
    ✓{n} (gmap_view_plus_auth dq1 m1 ⋅ gmap_view_plus_auth dq2 m2) ↔ ✓ (dq1 ⋅ dq2) ∧ m1 ≡{n}≡ m2.
  Proof.
    rewrite view_auth_dfrac_op_validN. intuition eauto using gmap_view_plus_rel_unit.
  Qed.
  Lemma gmap_view_plus_auth_dfrac_op_valid dq1 dq2 m1 m2 :
    ✓ (gmap_view_plus_auth dq1 m1 ⋅ gmap_view_plus_auth dq2 m2) ↔ ✓ (dq1 ⋅ dq2) ∧ m1 ≡ m2.
  Proof.
    rewrite view_auth_dfrac_op_valid. intuition eauto using gmap_view_plus_rel_unit.
  Qed.
  Lemma gmap_view_plus_auth_dfrac_op_valid_L `{!LeibnizEquiv V} dq1 dq2 m1 m2 :
    ✓ (gmap_view_plus_auth dq1 m1 ⋅ gmap_view_plus_auth dq2 m2) ↔ ✓ (dq1 ⋅ dq2) ∧ m1 = m2.
  Proof. unfold_leibniz. apply gmap_view_plus_auth_dfrac_op_valid. Qed.

  Lemma gmap_view_plus_auth_op_validN n m1 m2 :
    ✓{n} (gmap_view_plus_auth (DfracOwn 1) m1 ⋅ gmap_view_plus_auth (DfracOwn 1) m2) ↔ False.
  Proof. apply view_auth_op_validN. Qed.
  Lemma gmap_view_plus_auth_op_valid m1 m2 :
    ✓ (gmap_view_plus_auth (DfracOwn 1) m1 ⋅ gmap_view_plus_auth (DfracOwn 1) m2) ↔ False.
  Proof. apply view_auth_op_valid. Qed.

  Lemma gmap_view_plus_frag_validN n k dq v : ✓{n} gmap_view_plus_frag k dq v ↔ ✓ dq.
  Proof.
    rewrite view_frag_validN gmap_view_plus_rel_exists.
    1: rewrite singleton_validN pair_validN Some_validN pair_validN; naive_solver.
    eapply @map_Forall_singleton; first apply _. cbn.
    by exists v.
  Qed.
  Lemma gmap_view_plus_frag_valid k dq v : ✓ gmap_view_plus_frag k dq v ↔ ✓ dq.
  Proof.
    rewrite cmra_valid_validN. setoid_rewrite gmap_view_plus_frag_validN.
    naive_solver eauto using zero.
  Qed.

  Lemma gmap_view_plus_frag_op k dq1 dq2 v :
    gmap_view_plus_frag k (dq1 ⋅ dq2) v ≡ gmap_view_plus_frag k dq1 v ⋅ gmap_view_plus_frag k dq2 v.
  Proof. rewrite -view_frag_op singleton_op -pair_op -Some_op -pair_op !agree_idemp //. Qed.
  Lemma gmap_view_plus_frag_add k q1 q2 v :
    gmap_view_plus_frag k (DfracOwn (q1 + q2)) v ≡
      gmap_view_plus_frag k (DfracOwn q1) v ⋅ gmap_view_plus_frag k (DfracOwn q2) v.
  Proof. rewrite -gmap_view_plus_frag_op. done. Qed.

  Lemma gmap_view_plus_frag_op_validN n k dq1 dq2 v1 v2 :
    ✓{n} (gmap_view_plus_frag k dq1 v1 ⋅ gmap_view_plus_frag k dq2 v2) ↔
      ✓ (dq1 ⋅ dq2) ∧ v1 ≡{n}≡ v2.
  Proof.
    rewrite view_frag_validN;
    rewrite singleton_op -pair_op -Some_op -pair_op; split; intros Hass.
    - apply gmap_view_plus_rel_exists_1 in Hass.
      rewrite singleton_validN !pair_validN Some_validN !pair_validN !to_agree_op_validN in Hass.
      apply Hass.
    - destruct Hass as (Hass1&Hass2).
      apply gmap_view_plus_rel_exists.
      2: rewrite singleton_validN !pair_validN Some_validN !pair_validN !to_agree_op_validN; by rewrite Hass2.
      eapply @map_Forall_singleton; first apply _. cbn.
      exists v1. rewrite Hass2 !agree_idemp. done.
  Qed.

  Lemma gmap_view_plus_frag_op_valid k dq1 dq2 v1 v2 :
    ✓ (gmap_view_plus_frag k dq1 v1 ⋅ gmap_view_plus_frag k dq2 v2) ↔ ✓ (dq1 ⋅ dq2) ∧ v1 ≡ v2.
  Proof.
    rewrite view_frag_valid;
    rewrite singleton_op -pair_op -Some_op -pair_op; split; intros Hass.
    - eassert (∀ (n:index), _) as Hass2.
      { intros n. specialize (Hass n). apply gmap_view_plus_rel_exists_1 in Hass. exact Hass. }
      clear Hass. apply cmra_valid_validN in Hass2.
      rewrite singleton_valid !pair_valid Some_valid !pair_valid !to_agree_op_valid in Hass2.
      apply Hass2.
    - destruct Hass as (Hass1&Hass2).
      setoid_rewrite gmap_view_plus_rel_exists.
      1: rewrite -cmra_valid_validN singleton_valid !pair_valid Some_valid !pair_valid !to_agree_op_valid.
      1: split_and; try done.
      1: apply equiv_dist; intros n; eapply equiv_dist in Hass2; by rewrite Hass2.
      eapply @map_Forall_singleton; first apply _. cbn.
      exists v1. eapply equiv_dist in Hass2. rewrite Hass2 !agree_idemp. done.
  Qed.

  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  Lemma gmap_view_plus_frag_op_valid_L `{!LeibnizEquiv V} k dq1 dq2 v1 v2 :
    ✓ (gmap_view_plus_frag k dq1 v1 ⋅ gmap_view_plus_frag k dq2 v2) ↔ ✓ (dq1 ⋅ dq2) ∧ v1 = v2.
  Proof. unfold_leibniz. apply gmap_view_plus_frag_op_valid. Qed.


  Lemma gmap_view_plus_frag_pers_op_validN n k dq1 v1 vp2 :
    ✓{n} (gmap_view_plus_frag k dq1 v1 ⋅ gmap_view_plus_pers k vp2) ↔
      ✓ (dq1) ∧ Fpers v1 ≡{n}≡ vp2.
  Proof.
    rewrite view_frag_validN;
    rewrite singleton_op -pair_op Some_op_opM /=; split; intros Hass.
    - apply gmap_view_plus_rel_exists_1 in Hass; last done.
      rewrite singleton_validN !pair_validN Some_validN !pair_validN !to_agree_op_validN in Hass; split;
      apply Hass.
    - destruct Hass as (Hass1&Hass2).
      eapply gmap_view_plus_rel_exists.
      2: rewrite singleton_validN !pair_validN Some_validN !pair_validN !to_agree_op_validN; by rewrite -Hass2.
      eapply @map_Forall_singleton; first apply _. cbn.
      exists v1. rewrite Hass2 !agree_idemp. done.
  Qed.

  Lemma gmap_view_plus_frag_pers_op_valid k dq1 v1 vp2 :
    ✓ (gmap_view_plus_frag k dq1 v1 ⋅ gmap_view_plus_pers k vp2) ↔ ✓ (dq1) ∧ Fpers v1 ≡ vp2.
  Proof.
    rewrite view_frag_valid;
    rewrite singleton_op -pair_op Some_op_opM /=; split; intros Hass.
    - eassert (∀ (n:index), _) as Hass2.
      { intros n. specialize (Hass n). apply gmap_view_plus_rel_exists_1 in Hass; last done. exact Hass. }
      clear Hass. apply cmra_valid_validN in Hass2.
      rewrite singleton_valid !pair_valid Some_valid !pair_valid !to_agree_op_valid in Hass2; split;
      apply Hass2.
    - destruct Hass as (Hass1&Hass2).
      setoid_rewrite gmap_view_plus_rel_exists. 2: done.
      1: rewrite -cmra_valid_validN singleton_valid !pair_valid Some_valid !pair_valid !to_agree_op_valid.
      1: split_and; try done.
      eapply @map_Forall_singleton; first apply _. cbn.
      exists v1. eapply equiv_dist in Hass2. rewrite Hass2 !agree_idemp. done.
  Qed.

  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  Lemma gmap_view_plus_frag_pers_op_valid_L `{!LeibnizEquiv Vpers} k dq1 v1 vp2 :
    ✓ (gmap_view_plus_frag k dq1 v1 ⋅ gmap_view_plus_pers k vp2) ↔ ✓ (dq1) ∧ Fpers v1 = vp2.
  Proof. unfold_leibniz. apply gmap_view_plus_frag_pers_op_valid. Qed.


  Lemma gmap_view_plus_pers_op_validN n k vp1 vp2 :
    ✓{n} (gmap_view_plus_pers k vp1 ⋅ gmap_view_plus_pers k vp2) ↔
       vp1 ≡{n}≡ vp2 ∧ ∃ vax, Fpers vax ≡{n}≡ vp2.
  Proof.
    rewrite view_frag_validN;
    rewrite singleton_op -pair_op op_None_right_id /=; split; intros Hass.
    - apply gmap_view_plus_rel_exists_1 in Hass as Hass2; last done.
      rewrite singleton_validN !pair_validN !to_agree_op_validN in Hass2; split.
      1: apply Hass2.
      destruct Hass as [m Hm].
      apply map_Forall_singleton in Hm as (v & Hmv & Hagree & _).
      destruct (Hass2) as [_ Hass3]. rewrite Hass3 agree_idemp in Hagree.
      eexists. eapply to_agree_injN. by symmetry.
    - destruct Hass as (Hass1&vax&Hass2). eapply gmap_view_plus_rel_exists.
      2: rewrite singleton_validN !pair_validN !to_agree_op_validN; by rewrite -Hass1.
      eapply @map_Forall_singleton; first apply _. cbn.
      exists vax. rewrite Hass1 -!Hass2 !agree_idemp. done.
  Qed.

  Lemma gmap_view_plus_pers_op_valid k vp1 vp2 :
    ✓ (gmap_view_plus_pers k vp1 ⋅ gmap_view_plus_pers k vp2) ↔ vp1 ≡ vp2 ∧ ∀ n, ∃ vax, Fpers vax ≡{n}≡ vp2.
  Proof.
    rewrite view_frag_valid;
    rewrite singleton_op -pair_op op_None_right_id /=; split; intros Hass.
    - eassert (∀ (n:index), _) as Hass'.
      { intros n. specialize (Hass n). apply gmap_view_plus_rel_exists_1 in Hass; last done. exact Hass. }
      apply cmra_valid_validN in Hass' as Hass2.
      rewrite singleton_valid !pair_valid !to_agree_op_valid in Hass2; split.
      1: apply Hass2.
      intros n. specialize (Hass n).
      destruct Hass as [m Hm].
      apply map_Forall_singleton in Hm as (v & Hmv & Hagree & _).
      destruct (Hass2) as [_ Hass3]. rewrite Hass3 agree_idemp in Hagree.
      eexists. eapply to_agree_injN. by symmetry.
    - destruct Hass as (Hass1&Hass2).
      setoid_rewrite gmap_view_plus_rel_exists. 2: done.
      1: rewrite -cmra_valid_validN singleton_valid !pair_valid !to_agree_op_valid.
      1: split_and; try done.
      eapply @map_Forall_singleton; first apply _. cbn.
      destruct (Hass2 n) as (vax&Hass2').
      exists vax. eapply equiv_dist in Hass1. rewrite Hass1 !agree_idemp. split; last done.
      by rewrite -Hass2'.
  Qed.

  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  Lemma gmap_view_plus_pers_op_valid_L `{!LeibnizEquiv Vpers} k vp1 vp2 :
    ✓ (gmap_view_plus_pers k vp1 ⋅ gmap_view_plus_pers k vp2) ↔ vp1 = vp2 ∧ ∀ n, ∃ vax, Fpers vax ≡{n}≡ vp2.
  Proof. unfold_leibniz. setoid_rewrite gmap_view_plus_pers_op_valid; done. Qed.


  Lemma gmap_view_plus_both_dfrac_validN n dp m k dq v :
    ✓{n} (gmap_view_plus_auth dp m ⋅ gmap_view_plus_frag k dq v) ↔
      ✓ dp ∧ ✓ dq ∧ m !! k ≡{n}≡ Some v.
  Proof.
    rewrite /gmap_view_plus_auth /gmap_view_plus_frag.
    rewrite view_both_dfrac_validN gmap_view_plus_rel_lookup_Some.
    naive_solver.
  Qed.
  Lemma gmap_view_plus_both_validN n m k dq v :
    ✓{n} (gmap_view_plus_auth (DfracOwn 1) m ⋅ gmap_view_plus_frag k dq v) ↔
      ✓ dq ∧ m !! k ≡{n}≡ Some v.
  Proof. rewrite gmap_view_plus_both_dfrac_validN. naive_solver done. Qed.
  Lemma gmap_view_plus_both_dfrac_valid dp m k dq v :
    ✓ (gmap_view_plus_auth dp m ⋅ gmap_view_plus_frag k dq v) ↔
    ✓ dp ∧ ✓ dq ∧ m !! k ≡ Some v.
  Proof.
    rewrite /gmap_view_plus_auth /gmap_view_plus_frag.
    rewrite view_both_dfrac_valid. setoid_rewrite gmap_view_plus_rel_lookup_Some.
    split=>[[Hq Hm]|[Hq Hm]].
    - split; first done. split.
      + apply (Hm zero).
      + apply equiv_dist=>n. apply Hm.
    - split; first done. intros n. split.
      + apply Hm.
      + split; last done. revert n. apply equiv_dist. apply Hm.
  Qed.
  Lemma gmap_view_plus_both_dfrac_valid_L `{!LeibnizEquiv V} dp m k dq v :
    ✓ (gmap_view_plus_auth dp m ⋅ gmap_view_plus_frag k dq v) ↔
    ✓ dp ∧ ✓ dq ∧ m !! k = Some v.
  Proof. unfold_leibniz. apply gmap_view_plus_both_dfrac_valid. Qed.
  Lemma gmap_view_plus_both_valid m k dq v :
    ✓ (gmap_view_plus_auth (DfracOwn 1) m ⋅ gmap_view_plus_frag k dq v) ↔
    ✓ dq ∧ m !! k ≡ Some v.
  Proof. rewrite gmap_view_plus_both_dfrac_valid. naive_solver done. Qed.
  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  Lemma gmap_view_plus_both_valid_L `{!LeibnizEquiv V} m k dq v :
    ✓ (gmap_view_plus_auth (DfracOwn 1) m ⋅ gmap_view_plus_frag k dq v) ↔
    ✓ dq ∧ m !! k = Some v.
  Proof. unfold_leibniz. apply gmap_view_plus_both_valid. Qed.


  Lemma gmap_view_plus_pers_both_dfrac_validN n dp m k vp :
    ✓{n} (gmap_view_plus_auth dp m ⋅ gmap_view_plus_pers k vp) ↔
      ✓ dp ∧ ∃ v, m !! k ≡{n}≡ Some v ∧  Fpers v ≡{n}≡ vp.
  Proof.
    rewrite /gmap_view_plus_auth /gmap_view_plus_pers.
    rewrite view_both_dfrac_validN gmap_view_plus_rel_lookup_None.
    naive_solver.
  Qed.
  Lemma gmap_view_plus_pers_both_validN n m k vp :
    ✓{n} (gmap_view_plus_auth (DfracOwn 1) m ⋅ gmap_view_plus_pers k vp) ↔
      ∃ v, m !! k ≡{n}≡ Some v ∧ Fpers v ≡{n}≡ vp.
  Proof. rewrite gmap_view_plus_pers_both_dfrac_validN. naive_solver done. Qed.





  (** Frame-preserving updates *)
  Lemma gmap_view_plus_alloc m k dq v :
    m !! k = None →
    ✓ dq →
    gmap_view_plus_auth (DfracOwn 1) m ~~> gmap_view_plus_auth (DfracOwn 1) (<[k := v]> m) ⋅ (gmap_view_plus_frag k dq v ⋅ gmap_view_plus_pers k (Fpers v)).
  Proof.
    intros Hfresh Hdq. apply view_update_alloc=>n bf Hrel j [dvo vp] /=.
    rewrite lookup_op singleton_op -pair_op op_None_right_id.
    destruct (decide (j = k)) as [->|Hne].
    - assert (bf !! k = None) as Hbf.
      { destruct (bf !! k) as [[df' va']|] eqn:Hbf; last done.
        specialize (Hrel _ _ Hbf). destruct Hrel as (v' & Hm & _).
        exfalso. rewrite Hm in Hfresh. done. }
      rewrite lookup_singleton Hbf right_id.
      intros [= <- <-]. eexists. rewrite lookup_insert. rewrite @agree_idemp. do 2 (split; first done).
      cbn. done.
    - rewrite lookup_singleton_ne; last done.
      rewrite left_id=>Hbf.
      specialize (Hrel _ _ Hbf). destruct Hrel as (v' & Hm & Hvp & Hopt).
      eexists. split_and!; try done.
      rewrite lookup_insert_ne //.
  Qed.

  Lemma gmap_view_plus_alloc_big m m' dq :
    m' ##ₘ m →
    ✓ dq →
    gmap_view_plus_auth (DfracOwn 1) m ~~>
      gmap_view_plus_auth (DfracOwn 1) (m' ∪ m) ⋅ (([^op map] k↦v ∈ m', gmap_view_plus_frag k dq v) ⋅ ([^op map] k↦v ∈ m', gmap_view_plus_pers k (Fpers v))).
  Proof.
    intros. induction m' as [|k v m' ? IH] using map_ind; decompose_map_disjoint.
    { rewrite !big_opM_empty left_id_L !right_id. done. }
    rewrite IH //.
    rewrite -!big_opM_op.
    rewrite big_opM_insert // assoc.
    apply cmra_update_op; last done.
    rewrite -insert_union_l. apply (gmap_view_plus_alloc _ k dq); last done.
    by apply lookup_union_None.
  Qed.

  Lemma gmap_view_plus_update m k v v' :
    Fpers v ≡ Fpers v' →
    gmap_view_plus_auth (DfracOwn 1) m ⋅ gmap_view_plus_frag k (DfracOwn 1) v ~~>
      gmap_view_plus_auth (DfracOwn 1) (<[k := v']> m) ⋅ gmap_view_plus_frag k (DfracOwn 1) v'.
  Proof.
    intros Hpers. apply view_update=>n bf Hrel j [dvo vp] /=.
    destruct (decide (j = k)) as [->|Hne]; last first.
    - rewrite gmap_op lookup_merge lookup_singleton_ne; last done.
      destruct (bf !! j) eqn:Heq; rewrite Heq; try done.
      cbn. rewrite op_None_left_id. intros [= ->]. rewrite lookup_insert_ne; last done.
      eapply (map_Forall_lookup_1 _ _ j) in Hrel.
      2: rewrite gmap_op lookup_merge lookup_singleton_ne // Heq //.
      apply Hrel.
    - rewrite gmap_op lookup_merge lookup_singleton /=.
      destruct (bf !! k) as [[[[q' va']|] vp']|] eqn:Heq; rewrite Heq;
      (eapply (map_Forall_lookup_1 _ _ k) in Hrel; last
        rewrite gmap_op lookup_merge lookup_singleton Heq //).
      + rewrite -!Some_op -!pair_op -!Some_op -!pair_op in Hrel|-*.
        intros [= <- <-]. destruct Hrel as (v0 & Hm & Hagr & Hval & Hq).
        cbn in Hq. exfalso. rewrite cmra_comm in Hq.
        apply dfrac_valid_own_r in Hq. eapply Qp.le_ngt; last exact Hq.
        reflexivity.
      + rewrite -!Some_op -!pair_op !op_None_right_id in Hrel|-*.
        intros [= <- <-].
        destruct Hrel as (v0 & Hm & Hagr & Hagr2 & Hq). cbn in Hagr2, Hq.
        apply to_agree_injN in Hagr2.
        eexists; cbn; split_and!; try done.
        1: by rewrite lookup_insert.
        1: by rewrite -Hagr2 Hpers in Hagr.
      + rewrite op_None_right_id.
        intros [= <- <-]. cbn in Hrel|-*.
        destruct Hrel as (v0 & Hm & Hagr & Hagr2 & Hq).
        eexists; cbn; split_and!; try done.
        by rewrite lookup_insert.
  Qed.

  Lemma gmap_view_plus_update_big m m0 m1 :
    dom m0 = dom m1 →
    (∀ k v0 v1, m0 !! k = Some v0 → m1 !! k = Some v1 → Fpers v0 ≡ Fpers v1) →
    gmap_view_plus_auth (DfracOwn 1) m ⋅ ([^op map] k↦v ∈ m0, gmap_view_plus_frag k (DfracOwn 1) v) ~~>
      gmap_view_plus_auth (DfracOwn 1) (m1 ∪ m) ⋅ ([^op map] k↦v ∈ m1, gmap_view_plus_frag k (DfracOwn 1) v).
  Proof.
    intros Hdom%eq_sym. revert m1 Hdom.
    induction m0 as [|k v m0 Hnotdom IH] using map_ind; intros m1 Hdom Hequiv.
    { rewrite dom_empty_L in Hdom.
      apply dom_empty_iff_L in Hdom as ->.
      rewrite left_id_L big_opM_empty. done. }
    rewrite dom_insert_L in Hdom.
    assert (k ∈ dom m1) as Hindom by set_solver.
    apply elem_of_dom in Hindom as [v' Hlookup].
    rewrite big_opM_insert //.
    rewrite [gmap_view_plus_frag _ _ _ ⋅ _]comm assoc.
    rewrite (IH (delete k m1)); last first.
    { intros k0 v0 v1 H1 [Hne H2]%lookup_delete_Some.
      eapply Hequiv; try done. by rewrite lookup_insert_ne. }
    { rewrite dom_delete_L Hdom.
      apply not_elem_of_dom in Hnotdom. set_solver -Hdom. }
    rewrite -assoc [_ ⋅ gmap_view_plus_frag _ _ _]comm assoc.
    rewrite (gmap_view_plus_update _ _ _ v'); last first.
    { eapply Hequiv; last done. by rewrite lookup_insert. }
    rewrite (big_opM_delete _ m1 k v') // -assoc.
    rewrite insert_union_r; last by rewrite lookup_delete.
    rewrite union_delete_insert //.
  Qed.

  Lemma gmap_view_plus_auth_persist dq m :
    gmap_view_plus_auth dq m ~~> gmap_view_plus_auth DfracDiscarded m.
  Proof. apply view_update_auth_persist. Qed.

  Lemma gmap_view_plus_frag_dfractional k dq v P :
    dq ~~>: P →
    gmap_view_plus_frag k dq v ~~>: (λ x, ∃ dq', x = gmap_view_plus_frag k dq' v ∧ P dq').
  Proof.
    intros Hdq.
    eapply cmra_updateP_weaken.
    1: apply view_updateP_frag.
    2: { intros y (b'&->&HP). apply HP. }
    intros m n bf Hrel. cbn. cbv in bf. cbn in Hrel.
    destruct (bf !! k) as [[[[dq' va]|] vp]|] eqn:Heq; last first.
    - eapply (map_Forall_lookup_1 _ _ k ((Some (dq,_),_))) in Hrel as Hrel2; first destruct Hrel2 as (v' & Hm & Hpers & Hva & Hdf).
      2: by rewrite lookup_op Heq lookup_singleton. cbn in Hdf.
      destruct (Hdq zero None Hdf) as (dq'&HP&Hdq').
      eexists; split; first by eexists.
      intros j [dvo vp]. cbn.
      rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
      + rewrite lookup_singleton.
        rewrite Some_op_opM Heq. cbn. intros [= <- <-].
        exists v'. rewrite assoc; done.
      + rewrite lookup_singleton_ne //.
        rewrite left_id=>Hbf.
        edestruct (Hrel j (dvo,vp)) as (v'' & Hm' & Hpers' & Hdvo).
        { rewrite lookup_op lookup_singleton_ne // left_id. done. }
        simpl in *. eexists. done.
    - eapply (map_Forall_lookup_1 _ _ k ((Some (dq,_),_))) in Hrel as Hrel2; first destruct Hrel2 as (v' & Hm & Hpers & Hva & Hdf).
      2: by rewrite lookup_op Heq lookup_singleton. cbn in Hdf.
      destruct (Hdq zero None Hdf) as (dq'&HP&Hdq').
      eexists; split; first by eexists.
      intros j [dvo vp']. cbn.
      rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
      + rewrite lookup_singleton.
        rewrite Some_op_opM Heq. cbn. intros [= <- <-].
        exists v'. rewrite assoc; done.
      + rewrite lookup_singleton_ne //.
        rewrite left_id=>Hbf.
        epose proof (Hrel j (_,_)) as (v'' & Hm' & Hpers' & Hdvo).
        { rewrite lookup_op lookup_singleton_ne // left_id. done. }
        simpl in *. eexists. done.
    - eapply (map_Forall_lookup_1 _ _ k (Some (_,_) ,_)) in Hrel as Hrel2; first destruct Hrel2 as (v' & Hm & Hvp & Hdf & Hva).
      2: rewrite lookup_op Heq lookup_singleton -Some_op -pair_op -Some_op -pair_op //.
      destruct (Hdq zero (Some dq') Hva) as (dq'1&HP&Hdq').
      eexists; split; first by eexists.
      intros j [df va']. cbn.
      rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
      + rewrite lookup_singleton Heq.
        do 2 rewrite -Some_op -pair_op. intros [= <- <-].
        exists v'. rewrite assoc; split; try done.
      + rewrite lookup_singleton_ne //.
        rewrite left_id=>Hbf.
        epose proof (Hrel j ( _,_)) as (v'' & Hm' & Hvp' & Hdvo).
        { rewrite lookup_op lookup_singleton_ne // left_id. done. }
        simpl in *. eexists. done.
  Qed.

  Lemma gmap_view_plus_frag_persist k dq v :
    gmap_view_plus_frag k dq v ~~> gmap_view_plus_frag k DfracDiscarded v.
  Proof.
    eapply cmra_update_updateP, cmra_updateP_weaken.
    1: apply gmap_view_plus_frag_dfractional, cmra_update_updateP, dfrac_discard_update.
    by intros ? (?&->&->).
  Qed.

  Lemma gmap_view_plus_frag_get_persistent k dq v :
    gmap_view_plus_frag k dq v ≡ gmap_view_plus_frag k dq v ⋅ gmap_view_plus_pers k (Fpers v).
  Proof.
    rewrite -view_frag_op singleton_op -pair_op agree_idemp op_None_right_id //.
  Qed.

  (** Typeclass instances *)
  Global Instance gmap_view_plus_frag_core_id k dq v : CoreId dq → CoreId (gmap_view_plus_frag k dq v).
  Proof. apply _. Qed.
  Global Instance gmap_view_plus_pers_core_id k vp : CoreId (gmap_view_plus_pers k vp).
  Proof. apply _. Qed.

  Global Instance gmap_view_plus_cmra_discrete : OfeDiscrete V → OfeDiscrete Vpers → CmraDiscrete (gmap_view_plusR K V Vpers Fpers).
  Proof. apply _. Qed.

  Global Instance gmap_view_plus_frag_mut_is_op dq dq1 dq2 k v :
    IsOp dq dq1 dq2 →
    IsOp' (gmap_view_plus_frag k dq v) (gmap_view_plus_frag k dq1 v) (gmap_view_plus_frag k dq2 v).
  Proof. rewrite /IsOp' /IsOp => ->. apply gmap_view_plus_frag_op. Qed.
End lemmas.

(*
(** Functor *)
Program Definition gmap_view_plusURF (K : Type) `{Countable K} `{SI: indexT} (F : oFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := gmap_view_plusUR K (oFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=gmap_view_plus_rel K (oFunctor_car F A1 B1))
              (rel':=gmap_view_plus_rel K (oFunctor_car F A2 B2))
              (gmapO_map (K:=K) (oFunctor_map F fg))
              (gmapO_map (K:=K) (prodO_map cid (agreeO_map (oFunctor_map F fg))))
|}.
Next Obligation.
  intros K ?? ? F A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne, oFunctor_map_ne. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply agreeO_map_ne, oFunctor_map_ne. done.
Qed.
Next Obligation.
  intros K ?? ? F A ? B ? x; simpl in *. rewrite -{2}(view_map_id x).
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k ??.
    apply oFunctor_map_id.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    rewrite -{2}(agree_map_id va).
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_id.
Qed.
Next Obligation.
  intros K ?? ? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -view_map_compose.
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k ??.
    apply oFunctor_map_compose.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    rewrite -agree_map_compose.
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_compose.
Qed.
Next Obligation.
  intros K ?? ? F A1 ? A2 ? B1 ? B2 ? fg; simpl.
  (* [apply] does not work, probably the usual unification probem (Coq #6294) *)
  eapply @view_map_cmra_morphism; [apply _..|]=> n m f.
  intros Hrel k [df va] Hf. move: Hf.
  rewrite !lookup_fmap.
  destruct (f !! k) as [[df' va']|] eqn:Hfk; rewrite Hfk; last done.
  simpl=>[= <- <-].
  specialize (Hrel _ _ Hfk). simpl in Hrel. destruct Hrel as (v & Hagree & Hdval & Hm).
  exists (oFunctor_map F fg v).
  rewrite Hm. split; last by auto.
  rewrite Hagree. rewrite agree_map_to_agree. done.
Qed.

Global Instance gmap_view_plusURF_contractive (K : Type) `{Countable K} `{SI: indexT} F :
  oFunctorContractive F → urFunctorContractive (gmap_view_plusURF K F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne. apply oFunctor_map_contractive. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply agreeO_map_ne, oFunctor_map_contractive. done.
Qed.

Program Definition gmap_view_plusRF (K : Type) `{Countable K} `{SI: indexT} (F : oFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := gmap_view_plusR K (oFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=gmap_view_plus_rel K (oFunctor_car F A1 B1))
              (rel':=gmap_view_plus_rel K (oFunctor_car F A2 B2))
              (gmapO_map (K:=K) (oFunctor_map F fg))
              (gmapO_map (K:=K) (prodO_map cid (agreeO_map (oFunctor_map F fg))))
|}.
Solve Obligations with apply gmap_view_plusURF.

Global Instance gmap_view_plusRF_contractive (K : Type) `{Countable K} `{SI: indexT} F :
  oFunctorContractive F → rFunctorContractive (gmap_view_plusRF K F).
Proof. apply gmap_view_plusURF_contractive. Qed.
*)

#[global]
Typeclasses Opaque gmap_view_plus_auth gmap_view_plus_frag.
