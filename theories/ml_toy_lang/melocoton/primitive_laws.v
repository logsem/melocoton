(** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)

From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import mono_nat.
From iris.base_logic.lib Require Export gen_heap gen_inv_heap.
From melocoton.language Require Export weakestpre lifting.
From melocoton.ml_toy_lang Require Export melocoton.class_instances.
From melocoton.ml_toy_lang Require Import melocoton.tactics notation.
From iris.prelude Require Import options.
From melocoton Require Import monotone.
Search "view" "GS".

Class heapGS_ML Σ := HeapGS_ML {
  heapGS_gen_heapGS :> gen_heapGS loc (option (list val)) Σ;
  heapGS_inv_heapGS :> inv_heapGS loc (option (list val)) Σ;
  heapGS_step_name : gname;
  heapGS_step_cnt : mono_natG Σ;
  heapGS_store_domain : inG Σ (viewUR (@auth_view_rel (@monotoneUR (leibnizO (gset loc)) subseteq)));
  heapGS_store_domain_name : gname
}.
Local Existing Instance heapGS_step_cnt.

Local Notation state := (gmap loc (option (list val))).

Section steps.
  Context `{!heapGS_ML Σ}.

  Local Definition steps_auth (n : nat) : iProp Σ :=
    mono_nat_auth_own heapGS_step_name 1 n.

  Definition steps_lb (n : nat) : iProp Σ :=
    mono_nat_lb_own heapGS_step_name n.

  Local Lemma steps_lb_valid n m :
    steps_auth n -∗ steps_lb m -∗ ⌜m ≤ n⌝.
  Proof.
    iIntros "Hauth Hlb".
    by iDestruct (mono_nat_lb_own_valid with "Hauth Hlb") as %[_ Hle].
  Qed.

  Local Lemma steps_lb_get n :
    steps_auth n -∗ steps_lb n.
  Proof. apply mono_nat_lb_own_get. Qed.

  Local Lemma steps_auth_update n n' :
    n ≤ n' → steps_auth n ==∗ steps_auth n' ∗ steps_lb n'.
  Proof. intros Hle. by apply mono_nat_own_update. Qed.

  Local Lemma steps_auth_update_S n :
    steps_auth n ==∗ steps_auth (S n).
  Proof.
    iIntros "Hauth".
    iMod (mono_nat_own_update with "Hauth") as "[$ _]"; [lia|done].
  Qed.

  Lemma steps_lb_le n n' :
    n' ≤ n → steps_lb n -∗ steps_lb n'.
  Proof. intros Hle. by apply mono_nat_lb_own_le. Qed.

End steps.

Section DomAuth.
  Context `{!heapGS_ML Σ}.

  Definition dom_auth (σ : state) : iProp Σ :=
    (@own _ _ heapGS_store_domain heapGS_store_domain_name (@auth_auth (@monotoneUR (leibnizO (gset loc)) subseteq) (DfracOwn (pos_to_Qp 1)) (principal subseteq (dom σ))))%I.

  Definition dom_part (σ : gset loc) : iProp Σ := 
    (@own _ _ heapGS_store_domain heapGS_store_domain_name (@auth_frag (@monotoneUR (leibnizO (gset loc)) subseteq) (principal subseteq (σ))))%I.

  Global Instance subseteq_preorder : PreOrder (subseteq : gset loc -> gset loc -> Prop).
  Proof. repeat split; eauto. intros a b c; set_solver. Qed.

  Global Instance dom_part_timeless σ : Timeless (dom_part σ).
  Proof. apply own_timeless. apply _. Qed.

  Lemma dom_auth_dom σ1 σ2 : dom σ1 = dom σ2 -> dom_auth σ1 -∗ dom_auth σ2.
  Proof. iIntros (Hdom) "H1". unfold dom_auth; rewrite Hdom; done. Qed.

  Lemma dom_auth_part_valid σ σsub : dom_auth σ -∗ dom_part σsub -∗ ⌜σsub ⊆ dom σ⌝.
  Proof.
    iIntros "H1 H2".
    iPoseProof (own_valid_2 with "H1 H2") as "%Hvalid".
    iPureIntro.
    apply auth_both_valid in Hvalid.
    destruct Hvalid as (Hv1 & _).
    specialize (Hv1 0). cbn in Hv1.
    by eapply (@principal_includedN (leibnizO (gset loc)) _ subseteq_preorder).
  Qed.

  Lemma dom_auth_extend σ σnew : dom_auth σ -∗ ⌜dom σ ⊆ dom σnew⌝ ==∗ dom_auth σnew.
  Proof.
    iIntros "H1 %H2".
    iMod (own_update with "H1") as "$"; last done. 
    eapply auth_update_auth.
    eapply monotone_local_update_grow. done.
  Qed.

  Lemma dom_auth_get σ σfrag : dom_auth σ -∗ ⌜σfrag ⊆ dom σ⌝ ==∗ dom_auth σ ∗ dom_part σfrag.
  Proof.
    iIntros "H1 %H2". 
    iMod (own_update with "H1") as "(H1 & H2)".
    1: eapply monotone_update; [done | apply H2].
    iModIntro. iFrame.
  Qed.

End DomAuth.

Section SafeValues.
  Context `{!heapGS_ML Σ}.

  Fixpoint val_safe_on_heap (σ : gmap loc (option (list val))) (v:val) : Prop := match v with
      LitV (LitInt _) => True
    | LitV (LitBool _) => True
    | LitV (LitUnit) => True
    | LitV (LitPoison) => False
    | LitV (LitLoc l) => l ∈ dom σ
    | PairV v1 v2 => val_safe_on_heap σ v1 ∧ val_safe_on_heap σ v2
    | InjLV vl => val_safe_on_heap σ vl
    | InjRV vr => val_safe_on_heap σ vr
    | RecV f x e => True end.

  Fixpoint val_safe (v : val) : iProp Σ := match v with
      LitV (LitInt _) => True
    | LitV (LitBool _) => True
    | LitV (LitUnit) => True
    | LitV (LitPoison) => False
    | LitV (LitLoc l) => dom_part {[ l ]}
    | PairV v1 v2 => val_safe v1 ∗ val_safe v2
    | InjLV vl => val_safe vl
    | InjRV vr => val_safe vr
    | RecV f x e => True end.

  Global Instance safe_persistent v : Persistent (val_safe v).
  Proof.
   induction v as [[z|b| | |l]|v1 IH1 v2|vl IH|vr IH|]; apply _.
  Qed.

  Global Instance safe_timeless v : Timeless (val_safe v).
  Proof.
   induction v as [[z|b| | |l]|v1 IH1 v2|vl IH|vr IH|]; apply _.
  Qed.


  Lemma val_safe_to_ghost_state σ v:
     ⌜val_safe_on_heap σ v⌝
   -∗ dom_auth σ
  ==∗ dom_auth σ ∗ val_safe v.
  Proof.
    iIntros "%Hd Hσ"; iInduction (v) as [[z|b| | |l]|v1 v2|vl|vr|] "IH"; cbn in Hd; cbn; try (iModIntro; iFrame; done).
    + apply singleton_subseteq_l in Hd. iApply (dom_auth_get with "Hσ []"). done.
    + destruct Hd. iMod ("IH" with "[] Hσ") as "(Hσ & H1)"; first done.
      iMod ("IH1" with "[] Hσ") as "(Hσ & H2)"; first done. iModIntro; iFrame.
    + iMod ("IH" with "[] Hσ") as "(Hσ & H1)"; first done. iModIntro; iFrame.
    + iMod ("IH" with "[] Hσ") as "(Hσ & H1)"; first done. iModIntro; iFrame.
  Qed.

  Lemma val_safe_of_ghost_state σ v:
      dom_auth σ
   -∗ val_safe v
   -∗⌜val_safe_on_heap σ v⌝.
  Proof.
    iIntros "Hσ #Hs"; iInduction (v) as [[z|b| | |l]|? ?|vl|vr|] "IH"; cbn; try done.
    + iPoseProof (dom_auth_part_valid with "Hσ Hs") as "%HH". iPureIntro. set_solver.
    + iDestruct "Hs" as "(Hs1 & Hs2)".
      iPoseProof ("IH" with "Hs1 Hσ") as "%H1".
      iPoseProof ("IH1" with "Hs2 Hσ") as "%H2". iPureIntro; done.
    + iPoseProof ("IH" with "Hs Hσ") as "%H1"; done.
    + iPoseProof ("IH" with "Hs Hσ") as "%H1"; done.
  Qed.

  Definition val_arr_safe_on_heap (σ : state) (vs:list val) : Prop := Forall (val_safe_on_heap σ) vs.
  Definition val_arr_safe (vs:list val) : iProp Σ := [∗ list] v ∈ vs, val_safe v.


  Global Instance arr_safe_timeless v : Timeless (val_arr_safe v).
  Proof.
    apply _.
  Qed.

  Lemma val_arr_safe_to_ghost_state σ vs:
     ⌜val_arr_safe_on_heap σ vs⌝
   -∗ dom_auth σ
  ==∗ dom_auth σ ∗ val_arr_safe vs.
  Proof.
    iInduction vs as [|v vs] "IH"; iIntros "%Hv Hσ".
    + iModIntro. cbn. iPoseProof (bi.emp_sep_1 with "Hσ") as "($&$)".
    + apply Forall_cons_1 in Hv. destruct Hv as (Hv & Hvs). 
      iMod ("IH" with "[] Hσ") as "(Hσ & Hvs)"; first done. 
      iMod (val_safe_to_ghost_state with "[] Hσ") as "(Hσ & Hv)"; first done.
      iModIntro; iFrame.
  Qed.

  Lemma val_arr_safe_of_ghost_state σ vs:
      dom_auth σ
   -∗ val_arr_safe vs
   -∗⌜val_arr_safe_on_heap σ vs⌝.
  Proof.
    iInduction vs as [|v vs] "IH"; iIntros "Hσ Hv".
    + iPureIntro; cbn. econstructor.
    + iDestruct "Hv" as "(Hv & Hvs)".
      iPoseProof ("IH" with "Hσ Hvs") as "%Hvs".
      iPoseProof (val_safe_of_ghost_state with "Hσ Hv") as "%Hv".
      iPureIntro; by econstructor.
  Qed.

  Definition heap_part_safe_on_heap (σ : state) (σpart : gmap loc (option (list val))) : Prop := 
   map_Forall (fun x y => match y with Some vs => val_arr_safe_on_heap σ vs | _ => True end) σpart.
  Definition heap_safe (σ : gmap loc (option (list val))) : iProp Σ := 
    [∗ map] k↦v ∈ σ, match v with Some vs => val_arr_safe vs | _ => True end.


  Global Instance heap_safe_timeless v : Timeless (val_arr_safe v).
  Proof.
    apply _.
  Qed.

  Lemma heap_safe_to_ghost_state σ σ1:
     ⌜heap_part_safe_on_heap σ σ1⌝
   -∗ dom_auth σ
  ==∗ dom_auth σ ∗ heap_safe σ1.
  Proof.
    induction σ1 using map_ind; iIntros "%Hsafe Hσ".
    + iModIntro. cbn. iPoseProof (bi.emp_sep_1 with "Hσ") as "(Hemp&$)".
      by iApply big_sepM_empty.
    + iMod (IHσ1 with "[] Hσ") as "(Hσ & Hvs)". 1: iPureIntro; eapply map_Forall_insert_1_2; done.
      destruct x as [vs|].
      * iMod (val_arr_safe_to_ghost_state with "[] Hσ") as "(Hσ & Hv)". 1: eapply map_Forall_insert_1_1 in Hsafe; done. 
        iModIntro. iFrame. unfold heap_safe. iApply big_sepM_insert; first done. iFrame.
      * iModIntro. iFrame. unfold heap_safe. iApply big_sepM_insert; first done. iFrame.
  Qed.

  Lemma heap_safe_of_ghost_state σ σ1:
      dom_auth σ
   -∗ heap_safe σ1
   -∗⌜heap_part_safe_on_heap σ σ1⌝.
  Proof.
    induction σ1 using map_ind; iIntros "Hσ Hv".
    + iPureIntro; cbn. eapply map_Forall_empty.
    + iPoseProof (big_sepM_insert) as "(Ha & _)"; first done.
      iPoseProof ("Ha" with "Hv") as "(Hvs & Hh)"; iClear "Ha".
      iPoseProof (IHσ1 with "Hσ Hh") as "%Hh".
      destruct x as [vs|].
      * iPoseProof (val_arr_safe_of_ghost_state with "Hσ Hvs") as "%Hvs".
        iPureIntro. apply map_Forall_insert; done.
      * iPureIntro. apply map_Forall_insert; done.
  Qed.

End SafeValues.



Global Program Instance heapGS_langGS_ML `{heapGS_ML Σ}
      : langGS val ML_lang Σ := {
  state_interp σ step_cnt :=
    ( gen_heap_interp σ
    ∗ steps_auth step_cnt
    ∗ dom_auth σ
    ∗ heap_safe σ)%I
}.
Next Obligation.
  iIntros (???? σ ns E)  "/= ($ & H & $)".
  by iMod (steps_auth_update_S with "H") as "$".
Qed.

Notation "l ↦M{ dq } v" := (mapsto (L:=loc) (V:=option (list val)) l dq (Some [v%V]))
  (at level 20, format "l  ↦M{ dq }  v") : bi_scope.
Notation "l ↦M□ v" := (mapsto (L:=loc) (V:=option (list val)) l DfracDiscarded (Some [v%V]))
  (at level 20, format "l  ↦M□  v") : bi_scope.
Notation "l ↦M{# q } v" := (mapsto (L:=loc) (V:=option (list val)) l (DfracOwn q) (Some [v%V]))
  (at level 20, format "l  ↦M{# q }  v") : bi_scope.
Notation "l ↦M v" := (mapsto (L:=loc) (V:=option (list val)) l (DfracOwn 1) (Some [v%V]))
  (at level 20, format "l  ↦M  v") : bi_scope.



Notation "l ↦M/{ dq }" := (mapsto (L:=loc) (V:=option (list val)) l dq None)
  (at level 20, format "l  ↦M/{ dq } ") : bi_scope.
Notation "l ↦M/□" := (mapsto (L:=loc) (V:=option (list val)) l DfracDiscarded None)
  (at level 20, format "l  ↦M/□") : bi_scope.
Notation "l ↦M/{# q }" := (mapsto (L:=loc) (V:=option (list val)) l (DfracOwn q) None)
  (at level 20, format "l  ↦M/{# q }") : bi_scope.
Notation "l ↦M/" := (mapsto (L:=loc) (V:=option (list val)) l (DfracOwn 1) None)
  (at level 20, format "l  ↦M/") : bi_scope.

Notation "l ↦∗{ dq } vs" := (mapsto (L:=loc) (V:=option (list val)) l dq (Some vs))
  (at level 20, format "l  ↦∗{ dq }  vs") : bi_scope.
Notation "l ↦∗□ vs" := (mapsto (L:=loc) (V:=option (list val)) l DfracDiscarded (Some vs))
  (at level 20, format "l  ↦∗□  vs") : bi_scope.
Notation "l ↦∗{# q } vs" := (mapsto (L:=loc) (V:=option (list val)) l (DfracOwn q) (Some vs))
  (at level 20, format "l  ↦∗{# q }  vs") : bi_scope.
Notation "l ↦∗ vs" := (mapsto (L:=loc) (V:=option (list val)) l (DfracOwn 1) (Some vs))
  (at level 20, format "l  ↦∗  vs") : bi_scope.

(** Same for [gen_inv_heap], except that these are higher-order notations so to
make setoid rewriting in the predicate [I] work we need actual definitions
here. *)
Section definitions.
  Context `{!heapGS_ML Σ}.
  Definition inv_mapsto_own (l : loc) (vs : option (list val)) (I : option (list val) → Prop) : iProp Σ :=
    inv_mapsto_own l vs I.
  Definition inv_mapsto (l : loc) (I : option (list val) → Prop) : iProp Σ :=
    inv_mapsto l I.
  (* TODO: single value version of those *)
End definitions.

Global Instance: Params (@inv_mapsto_own) 4 := {}.
Global Instance: Params (@inv_mapsto) 3 := {}.

Notation inv_heap_inv := (inv_heap_inv loc (option (list val))).
Notation "l '↦∗_' I □" := (inv_mapsto l I%stdpp%type)
  (at level 20, I at level 9, format "l  '↦∗_' I  '□'") : bi_scope.
Notation "l ↦∗_ I vs" := (inv_mapsto_own l vs I%stdpp%type)
  (at level 20, I at level 9, format "l  ↦∗_ I  vs") : bi_scope.

Section lifting.
Context `{!heapGS_ML Σ, !invGS_gen hlc Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types l : loc.
Implicit Types pe : prog_environ ML_lang Σ.

Lemma wp_lb_init pe E e Φ :
  TCEq (to_val e) None →
  (steps_lb 0 -∗ WP e @ pe; E {{ v, Φ v }}) -∗
  WP e @ pe; E {{ Φ }}.
Proof.
  (** TODO: We should try to use a generic lifting lemma (and avoid [wp_unfold])
  here, since this breaks the WP abstraction. *)
  rewrite !wp_unfold /wp_pre /=. iIntros (Heq) "Hwp".
  iIntros (σ1 ns) "(Hσ & Hsteps & Hdom)".
  iDestruct (steps_lb_get with "Hsteps") as "#Hlb".
  iDestruct (steps_lb_le _ 0 with "Hlb") as "Hlb0"; [lia|].
  iSpecialize ("Hwp" with "Hlb0"). iApply ("Hwp" $! σ1 ns). iFrame.
Qed.

Lemma wp_lb_update pe n E e Φ :
  TCEq (to_val e) None →
  steps_lb n -∗
  WP e @ pe; E {{ v, steps_lb n -∗ Φ v }} -∗
  WP e @ pe; E {{ Φ }}.
Proof.
  (** TODO: We should try to use a generic lifting lemma (and avoid [wp_unfold])
  here, since this breaks the WP abstraction. *)
  rewrite !wp_unfold /wp_pre /=. iIntros (Heq) "Hlb Hwp".
  iIntros (σ1 ns) "(Hσ & Hsteps & Hdom & Hsafe)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %?.
  iMod ("Hwp" $! σ1 ns with "[$Hσ $Hsteps $Hdom $Hsafe]") 
      as "[(%v & -> & Hσ & Hv)|[(%s0 & %vv & %K & -> & Hprog & Hwp)|(%Hred & Hwp)]]".
  - cbn in Heq. apply TCEq_eq in Heq. congruence.
  - iModIntro. iRight. iLeft. iExists s0, vv, K. iFrame. iSplitR; first done.
    iMod "Hwp" as "(%Ξ & (Hσ & Hsteps & Hdom) & HΞ & Hwp)". iModIntro. 
    iDestruct (steps_lb_get with "Hsteps") as "#HlbS".
    iExists Ξ. iFrame. iNext.
    iIntros (r) "Hr". iSpecialize ("Hwp" $! r with "Hr").
    iApply (wp_wand with "Hwp"). iIntros (v) "Hv". by iApply "Hv".
  - iModIntro. iRight. iRight. iSplitR; first done.
    iIntros (e2 σ2 Hstep). iMod ("Hwp" with "[//]") as "Hwp".
    iIntros "!> !>". iMod "Hwp" as "((Hσ & Hsteps & Hdom & Hsafe) & Hwp)". iIntros "!>".
    iDestruct (steps_lb_get with "Hsteps") as "#HlbS".
    iDestruct (steps_lb_le _ (S n) with "HlbS") as "#HlbS'"; [lia|].
    iFrame.
    iApply (wp_wand with "Hwp"). iIntros (v) "HΦ". by iApply "HΦ".
Qed.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb
induction directly, but this demonstrates that we can state the expected
reasoning principle for recursive functions, without any visible ▷. *)
Lemma wp_rec_löb pe E f x e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ pe; E {{ Φ }}) -∗
     ∀ v, Ψ v -∗ WP (subst' x v (subst' f (rec: f x := e) e)) @ pe; E {{ Φ }}) -∗
  ∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ pe; E {{ Φ }}.
Proof.
  iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ".
  iApply lifting.wp_pure_step_later; first eauto.
  iIntros "!>". iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ".
  iApply ("IH" with "HΨ").
Qed.

(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [val]. *)

Lemma mapsto_valid l dq v : l ↦M{dq} v -∗ ⌜✓ dq⌝.
Proof. apply mapsto_valid. Qed.
Lemma mapsto_valid_2 l dq1 dq2 v1 v2 :
  l ↦M{dq1} v1 -∗ l ↦M{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  iIntros "H1 H2". iDestruct (mapsto_valid_2 with "H1 H2") as %[? [=?]]. done.
Qed.
Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦M{dq1} v1 -∗ l ↦M{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %[=?]. done. Qed.

Lemma mapsto_combine l dq1 dq2 v1 v2 :
  l ↦M{dq1} v1 -∗ l ↦M{dq2} v2 -∗ l ↦M{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  iIntros "Hl1 Hl2". iDestruct (mapsto_combine with "Hl1 Hl2") as "[$ Heq]".
  by iDestruct "Heq" as %[= ->].
Qed. 

Lemma mapsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦M{dq1} v1 -∗ l2 ↦M{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_frac_ne. Qed.
Lemma mapsto_ne l1 l2 dq2 v1 v2 : l1 ↦M v1 -∗ l2 ↦M{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_ne. Qed.

Lemma mapsto_persist l dq v : l ↦M{dq} v ==∗ l ↦M□ v.
Proof. apply mapsto_persist. Qed.

Global Instance inv_mapsto_own_proper l (vs : option _) :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_mapsto_own l vs).
Proof.
  intros I1 I2 HI. rewrite /inv_mapsto_own. f_equiv; done.
Qed.
Global Instance inv_mapsto_proper l :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_mapsto l).
Proof.
  intros I1 I2 HI. rewrite /inv_mapsto. f_equiv; done.
Qed.

Lemma make_inv_mapsto l vs (I : option (list val) → Prop) E :
  ↑inv_heapN ⊆ E →
  I (Some vs) →
  inv_heap_inv -∗ l ↦∗ vs ={E}=∗ l ↦∗_I (Some vs).
Proof. iIntros (??) "#HI Hl". iApply make_inv_mapsto; done. Qed.
Lemma inv_mapsto_own_inv l vs I : l ↦∗_I (Some vs) -∗ l ↦∗_I □.
Proof. apply inv_mapsto_own_inv. Qed.

Lemma inv_mapsto_own_acc_strong E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv ={E, E ∖ ↑inv_heapN}=∗ ∀ l vs I, l ↦∗_I (Some vs) -∗
    (⌜I (Some vs)⌝ ∗ l ↦∗ vs ∗ (∀ ws : (list val), ⌜I (Some ws)⌝ -∗ l ↦∗ ws ==∗
      inv_mapsto_own l (Some ws) I ∗ |={E ∖ ↑inv_heapN, E}=> True)).
Proof.
  iIntros (?) "#Hinv".
  iMod (inv_mapsto_own_acc_strong with "Hinv") as "Hacc"; first done.
  iIntros "!>" (l v I) "Hl". iDestruct ("Hacc" with "Hl") as "(% & Hl & Hclose)".
  iFrame "Hl". iFrame (H0). iIntros "%ws %H2 HH". iApply ("Hclose" $! (Some ws) H2 with "HH").
Qed.

Lemma inv_mapsto_own_acc E l vs I:
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦∗_I (Some vs) ={E, E ∖ ↑inv_heapN}=∗
    (⌜I (Some vs)⌝ ∗ l ↦∗ vs ∗ (∀ ws, ⌜I (Some ws) ⌝ -∗ l ↦∗ ws ={E ∖ ↑inv_heapN, E}=∗ l ↦∗_I (Some ws))).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_mapsto_own_acc with "Hinv Hl") as "(% & Hl & Hclose)"; first done.
  iFrame "Hl". iFrame (H0). iIntros "!> %ws %H2 HH". iApply ("Hclose" $! (Some ws) H2 with "HH").
Qed.

Lemma inv_mapsto_acc l I E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦∗_I □ ={E, E ∖ ↑inv_heapN}=∗
    ∃ (vs:option _), ⌜I vs⌝ ∗ mapsto l (DfracOwn 1) vs ∗ (mapsto l (DfracOwn 1) vs ={E ∖ ↑inv_heapN, E}=∗ ⌜True⌝).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_mapsto_acc with "Hinv Hl") as (v) "(% & Hl & Hclose)"; [done|].
  iIntros "!>". iExists (v). iFrame "%∗".
Qed.

Lemma wp_allocN pe E v n :
  (0 ≤ n)%Z →
  {{{ ▷ val_safe v }}} AllocN (Val $ LitV $ LitInt n) (Val v) @ pe; E
  {{{ l, RET LitV (LitLoc l); l ↦∗ (replicate (Z.to_nat n) v) ∗ meta_token l ⊤ ∗ val_safe (#l) }}}.
Proof.
  iIntros (Hn Φ) ">#Hsafe HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1 ns) "(Hσ & Hsteps & Hdom & Hheap)". iModIntro. iSplit; first (destruct n; eauto with lia head_step).
  iIntros (v2 σ2 Hstep). inv_head_step. iModIntro.
  iMod (gen_heap_alloc _ l (Some (replicate (Z.to_nat n) v)) with "Hσ") as "(Hσ & Hl & Hm)".
  { by apply not_elem_of_dom. }
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (dom_auth_extend with "Hdom []") as "Hdom"; last first.
  1: iMod (dom_auth_get _ {[l]} with "Hdom []") as "(Hdom & #Hpart)"; first last.
  1: iFrame "Hdom".
  3: iPureIntro; rewrite dom_insert_L; set_solver.
  2: iPureIntro; rewrite dom_insert_L; set_solver.
  iModIntro. iFrame. iSplitL "Hsafe Hheap"; last iApply "HΦ"; iFrame; last done.
  iApply big_sepM_insert. 1: by eapply not_elem_of_dom. iFrame.
  iApply big_sepL_forall. iIntros (k x Hkx). apply lookup_replicate in Hkx. destruct Hkx; subst; done.
Qed.

Lemma wp_alloc pe E v :
  {{{ ▷ val_safe v }}} Alloc (Val v) @ pe; E
  {{{ l, RET LitV (LitLoc l); l ↦M v ∗ meta_token l ⊤ ∗ val_safe (#l) }}}.
Proof.
  iIntros (HΦ) ">#Hsafe HΦ". by iApply wp_allocN.
Qed.

Lemma wp_loadN pe E l i dq vs v :
  (0 ≤ i)%Z →
  vs !! Z.to_nat i = Some v →
  {{{ ▷ l ↦∗{dq} vs }}} LoadN (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i) @ pe; E
  {{{ RET v; l ↦∗{dq} vs ∗ val_arr_safe vs }}}.
Proof.
  iIntros (Hi Hv Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1 ns) "(Hσ & Hsteps & Hdom & #Hsafe) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  assert (σ1 !! l.[i] = Some v).
  { rewrite store_lookup_eq. case_bool_decide; [|done]. by simplify_map_eq/=. }
  iSplit; first by eauto with head_step.
  iIntros (v2 σ2 Hstep); inv_head_step. iModIntro.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps". iModIntro. iFrame. iFrame "Hsafe".
  iApply "HΦ". iFrame.
  iPoseProof (big_sepM_lookup with "Hsafe") as "HH"; first done. iApply "HH".
Qed.

Lemma wp_load pe E l dq v :
  {{{ ▷ l ↦M{dq} v }}} Load (Val $ LitV $ LitLoc l) @ pe; E
  {{{ RET v; l ↦M{dq} v ∗ val_safe v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply (wp_loadN with "Hl"); try done.
  iIntros "!> (H1 & #H2)". iApply "HΦ"; iFrame.
  iPoseProof big_sepL_singleton as "[HL HR]".  unfold val_arr_safe. iPoseProof ("HL" with "H2") as "$".
Qed.

Lemma wp_storeN pe E l i vs w :
  (0 ≤ i < length vs)%Z →
  {{{ ▷ l ↦∗ vs ∗ ▷ val_safe w}}} StoreN (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i) (Val w) @ pe; E
  {{{ RET LitV LitUnit; l ↦∗ <[ Z.to_nat i := w ]> vs }}}.
Proof.
  iIntros (Hi Φ) "(>Hl & >#Hsafe) HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1 ns) "(Hσ & Hsteps & Hdom & #Hheap) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  assert (is_Some (σ1 !! l.[i])) as [? ?].
  { rewrite store_lookup_eq. case_bool_decide; [|lia]. simplify_map_eq.
    apply lookup_lt_is_Some. lia. }
  iSplit; first by eauto with head_step.
  iIntros (v2 σ2 Hstep); inv_head_step. iModIntro.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (gen_heap_update with "Hσ Hl") as "[Hσ Hl]".
  rewrite (store_insert_offset _ _ _ vs); auto; [].
  iModIntro. iFrame "Hσ Hsteps". iSplitL "Hdom"; last by iApply "HΦ".
  iSplitL.
  + iApply dom_auth_dom; last done. rewrite dom_insert_L. eapply elem_of_dom_2 in H; set_solver.
  + iApply big_sepM_insert_override_2; try done. iIntros "#Hvs".
    iPoseProof (big_sepL_insert_acc with "Hvs") as "(_ & Hvs2)"; last by iApply "Hvs2".
    rewrite store_lookup_eq in H0. rewrite bool_decide_decide in H0. destruct (decide); try lia.
    rewrite H in H0. cbn in H0. done.
Qed.

Lemma wp_store pe E l v w :
  {{{ ▷ l ↦M v  ∗ ▷ val_safe w}}} Store (Val $ LitV $ LitLoc l) (Val w) @ pe; E
  {{{ RET LitV LitUnit; l ↦M w }}}.
Proof.
  iIntros (Φ) "Hl HΦ". by iApply (wp_storeN with "Hl").
Qed.

Lemma wp_length pe E l dq vs :
  {{{ ▷ l ↦∗{dq} vs }}} Length (Val $ LitV $ LitLoc l) @ pe; E
  {{{ RET LitV $ LitInt (length vs); l ↦∗{dq} vs }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1 ns) "(Hσ & Hsteps & Hrem) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (v2 σ2 Hstep); inv_head_step. iModIntro.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iFrame. by iApply "HΦ".
Qed.

(* TODO: rules to allow splitting the ownership of an array, and having the
   knowledge of the length of an array be persistent, following what is done in
   Cosmo. *)

End lifting.
