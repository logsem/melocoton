(** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)

From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From transfinite.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From melocoton.language Require Export weakestpre lifting.
From melocoton.c_interface Require Export resources.
From melocoton.c_lang Require Export class_instances.
From melocoton.c_lang Require Import tactics notation.
From iris.prelude Require Import options.

Global Program Instance heapG_langG_C {SI:indexT} `{heapG_C Σ}
      : langG val C_lang Σ := {
  state_interp σ := public_state_interp σ
}.

Section lifting.
Context {SI:indexT}.
Context `{!heapG_C Σ, !invG Σ}.
Context {p:prog_environ C_lang Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : outcome val → iProp Σ.
Implicit Types Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : gmap loc heap_cell.
Implicit Types v : val.
Implicit Types l : loc.

(*
#[global] Instance wp'': Wp (iProp Σ) expr val stuckness := (@wp' (C_lang p) Σ _).
#[global] Instance twp'': Twp (iProp Σ) expr val stuckness := (@twp' (C_lang p) Σ _).
*)

(** Recursive functions: we do not use this lemmas as it is easier to use Löb
induction directly, but this demonstrates that we can state the expected
reasoning principle for recursive functions, without any visible ▷. *)
(* Lemma wp_rec_löb s E f e args Φ (Ψ : list val → iProp Σ) : *)
(*    ⌜penv_prog s !! f = Some (Fun args e)⌝ -∗ *)
(*   □ ( □ (∀ vs res, Ψ vs -∗ ⌜zip_args args vs = Some res⌝ -∗ WP (FunCall ((&f)%V) (map Val vs)) @ s; E {{ Φ }}) -∗ *)
(*      ∀ vs res, Ψ vs -∗ ⌜zip_args args vs = Some res⌝ -∗ WP (subst_all res e) @ s; E {{ Φ }}) -∗ *)
(*   ∀ vs res , Ψ vs -∗ ⌜zip_args args vs = Some res⌝ -∗ WP (FunCall ((&f)%V) (map Val vs)) @ s; E {{ Φ }}. *)
(* Proof. *)
(*   iIntros "%Hp #Hrec". iLöb as "IH". iIntros (v res) "HΨ %Hres". *)
(*   iApply lifting.wp_pure_step_later. 1: eauto. *)
(*   iIntros "!>". iApply ("Hrec" with "[] HΨ"). 2:done. iIntros "!>" (w res') "HΨ %Hres'". *)
(*   iApply ("IH" with "HΨ"). iPureIntro. apply Hres'. *)
(* Qed. *)

Lemma wp_lift_atomic_head_step {s E Φ} e1 :
  to_outcome e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible (penv_prog s) e1 σ1⌝ ∗
    ▷ ∀ e2 σ2, ⌜head_step (penv_prog s) e1 σ1 e2 σ2⌝ ={E}=∗
      state_interp σ2 ∗
      from_option Φ False (to_outcome e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E _ e1)=>//; iIntros (σ1) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[%HH H]". iModIntro. iSplitR; first (iPureIntro; by eapply head_prim_reducible).
  iIntros (e' σ' Hstep%head_reducible_prim_step). 2: {  destruct HH as (?&?&HH). do 2 eexists. done. }
  do 2 iModIntro.
  iMod ("H" $! e' σ' Hstep) as "[H1 H2]". iModIntro.
  iFrame.
  destruct (to_outcome e') eqn:?; last by iExFalso.
  iApply wp_outcome; first done. iApply "H2".
Qed.

Lemma wp_Malloc_seq E n :
  (0 < n)%Z →
  {{{ True }}} Malloc (Val $ LitV $ LitInt $ n) @ p; E
  {{{ l, RET OVal (LitV (LitLoc l)); [∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦C ? }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1) "Hσ". iModIntro. iSplit; first (destruct n; eauto with lia head_step).
  iIntros (e2 σ2 Hstep). inv_head_step. iModIntro.
  iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) Uninitialized)) with "Hσ")
    as "(Hσ & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite replicate_length Z2Nat.id; auto with lia. }
  iModIntro. iFrame. iApply "HΦ".
  by iApply heap_array_to_seq_mapsto.
Qed.

Lemma wp_free s E l (v:option val) :
  {{{ ▷ l O↦C (Some v) }}} Free (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt 1) @ s; E
  {{{ RET OVal (LitV LitUnit); True }}}.
Proof.
  iIntros (Φ) "> Hl HΦ". iApply (wp_step with "HΦ"). iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1) "Hσ". iDestruct (gen_heap_valid with "Hσ Hl") as "%HH". iModIntro.
  iSplitR; first ( iPureIntro ).
  1: { do 2 eexists. econstructor.
       intros i H1 H2. exists v. rewrite <- HH. f_equal.
       destruct l; cbn. unfold loc_add. f_equal. cbn. lia. }
  iIntros (e2 σ2 Hstep); inv_head_step. iModIntro.
  rewrite state_init_heap_singleton.
  iMod (gen_heap_update (σ1) l (Some v) Deallocated with "Hσ Hl") as "[$ Hl]".
  iModIntro. iFrame. iIntros "HΦ". iModIntro. by iApply "HΦ".
Qed.

Lemma wp_load s E l dq v :
  {{{ ▷ l ↦C{dq} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET OVal v; l ↦C{dq} v }}}.
Proof.
  iIntros (Φ) "> Hl HΦ". iApply (wp_step with "HΦ"). iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1) "Hσ". iDestruct (gen_heap_valid with "Hσ Hl") as "%HH". iModIntro.
  iSplitR; first ( iPureIntro; eauto with head_step).
  iIntros (e2 σ2 Hstep); inv_head_step. iModIntro.
  iModIntro. iFrame. iIntros "HΦ". iModIntro.
  by iApply "HΦ".
Qed.

Lemma wp_store s E l (v':option val) v :
  {{{ ▷ l O↦C Some v' }}} Store (Val $ LitV $ LitLoc l) (Val v) @ s; E
  {{{ RET OVal (LitV LitUnit); l ↦C v }}}.
Proof.
  iIntros (Φ) "> Hl HΦ". iApply (wp_step with "HΦ"). iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1) "Hσ !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (e2 σ2 Hstep); inv_head_step. iModIntro.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iFrame. iIntros "HΦ". iModIntro. by iApply "HΦ".
Qed.

Lemma wp_call' (s:prog_environ C_lang Σ) n args body body' vv E Φ :
     ⌜(penv_prog s) !! n = Some (Fun args body)⌝
  -∗ ⌜apply_function (Fun args body) vv = Some body'⌝
  -∗ (|={E}=> ▷ |={E}=> WP body' @ s ; E {{v, Φ v}})
  -∗ WP (FunCall ((&n)) (map Val vv)) @ s ; E {{v, Φ v}}.
Proof.
  iIntros (Hlookup Happly) "Hcont". iApply wp_lift_step_fupd; first done.
  iIntros (σ1) "Hσ !>".
  iSplit.
  { iPureIntro. eexists _,_. apply head_prim_step. econstructor; done. }
  iIntros (v2 σ2 Hstep).
  apply head_reducible_prim_step in Hstep; last by eauto with head_step.
  inv_head_step. iMod "Hcont". do 2 iModIntro.
  iMod "Hcont".
  do 2 iModIntro. iFrame.
Qed.

Lemma wp_call (s:prog_environ C_lang Σ) n args body body' vv E Φ :
     ⌜penv_prog s !! n = Some (Fun args body)⌝
  -∗ ⌜apply_function (Fun args body) vv = Some body'⌝
  -∗ (WP body' @ s ; E {{v, Φ v}})
  -∗ WP (FunCall ((&n)) (map Val vv)) @ s ; E {{v, Φ v}}.
Proof.
  iIntros (Hlookup Happly) "Hcont".
  iApply wp_call'. 1-2: done. do 3 iModIntro. done.
Qed.

End lifting.
