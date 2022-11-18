From stdpp Require Import gmap coPset.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import mono_nat.
From iris.base_logic.lib Require Export gen_heap.
From iris.algebra.lib Require Import excl_auth gmap_view.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.mlanguage Require Import weakestpre lifting.
From melocoton.minilang Require Import lang.
From melocoton.interop Require Import linking_wp.
From melocoton Require Import commons monotone.
From iris.prelude Require Import options.
Import Mini.

Canonical Structure coPsetO := leibnizO coPset.
Canonical Structure gsetlocO := leibnizO (gset loc).

Notation locs_subset := ((⊆) : relation (leibnizO (gset loc))).

Class minilangGS hlc Σ := HeapGS {
  heapGS_invGS :> invGS_gen hlc Σ;
  heapGS_gen_heapGS :> gen_heapGS loc nat Σ;
  heapGS_acc_name : gname;
  heapGS_accGS :> inG Σ (excl_authR (leibnizO nat));
  heapGS_available_name : gname;
  heapGS_availableGS :> inG Σ (excl_authR (leibnizO coPset));
  heapGS_locsGS :> inG Σ (authUR (monotoneUR locs_subset));
  heapGS_locs_name : gname;
}.

Section ghost_state_defs.
Context `{!minilangGS hlc Σ}.

Definition available_auth (locs : gset loc) : iProp Σ :=
  ∃ (available:coPset),
    own heapGS_available_name (●E available) ∗
    ⌜∀ ℓ, ℓ ∈ locs → (Pos.of_nat ℓ) ∉ available⌝.

Definition locs_auth (s : gset loc) : iProp Σ :=
  own heapGS_locs_name (● (principal locs_subset s)).
Definition locs_atleast (s : gset loc) : iProp Σ :=
  own heapGS_locs_name (◯ (principal locs_subset s)).
Global Instance locs_atleast_persistent s : Persistent (locs_atleast s).
Proof. apply _. Qed.
Lemma locs_atleast_sub s s' :
  locs_auth s -∗ locs_atleast s' -∗ ⌜s' ⊆ s⌝.
Proof.
  rewrite /locs_auth /locs_atleast. iIntros "Ha Hf".
  iDestruct (own_valid_2 with "Ha Hf") as %[Hv _]%auth_both_valid_discrete.
  iPureIntro. by apply (principal_included s' s) in Hv.
Qed.

Definition minilang_pub_interp (st : gmap loc nat * nat) : iProp Σ :=
  let '(σ, n) := st in
  gen_heap_interp σ ∗
  own heapGS_acc_name (●E n) ∗
  available_auth (dom σ) ∗
  locs_auth (dom σ).

Global Program Instance minilangGS_mlangGS : mlangGS hlc unit Σ minilang := {
  state_interp '(σ, acc) :=
    (gen_heap_interp σ ∗
     own heapGS_acc_name (●E acc) ∗
     available_auth (dom σ) ∗
     locs_auth (dom σ))%I;
  at_boundary := True%I;
}.

Global Program Instance minilangGS_linkableGS :
  linkableGS minilang minilang_pub_interp := {
  private_state_interp locs :=
    locs_atleast locs;
}.
Next Obligation.
  simpl. intros [σ acc] pubσ privσ Hsplit.
  iIntros "(Hσ & Hacc & ? & Hlocs)". inversion Hsplit; simplify_eq.
  unfold private_state in privσ.
  iMod (own_update with "Hlocs") as "[Hlocs Hlocsf]".
  { by eapply (monotone_update _ (dom σ) (privσ : leibnizO _)). }
  by iFrame.
Qed.
Next Obligation.
  simpl. intros [σ acc] privσ. iIntros "(? & ? & ? & Hlocs) Hlocsf".
  iDestruct (locs_atleast_sub with "Hlocs Hlocsf") as %?.
  iModIntro. iExists (_, _). iFrame. iPureIntro. by econstructor.
Qed.
Next Obligation.
  intros [σ acc]. simpl.
  iIntros "_ (? & ? & ? & ?)".
  iPureIntro. eexists _, (dom σ). by econstructor.
Qed.

Definition acc_frag (n:nat) : iProp Σ :=
  own heapGS_acc_name (◯E n).
Definition available_frag (avail:coPset) : iProp Σ :=
  own heapGS_available_name (◯E avail).
Definition loc_frag ℓ : iProp Σ :=
  locs_atleast {[ ℓ ]}.

Global Instance loc_frag_persistent ℓ : Persistent (loc_frag ℓ).
Proof. apply _. Qed.

End ghost_state_defs.

Notation "l ↦ v" := (mapsto (L:=loc) (V:=nat) l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.
Notation "'ACC' n" := (acc_frag n)
  (at level 20, format "ACC  n") : bi_scope.
Notation "'AVAILABLE' a" := (available_frag a)
  (at level 20, format "AVAILABLE  a") : bi_scope.
Notation "'REGISTERED' ℓ" := (loc_frag ℓ)
  (at level 20, format "REGISTERED  ℓ") : bi_scope.

Section lifting.
Context `{!minilangGS hlc Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : unit → iProp Σ.
Implicit Types σ : state.
Implicit Types ℓ : loc.

Lemma wp_read p ℓ EE n m :
  {{{ ℓ ↦ n ∗ ACC m }}}
    E [Read ℓ] @ p; EE
  {{{ RET (); ℓ ↦ n ∗ ACC n }}}.
Proof.
  iIntros (Φ) "(Hℓ & Ha) HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros ([σ acc]) "(Hσ & Haa & ? & ?) !>".
  iDestruct (gen_heap_valid with "Hσ Hℓ") as %Hℓ.
  iSplit. { iPureIntro. exists (λ _, True). by econstructor. }
  iIntros "!>" (X Hstep). inversion Hstep; simplify_eq.
  iMod (excl_auth_upd with "Ha Haa") as "[? ?]".
  iModIntro. iExists _, _. iSplitR; first done. iFrame.
  simpl. iApply "HΦ". iFrame.
Qed.

Lemma wp_read_registered p ℓ EE m :
  {{{ REGISTERED ℓ ∗ ACC m }}}
    E [Read ℓ] @ p; EE
  {{{ RET (); ∃ n, ACC n }}}.
Proof.
  iIntros (Φ) "(Hℓ & Ha) HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros ([σ acc]) "(Hσ & Haa & ? & Hlocsa) !>".
  iDestruct (locs_atleast_sub with "Hlocsa Hℓ") as %[? ?]%singleton_subseteq_l%elem_of_dom.
  iSplit. { iPureIntro. exists (λ _, True). by econstructor. }
  iIntros "!>" (X Hstep). inversion Hstep; simplify_eq.
  iMod (excl_auth_upd with "Ha Haa") as "[? ?]".
  iModIntro. iExists _, _. iSplitR; first done. iFrame.
  simpl. iApply "HΦ". iExists _. iFrame.
Qed.

Lemma wp_write p ℓ EE n m :
  {{{ ℓ ↦ n ∗ ACC m }}}
    E [Write ℓ] @ p; EE
  {{{ RET (); ℓ ↦ m ∗ ACC m }}}.
Proof.
  iIntros (Φ) "(Hℓ & Ha) HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros ([? ?]) "(Hσ & Haa & ? & ?) !>".
  iDestruct (gen_heap_valid with "Hσ Hℓ") as %Hℓ.
  iSplit. { iPureIntro. exists (λ _, True). econstructor; eauto.
            by eapply elem_of_dom_2. }
  iIntros "!>" (X Hstep). inversion Hstep; simplify_eq.
  iDestruct (excl_auth_eq with "Ha Haa") as %<-.
  iMod (gen_heap_update with "Hσ Hℓ") as "[Hσ Hℓ]".
  iModIntro. iExists _, _. iSplitR; first done. iFrame.
  rewrite dom_insert_lookup_L //. iFrame.
  simpl. iApply "HΦ". iFrame.
Qed.

Lemma wp_register p ℓ EE av :
  (Pos.of_nat ℓ) ∈ av →
  {{{ AVAILABLE av }}}
    E [Register ℓ] @ p; EE
  {{{ RET (); ℓ ↦ 0 ∗ REGISTERED ℓ ∗ AVAILABLE (av ∖ {[Pos.of_nat ℓ]}) }}}.
Proof.
  iIntros (Hℓ Φ) "Hav HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros ([? ?]) "(Hσ & Haa & Hava & Hlocsa) !>".
  iDestruct "Hava" as (av') "(Hava & %Hav)".
  iDestruct (excl_auth_eq with "Hav Hava") as %<-.
  iSplit. { iPureIntro. exists (λ _, True). econstructor; naive_solver. }
  iIntros "!>" (X Hstep). inversion Hstep; simplify_eq.
  iMod (excl_auth_upd _ _ _ (av ∖ {[Pos.of_nat ℓ]}) with "Hav Hava") as "[Hav Hava]".
  iMod (gen_heap_alloc _ ℓ with "Hσ") as "(Hσ & Hℓ & _)".
  1: by apply not_elem_of_dom_1.
  iMod (own_update with "Hlocsa") as "[Hlocsa Hlocsf]".
  { eapply (monotone_update _ ({[ ℓ ]} ∪ dom g) ({[ ℓ ]} ∪ dom g)); try done.
    apply union_subseteq_r. }
  iMod (own_update with "Hlocsa") as "[Hlocsa Hlocsf1]".
  { eapply (monotone_update _ _ {[ ℓ ]}). 1: reflexivity. set_solver. }
  iModIntro. iExists _, _. iSplitR; first done. iFrame.
  rewrite dom_insert_L. iFrame. iSplitL "Hava".
  { rewrite /available_auth. iExists (av ∖ {[Pos.of_nat ℓ]}). iFrame.
    iPureIntro. set_solver. }
  simpl. iApply "HΦ". iFrame.
Qed.

Lemma wp_const p m n EE :
  {{{ ACC m }}}
    E [Const n] @ p; EE
  {{{ RET (); ACC n }}}.
Proof.
  iIntros (Φ) "Ha HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros ([? ?]) "(Hσ & Haa & Hava & Hlocsa) !>".
  iDestruct (excl_auth_eq with "Ha Haa") as %<-.
  iSplit. { iPureIntro. exists (λ _, True). by econstructor. }
  iIntros "!>" (X Hstep). inversion Hstep; simplify_eq.
  iMod (excl_auth_upd with "Ha Haa") as "[Ha Haa]".
  iModIntro. iExists _, _. iSplitR; first done. iFrame.
  simpl. by iApply "HΦ".
Qed.

Lemma wp_call p fn n instrs EE Φ :
  prog p !! fn = Some instrs →
  WP instrs @ p; EE {{ Φ }} -∗
  WP (E [Call fn n]) @ p; EE {{ Φ }}.
Proof.
  iIntros (Hfn) "Hwp". iApply wp_lift_step_fupd; first done.
  iIntros ([? ?]) "(Hσ & Haa & Hava & Hlocsa) !>".
  iSplit. { iPureIntro. apply head_prim_reducible.
            exists (λ _, True). by econstructor. }
  iIntros (X Hstep) "!> !> !> !>".
  apply head_reducible_prim_step in Hstep.
  2: { exists (λ _, True). by econstructor. }
  inversion Hstep; simplify_eq.
  iExists _, _. iSplitR; first done. iFrame. simplify_eq/=. done.
Qed.

End lifting.
