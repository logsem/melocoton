From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From transfinite.base_logic.lib Require Import ghost_var.
From melocoton.linking Require Import lang.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.mlanguage Require Import weakestpre.
From iris.proofmode Require Import proofmode.

(* FIXME: the proofs in this file need cleanup *)

Inductive link_state_case :=
  Boundary | In1 | In2.


Class linkGpre `{!indexT} Σ := LinkGpre {
  linkG_inG :> ghost_varG Σ link_state_case;
}.

Class linkG `{!indexT} Σ := LinkG {
  linkG_preG :> linkGpre Σ;
  linkG_γ : gname;
}.

Section Linking_logic.
Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context {val pubstate : Type}.
Context (Λ1 Λ2 : mlanguage val).
Context `{!linkG Σ}.
Context `{!mlangG val Λ1 Σ}.
Context `{!mlangG val Λ2 Σ}.
Context `{!invG Σ}.
Context (public_state_interp : pubstate → iProp Σ).
Context `{!linkable Λ1 pubstate}.
Context `{!linkable Λ2 pubstate}.
Context `{!linkableG Λ1 public_state_interp}.
Context `{!linkableG Λ2 public_state_interp}.

Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types T : protocol val Σ.

Definition link_state_interp (st : (link_lang Λ1 Λ2).(state)) : iProp Σ :=
  match st with
  | Link.St pubσ privσ1 privσ2 =>
      ghost_var linkG_γ (1/2) Boundary ∗
      public_state_interp pubσ ∗
      private_state_interp privσ1 ∗
      private_state_interp privσ2
  | Link.St1 σ1 privσ2 =>
      ghost_var linkG_γ (1/2) In1 ∗
      state_interp σ1 ∗ private_state_interp privσ2
  | Link.St2 privσ1 σ2 =>
      ghost_var linkG_γ (1/2) In2 ∗
      private_state_interp privσ1 ∗ state_interp σ2
  end.

Definition link_state_frag (case : link_state_case) : iProp Σ :=
  ghost_var linkG_γ (1/2) case.

Definition link_in_state case : iProp Σ :=
  link_state_frag case ∗
  match case with
  | Boundary => at_boundary Λ1 ∗ at_boundary Λ2
  | In1 => at_boundary Λ2
  | In2 => at_boundary Λ1
  end.

Lemma link_state_update case case' :
  ghost_var linkG_γ (1/2) case -∗ link_state_frag case ==∗
  ghost_var linkG_γ (1/2) case' ∗ link_state_frag case'.
Proof using.
  iIntros "Haa Haf". unfold link_state_frag.
  iMod (ghost_var_update_halves with "Haf Haa") as "[? ?]". by iFrame.
Qed.

Lemma link_at_boundary st :
  link_state_interp st -∗ link_state_frag Boundary -∗
  ⌜∃ pubσ privσ1 privσ2, st = Link.St pubσ privσ1 privσ2⌝.
Proof using.
  iIntros "Hst Hb". destruct st; eauto.
  all: iDestruct "Hst" as "(Hb' & _)".
  all: by iDestruct (ghost_var_agree with "Hb Hb'") as %?.
Qed.

Lemma link_at_in1 st :
  link_state_interp st -∗ link_state_frag In1 -∗
  ⌜∃ σ1 privσ2, st = Link.St1 σ1 privσ2⌝.
Proof using.
  iIntros "Hst Hb". destruct st; eauto.
  all: iDestruct "Hst" as "(Hb' & ?)".
  all: by iDestruct (ghost_var_agree with "Hb Hb'") as %?.
Qed.

Lemma link_at_in2 st :
  link_state_interp st -∗ link_state_frag In2 -∗
  ⌜∃ privσ1 σ2, st = Link.St2 privσ1 σ2⌝.
Proof using.
  iIntros "Hst Hb". destruct st; eauto.
  all: iDestruct "Hst" as "(Hb' & ?)".
  all: by iDestruct (ghost_var_agree with "Hb Hb'") as %?.
Qed.

Global Program Instance link_mlangG : mlangG val (link_lang Λ1 Λ2) Σ := {
  state_interp := link_state_interp;
  at_boundary := link_in_state Boundary;
}.

Global Program Instance link_linkableG : linkableG (link_lang Λ1 Λ2) public_state_interp := {
  private_state_interp := (λ '(privσ1, privσ2),
    ghost_var linkG_γ (1/2) Boundary ∗
    private_state_interp privσ1 ∗ private_state_interp privσ2)%I;
}.
Next Obligation.
  simpl. iIntros (σ pubσ privσ). inversion 1; subst.
  iIntros "(? & ? & ? & ?)". by iFrame.
Qed.
Next Obligation.
  simpl. iIntros (pubσ [privσ1 privσ2]) "Hpub (? & ? & ?)".
  iModIntro. iExists (Link.St _ _ _). by iFrame.
Qed.
Next Obligation.
  iIntros (σ) "(Hb & ? & ?) Hσ".
  iDestruct (link_at_boundary with "Hσ Hb") as %(? & ? & ? & ->).
  iPureIntro. eexists _, _. constructor.
Qed.

Definition link_prog
  (p1 : mlang_prog Λ1) (p2 : mlang_prog Λ2) :
  mlang_prog (link_lang Λ1 Λ2)
:=
  fmap inl p1 ∪ fmap inr p2.

Lemma proj1_prog_union (p1: mlanguage.prog Λ1) (p2: mlanguage.prog Λ2) :
  dom p1 ## dom p2 →
  Link.proj1_prog _ _ (link_prog p1 p2) = p1.
Proof using.
  intros Hdisj.
  apply map_eq. intros fname. unfold Link.proj1_prog.
  rewrite map_omap_union.
  2: { apply map_disjoint_dom. rewrite !dom_fmap//. }
  rewrite lookup_union_l.
  { rewrite lookup_omap /= lookup_fmap. by destruct (p1 !! fname). }
  { rewrite lookup_omap /= lookup_fmap. by destruct (p2 !! fname). }
Qed.

Lemma proj2_prog_union (p1: mlanguage.prog Λ1) (p2: mlanguage.prog Λ2) :
  dom p1 ## dom p2 →
  Link.proj2_prog _ _ (link_prog p1 p2) = p2.
Proof using.
  intros Hdisj.
  apply map_eq. intros fname. unfold Link.proj2_prog.
  rewrite map_omap_union.
  2: { apply map_disjoint_dom. rewrite !dom_fmap//. }
  rewrite lookup_union_r.
  { rewrite lookup_omap /= lookup_fmap. by destruct (p2 !! fname). }
  { rewrite lookup_omap /= lookup_fmap. by destruct (p1 !! fname). }
Qed.

Class can_link
  (p1 : mlang_prog Λ1) (Ψ1 : protocol val Σ)
  (p2 : mlang_prog Λ2) (Ψ2 : protocol val Σ)
  (Ψ : protocol val Σ)
:= CanLink {
  can_link_prog_disj : dom p1 ## dom p2;
  can_link_internal1 E : Ψ1 on (dom p2) ⊑ mprog_proto E p2 Ψ2;
  can_link_internal2 E : Ψ2 on (dom p1) ⊑ mprog_proto E p1 Ψ1;
  can_link_external1 : Ψ1 except (dom p2) ⊑ Ψ;
  can_link_external2 : Ψ2 except (dom p1) ⊑ Ψ;
}.

Lemma wp_link_call (pe : prog_environ (link_lang Λ1 Λ2) Σ) E k fn vs Φ fname :
  penv_prog pe !! fname = Some fn →
  WP Link.LkE (Link.RunFunction fn vs) k @ pe; E {{ Φ }} -∗
  WP Link.LkE (Link.ExprCall fname vs) k @ pe; E {{ Φ }}.
Proof using.
  iIntros (Hfn) "Hwp".
  iApply wp_unfold. rewrite /wp_pre.
  iIntros (σ) "Hσ". iModIntro. iRight; iRight.
  iSplit; first done.
  iExists (λ '(e', σ'), e' = Link.LkE (Link.RunFunction fn vs) k ∧ σ' = σ).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (e' σ' (-> & ->)). do 3 iModIntro. iFrame.
Qed.

Lemma wp_link_run_function_1 p1 p2 Ψ1 Ψ2 Ψ E k2 k fn arg fname Φ Ξ :
  can_link p1 Ψ1 p2 Ψ2 Ψ →
  p1 !! fname = Some fn →
  link_state_frag Boundary -∗
  at_boundary Λ1 -∗
  Ψ2 fname arg Ξ -∗
  (∀ e1, ⌜apply_func fn arg = Some e1⌝ -∗
         WP e1 @ ⟪p1, Ψ1⟫; E {{ v, Ξ v ∗ at_boundary Λ1 }} -∗
         link_state_frag In1 -∗
         WP Link.LkE (Link.Expr1 e1) (inr k2 :: k) @ ⟪link_prog p1 p2, Ψ⟫; E {{ Φ }}) -∗
  WP Link.LkE (Link.RunFunction (inl fn) arg) (inr k2 :: k) @ ⟪link_prog p1 p2, Ψ⟫; E {{ Φ }}.
Proof using.
  iIntros (Hcanlink Hfn) "Hb Hb1 HTΞ Hwp".
  iApply wp_unfold. rewrite /wp_pre.
  iIntros (σ) "Hσ". iDestruct (link_at_boundary with "Hσ Hb") as %(pubσ&privσ1&privσ2&->).
  iRight; iRight.
  iPoseProof (can_link_internal2 _ _ _ with "[HTΞ]") as "H".
  { rewrite /proto_on. iFrame. iPureIntro. by eapply elem_of_dom_2. }
  rewrite /mprog_proto Hfn. iDestruct "H" as (? Happlyfunc) "Hwpcall".
  iDestruct "Hσ" as "(Hob & Hpubσ & Hprivσ1 & Hprivσ2)".
  iMod (state_interp_join with "Hpubσ Hprivσ1") as (σ1) "(Hσ1 & %Hsplit)". iModIntro.
  iSplit; first done.
  iExists (λ '(e', σ'), e' = Link.LkE (Link.Expr1 e) (inr k2 :: k) ∧
                        σ' = Link.St1 σ1 privσ2).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (e' σ' (-> & ->)). do 2 iModIntro.
  iMod (link_state_update _ In1 with "Hob Hb") as "(Hob & Hb)".
  iModIntro. iFrame.
  iDestruct ("Hwpcall" with "Hb1") as "Hwpcall".
  iApply ("Hwp" with "[] Hwpcall Hob"); first done.
Qed.

Lemma wp_link_run_function_2 p1 p2 Ψ1 Ψ2 Ψ E k1 k fn arg fname Φ Ξ :
  can_link p1 Ψ1 p2 Ψ2 Ψ →
  p2 !! fname = Some fn →
  link_state_frag Boundary -∗
  at_boundary Λ2 -∗
  Ψ1 fname arg Ξ -∗
  (∀ e2, ⌜apply_func fn arg = Some e2⌝ -∗
         WP e2 @ ⟪p2, Ψ2⟫; E {{ v, Ξ v ∗ at_boundary Λ2 }} -∗
         link_state_frag In2 -∗
         WP Link.LkE (Link.Expr2 e2) (inl k1 :: k) @ ⟪link_prog p1 p2, Ψ⟫; E {{ Φ }}) -∗
  WP Link.LkE (Link.RunFunction (inr fn) arg) (inl k1 :: k) @ ⟪link_prog p1 p2, Ψ⟫; E {{ Φ }}.
Proof using.
  iIntros (Hcanlink Hfn) "Hb Hb2 HTΞ Hwp".
  iApply wp_unfold. rewrite /wp_pre.
  iIntros (σ) "Hσ". iDestruct (link_at_boundary with "Hσ Hb") as %(pubσ&privσ1&privσ2&->).
  iRight; iRight.
  iPoseProof (can_link_internal1 _ _ _ with "[HTΞ]") as "H".
  { rewrite /proto_on. iFrame. iPureIntro. by eapply elem_of_dom_2. }
  rewrite /mprog_proto Hfn. iDestruct "H" as (? Happlyfunc) "Hwpcall".
  iDestruct "Hσ" as "(Hob & Hpubσ & Hprivσ1 & Hprivσ2)".
  iMod (state_interp_join with "Hpubσ Hprivσ2") as (σ2) "(Hσ2 & %Hsplit)". iModIntro.
  iSplit; first done.
  iExists (λ '(e', σ'), e' = Link.LkE (Link.Expr2 e) (inl k1 :: k) ∧
                        σ' = Link.St2 privσ1 σ2).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (e' σ' (-> & ->)). do 2 iModIntro.
  iMod (link_state_update _ In2 with "Hob Hb") as "(Hob & Hb)".
  iModIntro. iFrame.
  iDestruct ("Hwpcall" with "Hb2") as "Hwpcall".
  by iApply ("Hwp" with "[] Hwpcall Hob").
Qed.

Lemma wp_link_retval_1 (pe : prog_environ (link_lang Λ1 Λ2) Σ) E k1 v Φ :
  (link_state_frag In1 -∗ WP LkSE (Link.Expr1 (resume_with k1 (of_val Λ1 v))) @ pe; E {{ Φ }}) -∗
  (link_state_frag Boundary -∗ WP Link.LkE (Link.ExprV v) [inl k1] @ pe; E {{ Φ }}).
Proof using.
  iIntros "Hwp Hb".
  iApply wp_unfold. rewrite /wp_pre.
  iIntros (σ) "Hσ". iDestruct (link_at_boundary with "Hσ Hb") as %(pubσ&privσ1&privσ2&->).
  iDestruct "Hσ" as "(Hob & Hpub & Hpriv1 & Hpriv2)".
  iMod (state_interp_join with "Hpub Hpriv1") as (σ1) "[Hσ1 %Hsplit]".
  iModIntro. iRight. iRight.
  iSplitR; first done.
  iExists (λ '(e', σ'), e' = LkSE (Link.Expr1 (resume_with k1 (of_val Λ1 v))) ∧
                        σ' = Link.St1 σ1 privσ2).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (? ? (-> & ->)). iModIntro. iNext.
  iMod (link_state_update _ In1 with "Hob Hb") as "(Hob & Hb)".
  iModIntro. iFrame. by iApply "Hwp".
Qed.

Lemma wp_link_retval_2 (pe : prog_environ (link_lang Λ1 Λ2) Σ) E k2 v Φ :
  (link_state_frag In2 -∗ WP LkSE (Link.Expr2 (resume_with k2 (of_val Λ2 v))) @ pe; E {{ Φ }}) -∗
  (link_state_frag Boundary -∗ WP Link.LkE (Link.ExprV v) [inr k2] @ pe; E {{ Φ }}).
Proof using.
  iIntros "Hwp Hb".
  iApply wp_unfold. rewrite /wp_pre.
  iIntros (σ) "Hσ". iDestruct (link_at_boundary with "Hσ Hb") as %(pubσ&privσ1&privσ2&->).
  iDestruct "Hσ" as "(Hob & Hpub & Hpriv1 & Hpriv2)".
  iMod (state_interp_join with "Hpub Hpriv2") as (σ2) "[Hσ2 %Hsplit]".
  iModIntro. iRight. iRight.
  iSplitR; first done.
  iExists (λ '(e', σ'), e' = LkSE (Link.Expr2 (resume_with k2 (of_val Λ2 v))) ∧
                        σ' = Link.St2 privσ1 σ2).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (? ? (-> & ->)). iModIntro. iNext.
  iMod (link_state_update _ In2 with "Hob Hb") as "(Hob & Hb)".
  iModIntro. iFrame. by iApply "Hwp".
Qed.

Lemma wp_link_extcall_1 p1 p2 Ψ1 Ψ2 Ψ E k1 fn_name arg Φ Ξ :
  can_link p1 Ψ1 p2 Ψ2 Ψ →
  p1 !! fn_name = None →
  p2 !! fn_name = None →
  Ψ1 fn_name arg Ξ -∗
  (▷ ∀ r : val, Ξ r ∗ at_boundary Λ1 -∗
        WP resume_with k1 (of_val Λ1 r) @ ⟪p1, Ψ1⟫; E {{ λ v, Φ v ∗ at_boundary Λ1 }}) -∗
  (▷ ∀ r, WP resume_with k1 (of_val Λ1 r) @ ⟪p1, Ψ1⟫; E {{ λ v, Φ v ∗ at_boundary Λ1 }} -∗
        link_state_frag Boundary -∗
        at_boundary Λ2 -∗
        WP Link.LkE (Link.ExprV r) [inl k1] @ ⟪link_prog p1 p2, Ψ⟫; E {{ λ v, Φ v ∗ at_boundary (link_lang Λ1 Λ2) }}) -∗
  at_boundary (link_lang Λ1 Λ2) -∗
  WP Link.LkE (Link.ExprCall fn_name arg) [inl k1] @ ⟪link_prog p1 p2, Ψ⟫; E {{ λ v, Φ v ∗ at_boundary (link_lang Λ1 Λ2) }}.
Proof using.
  iIntros (Hcanlink Hfn1 Hfn2) "HTΞ HΞ Hwp (Hb & Hb1 & Hb2)".
  iApply wp_unfold. rewrite /wp_pre.
  iIntros (σ) "Hσ". iDestruct (link_at_boundary with "Hσ Hb") as %(pubσ&privσ1&privσ2&->).
  iModIntro. iRight; iLeft. iExists _, _, [inl k1]. iSplitR; [by eauto|].
  iSplit.
  { iPureIntro. apply lookup_union_None. rewrite !lookup_fmap Hfn1 Hfn2 //. }
  iFrame "Hσ Hb Hb1 Hb2". iExists Ξ. iSplitL "HTΞ".
  { cbn. iApply can_link_external1. iFrame. iPureIntro.
    by apply not_elem_of_dom_2. }
  iNext. iIntros (r) "[Hr Hb]". iDestruct "Hb" as "(Hb & Hb1 & Hb2)".
  simpl.
  iSpecialize ("HΞ" with "[$Hr $Hb1]").
  iApply ("Hwp" with "HΞ Hb Hb2").
Qed.

Lemma wp_link_extcall_2 p1 p2 Ψ1 Ψ2 Ψ E k2 fn_name arg Φ Ξ :
  can_link p1 Ψ1 p2 Ψ2 Ψ →
  p1 !! fn_name = None →
  p2 !! fn_name = None →
  Ψ2 fn_name arg Ξ -∗
  (▷ ∀ r : val, Ξ r ∗ at_boundary Λ2 -∗
        WP resume_with k2 (of_val Λ2 r) @ ⟪p2, Ψ2⟫; E {{ λ v, Φ v ∗ at_boundary Λ2 }}) -∗
  (▷ ∀ r, WP resume_with k2 (of_val Λ2 r) @ ⟪p2, Ψ2⟫; E {{ λ v, Φ v ∗ at_boundary Λ2 }} -∗
        link_state_frag Boundary -∗
        at_boundary Λ1 -∗
        WP Link.LkE (Link.ExprV r) [inr k2] @ ⟪link_prog p1 p2, Ψ⟫; E {{ λ v, Φ v ∗ at_boundary (link_lang Λ1 Λ2) }}) -∗
  at_boundary (link_lang Λ1 Λ2) -∗
  WP Link.LkE (Link.ExprCall fn_name arg) [inr k2] @ ⟪link_prog p1 p2, Ψ⟫; E {{ λ v, Φ v ∗ at_boundary (link_lang Λ1 Λ2) }}.
Proof using.
  iIntros (Hcanlink Hfn1 Hfn2) "HTΞ HΞ Hwp (Hb & Hb1 & Hb2)".
  iApply wp_unfold. rewrite /wp_pre.
  iIntros (σ) "Hσ". iDestruct (link_at_boundary with "Hσ Hb") as %(pubσ&privσ1&privσ2&->).
  iModIntro. iRight; iLeft. iExists _, _, [inr k2]. iSplitR; [by eauto|].
  iSplit.
  { iPureIntro. apply lookup_union_None. rewrite !lookup_fmap Hfn1 Hfn2 //. }
  iFrame "Hσ Hb Hb1 Hb2". iExists Ξ. iSplitL "HTΞ".
  { cbn. iApply can_link_external2. iFrame. iPureIntro.
    by apply not_elem_of_dom_2. }
  iNext. iIntros (r) "[Hr Hb]". iDestruct "Hb" as "(Hb & Hb1 & Hb2)".
  simpl.
  iSpecialize ("HΞ" with "[$Hr $Hb2]").
  iApply ("Hwp" with "HΞ Hb Hb1").
Qed.

Lemma wp_link_run_mut p1 p2 Ψ1 Ψ2 Ψ E :
  can_link p1 Ψ1 p2 Ψ2 Ψ →
  ⊢ □ (
    (∀ e1 Φ, WP e1 @ ⟪p1, Ψ1⟫; E {{ λ v, Φ v ∗ at_boundary Λ1 }} -∗ link_in_state In1 -∗
             WP (LkSE (Link.Expr1 e1)) @ ⟪link_prog p1 p2, Ψ⟫; E {{ λ v, Φ v ∗ link_in_state Boundary }}) ∗
    (∀ e2 Φ, WP e2 @ ⟪p2, Ψ2⟫; E {{ λ v, Φ v ∗ at_boundary Λ2 }} -∗ link_in_state In2 -∗
             WP (LkSE (Link.Expr2 e2)) @ ⟪link_prog p1 p2, Ψ⟫; E {{ λ v, Φ v ∗ link_in_state Boundary }})
  ).
Proof using.
  intros Hcanlink. iLöb as "IH". iModIntro. iSplitL.
  (* Case 1: running Λ1 *)
  { iIntros (e1 Φ) "Hwp [Hb Hb2]".
    rewrite wp_unfold. rewrite /wp_pre.
    iApply wp_unfold. rewrite /wp_pre.
    iIntros (σ) "Hσ". iDestruct (link_at_in1 with "Hσ Hb") as %(σ1 & privσ2 & ->).
    iDestruct "Hσ" as "(Hob & Hσ1 & Hpriv2)".
    iMod ("Hwp" $! σ1 with "[$Hσ1]") as "[Hwp|[Hwp|Hwp]]".

    (* WP: value case *)
    { iDestruct "Hwp" as (v ->) "[Hσ [HΦ Hb1]]".
      iModIntro. iRight; iRight.
      (* administrative step Val1S: Link.Expr1 ~> Link.ExprV *)
      iDestruct (@splittable_at_boundary with "Hb1 Hσ") as %(pubσ&privσ1&Hsplitσ1).
      iSplit; first done.
      iExists (λ '(e', σ'), e' = LkSE (Link.ExprV v) ∧ σ' = Link.St pubσ privσ1 privσ2).
      iSplit. { iPureIntro. eapply Link.Val1S; eauto. rewrite to_of_val //. }
      iIntros (? ? (-> & ->)).
      iMod (state_interp_split with "Hσ") as "[Hpriv1 Hpub]"; first by eauto.
      iMod (link_state_update _ Boundary with "Hob Hb") as "[Hob Hb]".
      do 3 iModIntro. iFrame. by iApply wp_value. }

    (* WP: call case *)
    { iDestruct "Hwp" as (f vs C Hiscall Hf) "(Hb1 & Hσ1 & Hcall)". iModIntro. iRight; iRight.
      (* administrative step MakeCall1S: Link.Expr1 ~> Link.ExprCall *)
      iDestruct (@splittable_at_boundary with "Hb1 Hσ1") as %(pubσ&privσ1&Hsplitσ1).
      iSplitR; first by eauto.
      iExists (λ '(e', σ'), e' = Link.LkE (Link.ExprCall f vs) [inl C] ∧
                            σ' = Link.St pubσ privσ1 privσ2).
      iSplit.
      { iPureIntro. eapply Link.MakeCall1S; eauto.
        rewrite proj1_prog_union; eauto. eapply Hcanlink. }
      iIntros (? ? (-> & ->)).

      iDestruct "Hcall" as (Ξ) "[HTΞ HΞ]".
      iMod (state_interp_split with "Hσ1") as "[Hpriv1 Hpub]"; first done.
      iMod (link_state_update _ Boundary with "Hob Hb") as "[Hob Hb]".
      do 3 iModIntro. iFrame "Hob Hpub Hpriv1 Hpriv2".

      (* two cases: this is an external call of the linking module itself, or it
         is a call to a function of pe2 *)
      destruct (p2 !! f) as [fn2|] eqn:Hf2.

      { (* call to a function of pe2 *)
        assert (link_prog p1 p2 !! f = Some (inr fn2)) as Hpef.
        { rewrite lookup_union_r lookup_fmap. 1: by rewrite Hf2. by rewrite Hf. }

        (* administrative step CallS: Link.ExprCall ~> LinkRunFunction *)
        iApply wp_link_call; first done.
        (* administrative step RunFunction2S: LinkRunFunction ~> Link.Expr2 *)
        iApply (wp_link_run_function_2 with "Hb Hb2 HTΞ"); first done.
        iIntros (e2 He2) "Hwpcall Hb".

        progress change (Link.LkE (Link.Expr2 e2) [inl C]) with
          (resume_with ([inl C]:cont (link_lang Λ1 Λ2)) (LkSE (Link.Expr2 e2))).
        iApply wp_bind.
        iApply (wp_wand with "[Hwpcall Hb Hb1]").
        { iDestruct "IH" as "#[_ IH2]". iApply ("IH2" with "Hwpcall [$Hb $Hb1]"). }
        iIntros (r) "[Hr (Hb & Hb1 & Hb2)]". iSpecialize ("HΞ" $! r).
        cbn.
        (* administrative step Ret1S: Link.ExprV ~> Link.Expr1 *)
        iApply (wp_link_retval_1 with "[-Hb] Hb"). iIntros "Hb".
        (* continue the execution by induction *)
        iDestruct "IH" as "#[IH1 _]". iApply ("IH1" with "[-Hb Hb2] [$Hb $Hb2]").
        iApply "HΞ". iFrame. }

      { (* external call *)
        iApply (wp_link_extcall_1 with "HTΞ HΞ [] [$Hb $Hb1 $Hb2]"); auto.
        iNext.
        iIntros (r) "HΞ Hb Hb2".
        (* administrative step Ret1S: Link.ExprV ~> Link.Expr1 *)
        iApply (wp_link_retval_1 with "[-Hb] Hb"). iIntros "Hb".
        (* continue the execution by induction *)
        iDestruct "IH" as "#[IH1 _]". iApply ("IH1" with "HΞ [$Hb $Hb2]"). } }

    { (* WP: step case *)
      iDestruct "Hwp" as (Hnv X Hstep) "Hwp".
      iModIntro. iRight; iRight. iSplit; first done.
      iExists (λ '(e', σ'), ∃ e1' σ1', X (e1', σ1') ∧
                  e' = LkSE (Link.Expr1 e1') ∧
                  σ' = Link.St1 σ1' privσ2).
      iSplit.
      { iPureIntro. econstructor; eauto.
        rewrite proj1_prog_union; eauto. apply Hcanlink. }
      iIntros (e' σ' (? & ? & HX & -> & ->)).
      iSpecialize ("Hwp" $! _ _ HX). iMod "Hwp". iIntros "!>!>". iMod "Hwp" as "[Hσ Hwp]".
      iModIntro. iFrame "Hσ Hob Hpriv2".
      iDestruct "IH" as "[IH1 _]". iApply ("IH1" with "Hwp [$Hb $Hb2]"). } }

  (* Case 2: running Λ2 *)
  { iIntros (e1 Φ) "Hwp [Hb Hb1]".
    rewrite wp_unfold. rewrite /wp_pre.
    iApply wp_unfold. rewrite /wp_pre.
    iIntros (σ) "Hσ". iDestruct (link_at_in2 with "Hσ Hb") as %(privσ1 & σ2 & ->).
    iDestruct "Hσ" as "(Hob & Hpriv1 & Hσ2)".
    iMod ("Hwp" $! σ2 with "[$Hσ2]") as "[Hwp|[Hwp|Hwp]]".

    (* WP: value case *)
    { iDestruct "Hwp" as (v ->) "[Hσ [HΦ Hb2]]".
      iModIntro. iRight; iRight.
      (* administrative step Val2S: Link.Expr2 ~> Link.ExprV *)
      iDestruct (@splittable_at_boundary with "Hb2 Hσ") as %(pubσ&privσ2&Hsplitσ2).
      iSplit; first done.
      iExists (λ '(e', σ'), e' = LkSE (Link.ExprV v) ∧ σ' = Link.St pubσ privσ1 privσ2).
      iSplit. { iPureIntro. eapply Link.Val2S; eauto. rewrite to_of_val //. }
      iIntros (? ? (-> & ->)).
      iMod (state_interp_split with "Hσ") as "[Hpriv2 Hpub]"; first by eauto.
      iMod (link_state_update _ Boundary with "Hob Hb") as "[Hob Hb]".
      do 3 iModIntro. iFrame. by iApply wp_value. }

    (* WP: call case *)
    { iDestruct "Hwp" as (f vs C Hiscall Hf) "(Hb2 & Hσ2 & Hcall)". iModIntro. iRight; iRight.
      (* administrative step MakeCall2S: Link.Expr2 ~> Link.ExprCall *)
      iDestruct (@splittable_at_boundary with "Hb2 Hσ2") as %(pubσ&privσ2&Hsplitσ2).
      iSplitR; first by eauto.
      iExists (λ '(e', σ'), e' = Link.LkE (Link.ExprCall f vs) [inr C] ∧
                            σ' = Link.St pubσ privσ1 privσ2).
      iSplit.
      { iPureIntro. eapply Link.MakeCall2S; eauto.
        rewrite proj2_prog_union; eauto. eapply Hcanlink. }
      iIntros (? ? (-> & ->)).

      iDestruct "Hcall" as (Ξ) "[HTΞ HΞ]".
      iMod (state_interp_split with "Hσ2") as "[Hpub Hpriv2]"; first done.
      iMod (link_state_update _ Boundary with "Hob Hb") as "[Hob Hb]".
      do 3 iModIntro. iFrame "Hob Hpub Hpriv1 Hpriv2".

      (* two cases: this is an external call of the linking module itself, or it
         is a call to a function of pe1 *)
      destruct (p1 !! f) as [fn1|] eqn:Hf1.

      { (* call to a function of pe1 *)
        assert (link_prog p1 p2 !! f = Some (inl fn1)) as Hpef.
        { rewrite lookup_union_l lookup_fmap. 1: by rewrite Hf1. by rewrite Hf. }

        (* administrative step CallS: Link.ExprCall ~> LinkRunFunction *)
        iApply wp_link_call; first done.
        (* administrative step RunFunction1S: LinkRunFunction ~> Link.Expr1 *)
        iApply (wp_link_run_function_1 with "Hb Hb1 HTΞ"); first done.
        iIntros (e2 He2) "Hwpcall Hb".

        progress change (Link.LkE (Link.Expr1 e2) [inr C]) with
          (resume_with ([inr C]:cont (link_lang Λ1 Λ2)) (LkSE (Link.Expr1 e2))).
        iApply wp_bind.
        iApply (wp_wand with "[Hwpcall Hb Hb2]").
        { iDestruct "IH" as "#[IH1 _]". iApply ("IH1" with "Hwpcall [$Hb $Hb2]"). }
        iIntros (r) "[Hr (Hb & Hb1 & Hb2)]". iSpecialize ("HΞ" $! r).
        cbn.
        (* administrative step Ret2S: Link.ExprV ~> Link.Expr1 *)
        iApply (wp_link_retval_2 with "[-Hb] Hb"). iIntros "Hb".
        (* continue the execution by induction *)
        iDestruct "IH" as "#[_ IH2]". iApply ("IH2" with "[-Hb Hb1] [$Hb $Hb1]").
        iApply "HΞ". iFrame. }

      { (* external call *)
        iApply (wp_link_extcall_2 with "HTΞ HΞ [] [$Hb $Hb1 $Hb2]"); auto.
        iNext.
        iIntros (r) "HΞ Hb Hb1".
        (* administrative step Ret2S: Link.ExprV ~> Link.Expr2 *)
        iApply (wp_link_retval_2 with "[-Hb] Hb"). iIntros "Hb".
        (* continue the execution by induction *)
        iDestruct "IH" as "#[_ IH2]". iApply ("IH2" with "HΞ [$Hb $Hb1]"). } }

    { (* WP: step case *)
      iDestruct "Hwp" as (Hnv X Hstep) "Hwp". iModIntro. iRight; iRight. iSplit; first done.
      iExists (λ '(e', σ'), ∃ e2' σ2', X (e2', σ2') ∧
                  e' = LkSE (Link.Expr2 e2') ∧
                  σ' = Link.St2 privσ1 σ2').
      iSplit.
      { iPureIntro. econstructor; eauto.
        rewrite proj2_prog_union; eauto. apply Hcanlink. }
      iIntros (e' σ' (? & ? & HX & -> & ->)).
      iSpecialize ("Hwp" $! _ _ HX). iMod "Hwp". iIntros "!>!>". iMod "Hwp" as "[Hσ Hwp]".
      iModIntro. iFrame "Hσ Hob Hpriv1".
      iDestruct "IH" as "[_ IH2]". iApply ("IH2" with "Hwp [$Hb $Hb1]"). } }
Qed.

Lemma wp_link_run1 p1 p2 Ψ1 Ψ2 Ψ E e1 Φ :
  can_link p1 Ψ1 p2 Ψ2 Ψ →
  link_in_state In1 -∗
  WP e1 @ ⟪p1, Ψ1⟫; E {{ λ v, Φ v ∗ at_boundary Λ1 }} -∗
  WP LkSE (Link.Expr1 e1) @ ⟪link_prog p1 p2, Ψ⟫; E {{ λ v, Φ v ∗ link_in_state Boundary }}.
Proof using.
  iIntros (Hcanlink) "Hlkst Hwp". iDestruct (wp_link_run_mut _ _ _ _ _ _ Hcanlink) as "[H _]".
  iApply ("H" with "Hwp Hlkst").
Qed.

Lemma wp_link_run1' p1 p2 Ψ1 Ψ2 Ψ E e1 Φ Φ' :
  can_link p1 Ψ1 p2 Ψ2 Ψ →
  link_in_state In1 -∗
  WP e1 @ ⟪p1, Ψ1⟫; E {{ λ v, Φ v ∗ at_boundary Λ1 }} -∗
  (∀ v, Φ v ∗ link_in_state Boundary -∗ Φ' v) -∗
  WP LkSE (Link.Expr1 e1) @ ⟪link_prog p1 p2, Ψ⟫; E {{ Φ' }}.
Proof using.
  iIntros (?) "Hin Hwp HΦ". iApply (wp_wand with "[-HΦ]").
  { iApply (wp_link_run1 with "Hin Hwp"). }
  done.
Qed.

Lemma wp_link_run2 p1 p2 Ψ1 Ψ2 Ψ E e2 Φ :
  can_link p1 Ψ1 p2 Ψ2 Ψ →
  link_in_state In2 -∗
  WP e2 @ ⟪p2, Ψ2⟫; E {{ λ v, Φ v ∗ at_boundary Λ2 }} -∗
  WP LkSE (Link.Expr2 e2) @ ⟪link_prog p1 p2, Ψ⟫; E {{ λ v, Φ v ∗ link_in_state Boundary }}.
Proof using.
  iIntros (Hcanlink) "Hlkst Hwp". iDestruct (wp_link_run_mut _ _ _ _ _ _ Hcanlink) as "[_ H]".
  iApply ("H" with "Hwp Hlkst").
Qed.

Lemma wp_link_run2' p1 p2 Ψ1 Ψ2 Ψ E e2 Φ Φ' :
  can_link p1 Ψ1 p2 Ψ2 Ψ →
  link_in_state In2 -∗
  WP e2 @ ⟪p2, Ψ2⟫; E {{ λ v, Φ v ∗ at_boundary Λ2 }} -∗
  (∀ v, Φ v ∗ link_in_state Boundary -∗ Φ' v) -∗
  WP LkSE (Link.Expr2 e2) @ ⟪link_prog p1 p2, Ψ⟫; E {{ Φ' }}.
Proof using.
  iIntros (?) "Hin Hwp HΦ". iApply (wp_wand with "[-HΦ]").
  { iApply (wp_link_run2 with "Hin Hwp"). }
  done.
Qed.

Lemma wp_link_internal_call p fn vs (func: Link.func Λ1 Λ2) Φ E :
  penv_prog p !! fn = Some func →
  (▷ WP LkSE (Link.RunFunction func vs) @ p; E {{ Φ }}) -∗
  WP LkSE (Link.ExprCall fn vs) @ p; E {{ Φ }}.
Proof using.
  iIntros (Hfn) "Hwp".
  by iApply wp_internal_call.
Qed.

Lemma wp_link_run_function1 p (func : Λ1.(func)) vs e1 Φ E :
  apply_func func vs = Some e1 →
  link_in_state Boundary -∗
  ▷ (link_in_state In1 -∗ at_boundary Λ1 -∗
      WP LkSE (Link.Expr1 e1) @ p; E {{ Φ }}) -∗
  WP LkSE (Link.RunFunction (inl func) vs) @ p; E {{ Φ }}.
Proof using.
  iIntros (Hfunc) "(Hb & Hb1 & Hb2) Hwp". iApply wp_unfold. rewrite /wp_pre /=.
  iIntros (σ) "Hσ".
  iDestruct (link_at_boundary with "Hσ Hb") as %(pubσ & privσ1 & privσ2 & ->).
  iDestruct "Hσ" as "(Hob & Hpub & Hpriv1 & Hpriv2)".
  iMod (state_interp_join with "Hpub Hpriv1") as (σ1) "(Hσ1 & %Hsplit)".
  iModIntro. iRight. iRight.
  iSplitR; first done.
  iExists (λ '(e', σ'), e' = LkSE (Link.Expr1 e1) ∧ σ' = Link.St1 σ1 privσ2).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (? ? (-> & ->)).
  iMod (link_state_update _ In1 with "Hob Hb") as "[Hob Hb]".
  iIntros "!>!>!>". iFrame. iApply ("Hwp" with "[-Hb1] Hb1"). iFrame.
Qed.

Lemma wp_link_run_function2 p (func : Λ2.(func)) vs e2 Φ E :
  apply_func func vs = Some e2 →
  link_in_state Boundary -∗
  ▷ (link_in_state In2 -∗ at_boundary Λ2 -∗
      WP LkSE (Link.Expr2 e2) @ p; E {{ Φ }}) -∗
  WP LkSE (Link.RunFunction (inr func) vs) @ p; E {{ Φ }}.
Proof using.
  iIntros (Hfunc) "(Hb & Hb1 & Hb2) Hwp". iApply wp_unfold. rewrite /wp_pre /=.
  iIntros (σ) "Hσ".
  iDestruct (link_at_boundary with "Hσ Hb") as %(pubσ & privσ1 & privσ2 & ->).
  iDestruct "Hσ" as "(Hob & Hpub & Hpriv1 & Hpriv2)".
  iMod (state_interp_join with "Hpub Hpriv2") as (σ2) "(Hσ2 & %Hsplit)".
  iModIntro. iRight. iRight.
  iSplitR; first done.
  iExists (λ '(e', σ'), e' = LkSE (Link.Expr2 e2) ∧ σ' = Link.St2 privσ1 σ2).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (? ? (-> & ->)).
  iMod (link_state_update _ In2 with "Hob Hb") as "[Hob Hb]".
  iIntros "!>!>!>". iFrame. iApply ("Hwp" with "[-Hb2] Hb2"). iFrame.
Qed.

Lemma link_refines E p1 Ψ1 p2 Ψ2 Ψ :
  can_link p1 Ψ1 p2 Ψ2 Ψ →
  mprog_proto E p1 Ψ1 ⊔ mprog_proto E p2 Ψ2 ⊑ mprog_proto E (link_prog p1 p2) Ψ.
Proof using.
  iIntros (Hcanlink ? ? ?) "H".
  rewrite /join /proto_join_join /proto_join /mprog_proto.
  destruct (p1 !! s) as [fn|] eqn:HH1.
  { destruct (p2 !! s) eqn:HH2; first exfalso.
    { destruct Hcanlink. apply elem_of_dom_2 in HH1, HH2. set_solver. }
    assert (link_prog p1 p2 !! s = Some (inl fn)) as HH3.
    { rewrite /link_prog lookup_union_l lookup_fmap //.
      1: rewrite HH1 //. rewrite HH2 //. (*TODO: lemma*) }
    iApply (bi.or_elim with "H"); iIntros "H"; last done.
    iDestruct "H" as (? ?) "H". rewrite HH3.
    iExists _. iSplit; first done. iNext. iIntros "Hb".
    iApply (wp_link_run_function1 with "Hb"); first done.
    iNext. iIntros "Hin Hb".
    iApply (wp_link_run1 with "Hin"). iApply ("H" with "Hb"). }
  { destruct (p2 !! s) as [fn|] eqn:HH2.
    2: { iExFalso. iApply (bi.or_elim with "H"); by iIntros. }
    assert (link_prog p1 p2 !! s = Some (inr fn)) as HH3.
    { rewrite /link_prog lookup_union_r lookup_fmap //.
      1: rewrite HH2 //. rewrite HH1 //. (*TODO: lemma*) }
    iApply (bi.or_elim with "H"); iIntros "H"; first done.
    iDestruct "H" as (? ?) "H". rewrite HH3.
    iExists _. iSplit; first done. iNext. iIntros "Hb".
    iApply (wp_link_run_function2 with "Hb"); first done.
    iNext. iIntros "Hin Hb".
    iApply (wp_link_run2 with "Hin"). iApply ("H" with "Hb"). }
Qed.

End Linking_logic.

Global Arguments can_link {_ _ _} _ _ {_ _ _} p1 Ψ1 p2 Ψ2 Ψ.
