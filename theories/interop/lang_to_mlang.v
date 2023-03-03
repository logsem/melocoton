From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.mlanguage Require Import mlanguage.
(* From melocoton.interop Require Import linking. *)
From melocoton.language Require Import language.

Section ToMlang.
  Context {val : Type}.
  Context (Λ : language val).

  Local Notation prog := (gmap string Λ.(func)).
  Local Notation expr_state := ((Λ.(expr) * Λ.(state)))%type.

  Inductive prim_step_mrel : prog -> expr_state -> (expr_state->Prop) -> Prop := 
  | LiftStep p e1 σ1 e2 σ2 (X : _ → Prop) : 
        prim_step p e1 σ1 e2 σ2 [] → 
        (X (e2, σ2)) →
      prim_step_mrel p (e1,σ1) X
  | LiftUbStep p e1 σ1 X :
        stuck_no_threads p e1 σ1 →
      prim_step_mrel p (e1,σ1) X.

  Program Definition prim_step (p : prog) : umrel (expr_state) :=
    {| mrel := prim_step_mrel p |}.
  Next Obligation.
    intros p. intros [e1 σ1] X Y Hstep HXY. inversion Hstep; subst.
    - eapply (LiftStep p e1 σ1 e2 σ2); first done. apply HXY, H4.
    - by eapply (LiftUbStep p e1 σ1).
  Qed.

  Notation cont := Λ.(ectx).

  Definition is_call (e : Λ.(expr)) (s : string) (vs : list val) (C : cont) : Prop := 
    e = fill C (of_class Λ (ExprCall s vs)).

  Definition XM_for (P:Prop) : Prop := P ∨ ¬ P.
  Axiom (XM_for_reducible_no_thread : ∀ p e σ, XM_for (reducible_no_threads (Λ:=Λ) p e σ)).

  Lemma language_mlanguage_mixin :
    MlanguageMixin (val:=val) (of_val Λ) to_val is_call (fill) (Λ.(apply_func)) prim_step.
  Proof using.
    constructor.
    - apply to_of_val.
    - apply of_to_val.
    - intros p v σ X H; inversion H; simplify_eq.
      + by eapply val_prim_step.
      + destruct H4 as [H4 _]. rewrite to_of_val in H4; done.
    - intros p e f vs C σ X ->. split; intros H.
      + inversion H; simplify_eq.
        * apply prim_step_call_inv in H3 as (er&fn&HH1&HH2&->&->&_).
          intros ? ? ? ?; simplify_eq; simplify_map_eq; congruence.
        * destruct H4 as [Hv Hpr]. intros fn e2 HH1 HH2; exfalso; eapply Hpr.
          eapply fill_prim_step, head_prim_step, call_head_step. by repeat eexists.
      + destruct (p !! f) as [fn|] eqn:Heq1; first destruct (apply_func fn vs) as [e2|] eqn:Heq2.
        * eapply LiftStep; last by eapply H.
          eapply fill_prim_step, head_prim_step, call_head_step. by repeat eexists.
        * eapply LiftUbStep. split; first apply to_val_fill_call.
          intros e' σ' (er&fn'&HH1&HH2&->&->&_)%prim_step_call_inv; repeat simplify_eq. congruence.
        * eapply LiftUbStep. split; first apply to_val_fill_call.
          intros e' σ' (er&fn'&HH1&HH2&->&->&_)%prim_step_call_inv; repeat simplify_eq.
    - intros e [v Hv] f vs C ->. rewrite to_val_fill_call in Hv; done.
    - intros p e σ H.
      destruct (XM_for_reducible_no_thread p e σ) as [(e2&σ2&Hl)|Hr].
      + eapply LiftStep; last done. exact Hl.
      + eapply LiftUbStep. split; first done. intros ? ? ?. eapply Hr. by do 2 eexists.
  Qed.

  Definition lang_to_mlang : mlanguage val :=
    Mlanguage language_mlanguage_mixin.

  Inductive lang_to_mlang_split_state : Λ.(state) → Λ.(state) → unit → Prop :=
    split_state_refl σ : lang_to_mlang_split_state σ σ ().
(*
  Global Program Instance lang_to_mlang_linkable : linkable lang_to_mlang Λ.(state) := {
    linking.private_state := unit;
    linking.split_state := lang_to_mlang_split_state;
  }.
  Next Obligation. intros *. inversion 1; inversion 1; by simplify_eq. Qed.
 *)
End ToMlang.
