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
  | LiftStep p e1 σ1 (X : _ → Prop) :
      to_val e1 = None →
      (reducible p e1 σ1 → ∃ e2 σ2, prim_step p e1 σ1 e2 σ2 ∧ X (e2, σ2)) →
      prim_step_mrel p (e1,σ1) X.

  Program Definition prim_step (p : prog) : umrel (expr_state) :=
    {| mrel := prim_step_mrel p |}.
  Next Obligation.
    intros p. intros [e1 σ1] X Y Hstep HXY. inversion Hstep; subst.
    - eapply (LiftStep p e1 σ1); first done.
      intros HH; specialize (H4 HH) as (?&?&?&?); eauto.
  Qed.

  Notation cont := Λ.(ectx).

  Definition is_call (e : Λ.(expr)) (s : string) (vs : list val) (C : cont) : Prop := 
    e = fill C (of_class Λ (ExprCall s vs)).

  Lemma language_mlanguage_mixin :
    MlanguageMixin (val:=val) (of_val Λ) to_val is_call (fill) (Λ.(comp_ectx)) (Λ.(apply_func)) prim_step.
  Proof using.
    constructor.
    - apply to_of_val.
    - apply of_to_val.
    - intros p v σ X H; inversion H; simplify_eq. rewrite to_of_val // in H3.
    - intros p e f vs C σ X ->. split; intros H.
      + inversion H; simplify_eq.
        * intros fn e2 ? ?. destruct H5 as (?&?&?&?).
          { do 2 eexists. eapply fill_prim_step, head_prim_step, call_head_step.
            by repeat eexists. }
          apply prim_step_call_inv in H2 as (er&fn'&HH1&HH2&->&->).
          simplify_map_eq. congruence.
      + econstructor; first by eapply to_val_fill_call.
        intros (? & ? & Hstep). pose proof Hstep as Hstep'.
        apply prim_step_call_inv in Hstep as (?&?&?&?&?&?); simplify_eq.
        do 2 eexists. split; eauto.
    - intros e [v Hv] f vs C ->. rewrite to_val_fill_call in Hv; done.
    - intros e C1 C2 s vv Heq. rewrite /is_call -fill_comp. by f_equal.
    - intros e C1 C2 s vv H1 H2. epose proof H2 as [(C'&HC')|[v Hv]]%call_in_ctx.
      + subst C2. eexists; split; last done.
        rewrite /is_call -fill_comp in H2.
        by eapply fill_inj.
      + rewrite -Hv /to_val to_of_class // in H1.
    - intros e C. apply fill_val.
    - intros e C1 C2. apply fill_comp.
    - by intros e s1 s2 f1 f2 C1 C2 -> (->&->&->)%call_call_in_ctx.
    - intros p C e σ X Hnv. inversion 1; simplify_eq.
      econstructor; first done. intros (? & ? & Hstep).
      destruct H5 as (?&?&?&?).
      { do 2 eexists. by eapply fill_prim_step. }
      apply fill_step_inv in H0 as (?&?&?); eauto; simplify_eq.
      do 2 eexists. split; eauto.
    - intros p e σ H. econstructor; eauto. intros (?&?&?). eauto.
  Qed.

  Definition lang_to_mlang : mlanguage val :=
    Mlanguage language_mlanguage_mixin.

  Inductive lang_to_mlang_split_state : Λ.(state) → Λ.(state) → unit → Prop :=
    split_state_refl σ : lang_to_mlang_split_state σ σ ().

  Global Program Instance lang_to_mlang_linkable : linkable lang_to_mlang Λ.(state) := {
    linking.private_state := unit;
    linking.split_state := lang_to_mlang_split_state;
  }.

End ToMlang.
