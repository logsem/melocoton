From Coq Require Import ssreflect.
From stdpp Require Import base strings gmap.
From melocoton.ml_lang Require Import lang.

Inductive prim :=
  | Palloc | Pregisterroot | Punregisterroot
  | Pmodify | Preadfield | Pval2int | Pint2val
  | Pallocforeign | Pwriteforeign | Preadforeign
  | Pcallback
  | Pmain (e : ML_lang.expr).

Inductive is_prim : string → prim → Prop :=
  | alloc_is_prim : is_prim "alloc" Palloc
  | registerroot_is_prim : is_prim "registerroot" Pregisterroot
  | unregisterroot_is_prim : is_prim "unregisterroot" Punregisterroot
  | modify_is_prim : is_prim "modify" Pmodify
  | readfield_is_prim : is_prim "readfield" Preadfield
  | val2int_is_prim : is_prim "val2int" Pval2int
  | int2val_is_prim : is_prim "int2val" Pint2val
  | allocforeign_is_prim : is_prim "alloc_foreign" Pallocforeign
  | writeforeign_is_prim : is_prim "write_foreign" Pwriteforeign
  | readforeign_is_prim : is_prim "read_foreign" Preadforeign
  | callback_is_prim : is_prim "callback" Pcallback
  | main_is_prim e : is_prim "main" (Pmain e).

Global Hint Constructors is_prim : core.

Global Instance prim_dec : EqDecision prim.
Proof.
  intros p1 p2.
  destruct p1; destruct p2;
    (try by left); try by right.
  destruct (decide (e = e0)); subst; first by left.
  right; congruence.
Qed.

Ltac inv_is_prim :=
  repeat match goal with
  | H : is_prim (String _ _) _ |- _ => inversion H; subst; clear H
  end.

Definition is_prim_name (s : string) : Prop :=
  ∃ p, is_prim s p.

Global Instance is_prim_name_dec s : Decision (is_prim_name s).
Proof.
  destruct (decide (s = "alloc")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "registerroot")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "unregisterroot")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "modify")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "readfield")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "val2int")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "int2val")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "alloc_foreign")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "write_foreign")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "read_foreign")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "callback")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "main")) as [->|]. left; eexists; constructor.
  right. by intros [? H]; inversion H.
  Unshelve. exact inhabitant.
Qed.

Definition prims_prog e : gmap string prim :=
  list_to_map [
      ("alloc", Palloc);
      ("registerroot", Pregisterroot);
      ("unregisterroot", Punregisterroot);
      ("modify", Pmodify);
      ("readfield", Preadfield);
      ("val2int", Pval2int);
      ("int2val", Pint2val);
      ("alloc_foreign", Pallocforeign);
      ("write_foreign", Pwriteforeign);
      ("read_foreign", Preadforeign);
      ("callback", Pcallback);
      ("main", Pmain e)
  ].

Lemma in_dom_prims_prog e s :
  s ∈ dom (prims_prog e) ↔ is_prim_name s.
Proof.
  rewrite /prims_prog.
  cbn. rewrite !dom_insert_L dom_empty_L. split.
  { rewrite !elem_of_union !elem_of_singleton. intros HH.
    destruct_or!; subst; eexists; try econstructor; [].
    exfalso. set_solver. }
  { intros [? Hprim]. inversion Hprim; set_solver. }
  Unshelve. { exfalso. set_solver. } { auto. }
Qed.

Lemma lookup_prims_prog_None e s :
  prims_prog e !! s = None ↔ ¬ is_prim_name s.
Proof. rewrite -not_elem_of_dom in_dom_prims_prog //. Qed.
