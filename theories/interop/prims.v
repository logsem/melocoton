From Coq Require Import ssreflect.
From stdpp Require Import base strings gmap.
From melocoton.ml_lang Require Import lang.

Inductive prim :=
  | Palloc | Pregisterroot | Punregisterroot
  | Pmodify | Preadfield | Pval2int | Pint2val
  | Pisblock | Pread_tag | Plength
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
  | isblock_is_prim : is_prim "isblock" Pisblock
  | read_tag_is_prim : is_prim "read_tag" Pread_tag
  | length_is_prim : is_prim "length" Plength
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
  destruct (decide (s = "isblock")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "read_tag")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "length")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "alloc_foreign")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "write_foreign")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "read_foreign")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "callback")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "main")) as [->|]. left; eexists; constructor.
  right. by intros [? H]; inversion H.
  Unshelve. exact inhabitant.
Qed.

Definition wrap_prog e : gmap string prim :=
  list_to_map [
      ("alloc", Palloc);
      ("registerroot", Pregisterroot);
      ("unregisterroot", Punregisterroot);
      ("modify", Pmodify);
      ("readfield", Preadfield);
      ("val2int", Pval2int);
      ("int2val", Pint2val);
      ("isblock", Pisblock);
      ("read_tag", Pread_tag);
      ("length", Plength);
      ("alloc_foreign", Pallocforeign);
      ("write_foreign", Pwriteforeign);
      ("read_foreign", Preadforeign);
      ("callback", Pcallback);
      ("main", Pmain e)
  ].

Definition prim_names : gset string :=
  dom (wrap_prog inhabitant).

Lemma dom_wrap_prog e :
  dom (wrap_prog e) = prim_names.
Proof.
  rewrite /prim_names /wrap_prog.
  rewrite !dom_list_to_map_L //.
Qed.

Lemma elem_of_prim_names s :
  s ∈ prim_names ↔ is_prim_name s.
Proof.
  rewrite /prim_names /wrap_prog.
  cbn. rewrite !dom_insert_L dom_empty_L. split.
  { rewrite !elem_of_union !elem_of_singleton. intros HH.
    destruct_or!; subst; eexists; try econstructor; [].
    exfalso. set_solver. }
  { intros [? Hprim]. inversion Hprim; set_solver. }
  Unshelve. { exfalso. set_solver. } { apply inhabitant. }
Qed.

Lemma not_elem_of_prim_names s :
  s ∉ prim_names ↔ ¬ is_prim_name s.
Proof. rewrite elem_of_prim_names //. Qed.

Lemma lookup_wrap_prog_except_main e s p :
  s ≠ "main" →
  wrap_prog e !! s = Some p ↔ is_prim s p.
Proof.
  intros Hnmain.
  rewrite /wrap_prog. cbn. split.
  { intros HH. rewrite !lookup_insert_Some in HH.
    repeat (destruct_or!; destruct_and!); simplify_eq; constructor. }
  { inversion 1; simplify_eq; try reflexivity. }
Qed.
