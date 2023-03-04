From Coq Require Import ssreflect.
From stdpp Require Import base strings gmap.

Inductive prim :=
  | Palloc | Pregisterroot | Punregisterroot
  | Pmodify | Preadfield | Pval2int | Pint2val
  | Pcallback.

Inductive is_prim : string → prim → Prop :=
  | alloc_is_prim : is_prim "alloc" Palloc
  | registerroot_is_prim : is_prim "registerroot" Pregisterroot
  | unregisterroot_is_prim : is_prim "unregisterroot" Punregisterroot
  | modify_is_prim : is_prim "modify" Pmodify
  | readfield_is_prim : is_prim "readfield" Preadfield
  | val2int_is_prim : is_prim "val2int" Pval2int
  | int2val_is_prim : is_prim "int2val" Pint2val
  | callback_is_prim : is_prim "callback" Pcallback.

Global Hint Constructors is_prim : core.

Global Instance prim_dec : EqDecision prim.
Proof.
  intros p1 p2.
  destruct p1; destruct p2;
    (try by left); try by right.
Qed.

Ltac inv_is_prim :=
  repeat match goal with
  | H : is_prim (String _ _) _ |- _ => inversion H; subst; clear H
  end.

Definition is_prim_name (s : string) : Prop :=
  ∃ p, is_prim s p.

Lemma is_prim_inj s p1 p2 :
  is_prim s p1 →
  is_prim s p2 →
  p1 = p2.
Proof. inversion 1; inversion 1; by simplify_eq. Qed.

Ltac is_prim_inj :=
  repeat match goal with
  | H1 : is_prim ?s ?p1, H2 : is_prim ?s ?p2 |- _ =>
      pose proof (is_prim_inj _ _ _ H1 H2); subst p2; clear H2
  end.

Global Instance is_prim_name_dec s : Decision (is_prim_name s).
Proof.
  destruct (decide (s = "alloc")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "registerroot")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "unregisterroot")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "modify")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "readfield")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "val2int")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "int2val")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "callback")) as [->|]. left; eexists; constructor.
  right. by intros [? H]; inversion H.
Qed.

Definition prims_prog : gmap string prim :=
  list_to_map [
      ("alloc", Palloc);
      ("registerroot", Pregisterroot);
      ("unregisterroot", Punregisterroot);
      ("modify", Pmodify);
      ("readfield", Preadfield);
      ("val2int", Pval2int);
      ("int2val", Pint2val);
      ("callback", Pcallback)
  ].

Lemma lookup_prims_prog_Some s p :
  prims_prog !! s = Some p ↔ is_prim s p.
Proof.
  rewrite /prims_prog /=. split.
  { intros H.
    destruct (decide (s = "alloc")) as [->|]; simplify_map_eq; first constructor.
    destruct (decide (s = "registerroot")) as [->|]; simplify_map_eq; first constructor.
    destruct (decide (s = "unregisterroot")) as [->|]; simplify_map_eq; first constructor.
    destruct (decide (s = "modify")) as [->|]; simplify_map_eq; first constructor.
    destruct (decide (s = "readfield")) as [->|]; simplify_map_eq; first constructor.
    destruct (decide (s = "val2int")) as [->|]; simplify_map_eq; first constructor.
    destruct (decide (s = "int2val")) as [->|]; simplify_map_eq; first constructor.
    destruct (decide (s = "callback")) as [->|]; simplify_map_eq; first constructor.
  }
  { inversion 1; by simplify_map_eq. }
Qed.

Lemma lookup_prims_prog_None s :
  prims_prog !! s = None ↔ ¬ is_prim_name s.
Proof.
  destruct (decide (is_prim_name s)) as [[p Hp]|].
  { destruct (prims_prog !! s) eqn:HH; split; intros; try done.
    { exfalso; firstorder. }
    { apply lookup_prims_prog_Some in Hp. congruence. } }
  { destruct (prims_prog !! s) eqn:HH; split; intros; try done.
    { apply lookup_prims_prog_Some in HH. firstorder. } }
Qed.
