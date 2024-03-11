From stdpp Require Import relations strings gmap.
From transfinite.base_logic.lib Require Import own.
From iris.algebra Require Import ofe.
From iris.algebra Require Import auth excl excl_auth gmap.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.
From iris.bi Require Import weakestpre.
From melocoton Require Export named_props.

(** Classifying expressions into values and calls. *)

Inductive mixin_expr_class {val} :=
| ExprVal (v : val) : mixin_expr_class
| ExprCall (fn_name : string) (arg : list val) : mixin_expr_class.

(** Weakestpre notations *)

Notation "'WP' e 'at' s {{ Φ } }" := (wp s ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e 'at' s {{ v , Q } }" := (wp s ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/'  'at'  s '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.


Notation "'{{{' P } } } e 'at' s {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; ⊤ {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/'  'at'  s  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

Notation "'{{{' P } } } e 'at' s {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; ⊤ {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/'  'at'  s  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.



Notation "'{{{' P } } } e 'at' s {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; ⊤ {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e 'at' s {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; ⊤ {{ Φ }}) : stdpp_scope.


(** Protocols *)

Notation protocol val Σ :=
  (string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ).

Section Protocols.
Context {SI:indexT}.

(* ⊥ *)
Global Instance protocol_bottom val Σ : Bottom (protocol val Σ) :=
  (λ _ _ _, False%I).

(* ⊤ *)
Global Instance protocol_top val Σ : Top (protocol val Σ) :=
  (λ _ _ _, True%I).

(* Protocol subsumption. Ψ1 ⊑ Ψ2 means intuitively that
   Ψ1 is less permissive than Ψ2. *)
Definition proto_refines {val Σ} (Ψ1 Ψ2 : protocol val Σ) :=
  ∀ s vs Φ, Ψ1 s vs Φ -∗ Ψ2 s vs Φ.

Global Instance proto_refines_sqsubseteq val Σ : SqSubsetEq (protocol val Σ) :=
  proto_refines.

Lemma proto_refines_bot_l val Σ (Ψ : protocol val Σ) : ⊥ ⊑ Ψ.
Proof. by iIntros (? ? ?) "?". Qed.
Lemma proto_refines_top_r val Σ (Ψ : protocol val Σ) : Ψ ⊑ ⊤.
Proof. by iIntros (? ? ?) "?". Qed.

Global Instance proto_refines_reflexive val Σ :
  Reflexive (sqsubseteq : relation (protocol val Σ)).
Proof. by iIntros (Ψ ? ? ?). Qed.

Global Instance proto_refines_transitive val Σ :
  Transitive (sqsubseteq : relation (protocol val Σ)).
Proof.
  iIntros (Ψ Ψ' Ψ'' H1 H2 ? ? ?) "H".
  iApply H2. iApply H1. done.
Qed.

(* Restricting a protocol by excluding a set of function names. *)
Definition proto_except {val Σ}
  (Ψ : protocol val Σ) (except : gset string) : protocol val Σ
:=
  (λ s vs Φ, ⌜s ∉ except⌝ ∗ Ψ s vs Φ)%I.

Notation "Ψ 'except' fns" := (proto_except Ψ fns) (at level 10).

Lemma proto_except_refines val Σ (Ψ : protocol val Σ) (fns : gset string) :
  Ψ except fns ⊑ Ψ.
Proof. by iIntros (? ? ?) "[_ H]". Qed.

Lemma proto_except_mono_l {val Σ} (Ψ Ψ' : protocol val Σ) S :
  Ψ ⊑ Ψ' →
  Ψ except S ⊑ Ψ' except S.
Proof.
  iIntros (Hsub ? ? ?). rewrite /proto_except.
  iIntros "[% ?]". iSplit; first done. by iApply Hsub.
Qed.

Lemma proto_except_except {val Σ} (Ψ : protocol val Σ) S :
  Ψ except S ⊑ (Ψ except S) except S.
Proof.
  iIntros (? ? ?) "[% ?]". do 2 (iSplit; first done). done.
Qed.

Global Instance proto_except_proper {val Σ} :
  Proper ((@proto_refines val Σ) ==> eq ==> (@proto_refines val Σ)) proto_except.
Proof. intros ? ? ? ? ? ->. by apply proto_except_mono_l. Qed.

(* Restricting a protocol on a set of function names. *)
Definition proto_on {val Σ}
  (Ψ : protocol val Σ) (on : gset string) : protocol val Σ
:=
  (λ s vs Φ, ⌜s ∈ on⌝ ∗ Ψ s vs Φ)%I.

Notation "Ψ 'on' fns" := (proto_on Ψ fns) (at level 10).

Lemma proto_on_refines val Σ (Ψ : protocol val Σ) (fns : gset string) :
  Ψ on fns ⊑ Ψ.
Proof. by iIntros (? ? ?) "[_ H]". Qed.

Lemma proto_on_mono_l {val Σ} (Ψ Ψ' : protocol val Σ) S :
  Ψ ⊑ Ψ' →
  Ψ on S ⊑ Ψ' on S.
Proof.
  iIntros (Hsub ? ? ?). rewrite /proto_except.
  iIntros "[% ?]". iSplit; first done. by iApply Hsub.
Qed.

Global Instance proto_on_proper {val Σ} :
  Proper ((@proto_refines val Σ) ==> eq ==> (@proto_refines val Σ)) proto_on.
Proof. intros ? ? ? ? ? ->. by apply proto_on_mono_l. Qed.

(* We can also define a meet and join operation on protocols. *)

(* "Meet" operation on protocols. *)
Definition proto_meet {val Σ} (Ψ1 Ψ2 : protocol val Σ) : protocol val Σ :=
  (λ s vs Φ, Ψ1 s vs Φ ∧ Ψ2 s vs Φ)%I.

Global Instance proto_meet_meet val Σ : Meet (protocol val Σ) :=
  proto_meet.

Lemma proto_refines_meet_l val Σ (Ψ1 Ψ2 : protocol val Σ) : Ψ1 ⊓ Ψ2 ⊑ Ψ1.
Proof. iIntros (? ? ?) "H". by iApply bi.and_elim_l. Qed.

Lemma proto_refines_meet_r val Σ (Ψ1 Ψ2 : protocol val Σ) : Ψ1 ⊓ Ψ2 ⊑ Ψ2.
Proof. iIntros (? ? ?) "H". by iApply bi.and_elim_r. Qed.

Global Instance proto_meet_ne val Σ : NonExpansive2 (@proto_meet val Σ).
Proof.
  rewrite /proto_meet /= => n pp1 pp2 Hpp qq1 qq2 Hqq.
  repeat first [intros ?|f_equiv]. 1: apply Hpp. 1: apply Hqq.
Qed.

(* "Join" operation en protocols. *)
Definition proto_join {val Σ} (Ψ1 Ψ2 : protocol val Σ) : protocol val Σ :=
  (λ s vs Φ, Ψ1 s vs Φ ∨ Ψ2 s vs Φ)%I.

Global Instance proto_join_join val Σ : Join (protocol val Σ) :=
  proto_join.

Lemma proto_refines_join_l val Σ (Ψ1 Ψ2 : protocol val Σ) : Ψ1 ⊑ Ψ1 ⊔ Ψ2.
Proof. iIntros (? ? ?) "H". by iApply bi.or_intro_l. Qed.

Lemma proto_refines_join_r val Σ (Ψ1 Ψ2 : protocol val Σ) : Ψ2 ⊑ Ψ1 ⊔ Ψ2.
Proof. iIntros (? ? ?) "H". by iApply bi.or_intro_r. Qed.

Lemma proto_join_mono val Σ (Ψ1 Ψ1' Ψ2 Ψ2' : protocol val Σ) :
  Ψ1 ⊑ Ψ1' → Ψ2 ⊑ Ψ2' → Ψ1 ⊔ Ψ2 ⊑ Ψ1' ⊔ Ψ2'.
Proof.
  iIntros (Hre1 Hre2 ? ? ?) "H".
  iApply (bi.or_elim with "H"); iIntros "H".
  { iApply bi.or_intro_l. by iApply Hre1. }
  { iApply bi.or_intro_r. by iApply Hre2. }
Qed.

Global Instance proto_join_ne val Σ : NonExpansive2 (@proto_join val Σ).
Proof.
  rewrite /proto_join /= => n pp1 pp2 Hpp qq1 qq2 Hqq.
  repeat first [intros ?|f_equiv]. 1: apply Hpp. 1: apply Hqq.
Qed.

End Protocols.

(* Reexport notations *)
Notation "Ψ 'except' fns" := (proto_except Ψ fns) (at level 10).
Notation "Ψ 'on' fns" := (proto_on Ψ fns) (at level 10).

(* Notations for protocols *)

Notation "'!!' x .. y '{{' P } } f 'with' l {{ u .. v , 'RET' pat ; Q } }" :=
  (λ fn args Φ, "->" ∷ ⌜fn = f⌝ ∗ (∃ x, .. (∃ y, "->" ∷ ⌜args = l⌝ ∗ "ProtoPre" ∷ P ∗
    "Cont" ∷ ▷ (∀ u, .. (∀ v, Q -∗ Φ pat) ..)) ..))%I
  (at level 20, x closed binder, y closed binder, u closed binder, v closed binder,
   format "'[hv' !!  x  ..  y  {{  '[' P  ']' } }  '/  ' f  'with'  l  '/'  {{  '[' u  ..  v ,  RET  pat ;  '/' Q  ']' } } ']'").

Notation "'!!' '{{' P } } f 'with' l {{ u .. v , 'RET' pat ; Q } }" :=
  (λ fn args Φ, "->" ∷ ⌜fn = f⌝ ∗ ("->" ∷ ⌜args = l⌝ ∗ "ProtoPre" ∷ P ∗
    "Cont" ∷ ▷ (∀ u, .. (∀ v, Q -∗ Φ pat) ..)))%I
  (at level 20, u closed binder, v closed binder,
   format "'[hv' !!  {{  '[' P  ']' } }  '/  ' f  'with'  l  '/'  {{  '[' u  ..  v ,  RET  pat ;  '/' Q  ']' } } ']'").

Notation "'!!' x .. y '{{' P } } f 'with' l {{ 'RET' pat ; Q } }" :=
  (λ fn args Φ, "->" ∷ ⌜fn = f⌝ ∗ (∃ x, .. (∃ y, "->" ∷ ⌜args = l⌝ ∗ "ProtoPre" ∷ P ∗
    "Cont" ∷ ▷ (Q -∗ Φ pat)) ..))%I
  (at level 20, x closed binder, y closed binder,
   format "'[hv' !!  x  ..  y  {{  '[' P  ']' } }  '/  ' f  'with'  l  '/'  {{  '[' RET  pat ;  '/' Q  ']' } } ']'").

Notation "'!!' '{{' P } } f 'with' l {{ 'RET' pat ; Q } }" :=
  (λ fn args Φ, "->" ∷ ⌜fn = f⌝ ∗ ("->" ∷ ⌜args = l⌝ ∗ "ProtoPre" ∷ P ∗
    "Cont" ∷ ▷ (Q -∗ Φ pat)))%I
  (at level 20,
   format "'[hv' !!  {{  '[' P  ']' } }  '/  ' f  'with'  l  '/'  {{  '[' RET  pat ;  '/' Q  ']' } } ']'").

Ltac iNamedProto H := repeat (iNamed H); iNamed "ProtoPre".
