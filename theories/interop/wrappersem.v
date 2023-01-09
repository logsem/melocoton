From stdpp Require Import base strings list gmap.
From melocoton Require Import multirelations.
From melocoton.ml_toy_lang Require Import melocoton.lang_instantiation.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language.
From melocoton.ml_toy_lang Require Import lang.
From melocoton.c_toy_lang Require Import lang.
From melocoton.interop Require Import basics linking wrapperstate.

Module Wrap.
Section wrappersem.

(*
Inductive is_prim : string → prim → Prop :=
  | alloc_is_prim : is_prim "alloc" Palloc
  | registerroot_is_prim : is_prim "registerroot" Pregisterroot
  | unregisterroot_is_prim : is_prim "unregisterroot" Punregisterroot
  | modify_is_prim : is_prim "modify" Pmodify
  | readfield_is_prim : is_prim "readfield" Preadfield
  | val2int_is_prim : is_prim "val2int" Pval2int
  | int2val_is_prim : is_prim "int2val" Pint2val.

Instance is_prim_dec s : Decision (∃ p, is_prim s p).
Proof.
  destruct (decide (s = "alloc")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "registerroot")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "unregisterroot")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "modify")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "readfield")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "val2int")) as [->|]. left; eexists; constructor.
  destruct (decide (s = "int2val")) as [->|]. left; eexists; constructor.
  right. by intros [? H]; inversion H.
Qed.
*)

Inductive prim :=
  | Palloc | Pregisterroot | Punregisterroot
  | Pmodify | Preadfield | Pval2int | Pint2val.

Local Notation prog := (gmap string prim).

Definition prims_prog : prog :=
  list_to_map [
      ("alloc", Palloc);
      ("registerroot", Pregisterroot);
      ("unregisterroot", Punregisterroot);
      ("modify", Pmodify);
      ("readfield", Preadfield);
      ("val2int", Pval2int);
      ("int2val", Pint2val)
  ].

Inductive simple_expr : Type :=
  (* the wrapped module returns with a C value *)
  | ExprV (w : word)
  (* A call to a C function, which can be either:
     - an outgoing call by the wrapped code to an external C function;
     - an incoming call to a runtime primitive, which will be implemented by the wrapper
   *)
  | ExprCall (fn_name : string) (args : list word)
  (* Call to a runtime primitive *)
  | RunPrimitive (prm : prim) (args : list word)
  (* Execution of wrapped ML code *)
  | ExprML (eml : ML_lang.expr).

Definition ectx := language.ectx ML_lang.

Inductive expr : Type :=
  WrE (se: simple_expr) (k: ectx).

Notation WrSE se := (WrE se []).

Definition apply_func (prm : prim) (args : list word) : option expr :=
  Some (WrSE (RunPrimitive prm args)).

Definition of_class (c : mixin_expr_class word) : expr :=
  match c with
  | ExprVal w => WrSE (ExprV w)
  | commons.ExprCall fn_name args => WrSE (ExprCall fn_name args)
  end.

Definition to_class (e : expr) : option (mixin_expr_class word) :=
  match e with
  | WrSE (ExprV w) => Some (ExprVal w)
  | WrSE (ExprCall fn_name args) => Some (commons.ExprCall fn_name args)
  | _ => None
  end.

(* wrapper evaluation contexts should become more interesting when we add callbacks *)
Definition comp_ectx (K1 K2 : ectx) : ectx :=
  K2 ++ K1.

Definition fill (K : ectx) (e : expr) : expr :=
  let 'WrE se k := e in
  WrE se (k ++ K).

Inductive state : Type :=
  (* state of the wrapper, which depends on whether we are yielding control to
     ML or executing the wrapped C program. *)
  | MLState (ρml : wrapstateML) (σ : store)
  | CState (ρc : wrapstateC) (mem : memory).

Local Notation private_state := wrapstateC.
Local Notation public_state := memory.

Inductive split_state : state → public_state → private_state → Prop :=
  | WrapSplitSt ρc mem :
    split_state (CState ρc mem) mem ρc.

Implicit Types X : expr * state → Prop.

Inductive head_step_mrel (internalp : ml_program) (p : prog) : expr * state → (expr * state → Prop) → Prop :=
  (* Step in the underlying wrapped ML program. *)
  | StepCS eml ρml σ eml' σ' X :
    prim_step internalp eml σ eml' σ' [] →
    X (WrSE (ExprML eml'), MLState ρml σ') →
    head_step_mrel internalp p (WrSE (ExprML eml), MLState ρml σ) X
  (* Administrative step for resolving a call to a primitive. *)
  | ExprCallS fn_name args prm ρ X :
    p !! fn_name = Some prm →
    X (WrSE (RunPrimitive prm args), ρ) →
    head_step_mrel internalp p (WrSE (ExprCall fn_name args), ρ) X
  (* Outgoing call to a C function from ML. *)
  | MakeCallS fn_name vs ρml σ ζσ ζnewimm lvs ws eml k mem χC ζC θC X :
    language.to_class eml = Some (commons.ExprCall fn_name vs) →
    p !! fn_name = None →
    (* Demonically get a new extended map χC. New bindings in χC correspond to
       new locations allocated from ML. *)
    lloc_map_mono (χML ρml) χC →
    (* The extended χC binds γs for all locations ℓ in σ; the γs that are mapped
       to [Some ...] in σ make up the domain of a map ζσ (whose contents are
       also chosen demonically). In other words, here ζσ has exactly one block
       for each location in σ that is mapped to [Some ...]. *)
    is_store_blocks χC σ ζσ →
    (* We take the new lstore ζC to be the old lstore + ζσ (the translation of σ
       into a lstore) + ζimm (new immutable blocks allocated from ML). These
       three parts must be disjoint. [ζML ρml] will typically contain immutable
       blocks, mutable blocks allocated in C but not yet shared with the ML
       code, or mutable blocks whose ownership was kept on the C side (and thus
       correspond to a [None] in σ). *)
    ζC = ζML ρml ∪ ζσ ∪ ζnewimm →
    dom (ζML ρml) ## dom ζσ →
    dom (ζML ρml) ## dom ζnewimm →
    dom ζσ ## dom ζnewimm →
    (* Taken together, the contents of the new lloc_map χC and new lstore ζC
       must represent the contents of σ. (This further constraints the demonic
       choice of ζσ.) *)
    is_store χC ζC σ →
    (* Demonically pick block-level values lvs that represent the arguments vs. *)
    Forall2 (is_val χC ζC) vs lvs →
    (* Demonically pick an addr_map θC satisfying the GC_correct property. *)
    GC_correct ζC θC →
    (* Rooted values must additionally be live in θC. *)
    roots_are_live θC (rootsML ρml) →
    (* Pick C-level words that are live and represent the arguments of the
       function. (repr_lval on a location entails that it is live.) *)
    Forall2 (repr_lval θC) lvs ws →
    (* Pick C memory (mem) that represents the roots (through θC) + the
       remaining private C memory. *)
    repr θC (rootsML ρml) (privmemML ρml) mem →
    (* Step to an external call to C function fn_name with arguments ws *)
    X (WrE (ExprCall fn_name ws) k, CState (WrapstateC χC ζC θC (dom (rootsML ρml))) mem) →
    head_step_mrel internalp p (WrSE (ExprML (language.fill k eml)), MLState ρml σ) X
  (* Returning execution to ML with a C value. *)
  (* Note: I believe that the "freezing step" does properly forbid freezing a
     mutable block that has already been passed to the outside world --- but
     seeing why is not obvious. I expect it to work through the combination of:
     - sharing a logical block as a mutable value requires registering it in χ
     - χ only always grows monotonically
     - an immutable block cannot be represented as a ML-level heap-allocated value
       (see definition of is_store)
     - thus: trying to freeze a mutable block means that we would have to
       unregister it from χ in order for [is_store ...] to hold. But χ must only
       grow. Qed...
  *)
  | RetS w ki ρc mem X :
    (∀ σ lv v ζ ζσ χML ζML rootsML privmemML,
       (* Angelically allow freezing some blocks in (ζC ρc); the result is ζ.
          Freezing allows allocating a fresh block, mutating it, then changing
          it into an immutable block that represents an immutable ML value. *)
       freeze_lstore (ζC ρc) ζ →
       (* Angelically extend (χC ρc) into (χML ρml). This makes it possible to
          expose new blocks to ML. *)
       lloc_map_mono (χC ρc) χML →
       (* Split the "current" lstore ζ into (ζML ρml) (the new lstore) and a
          part ζσ that is going to be converted into the ML store σ. *)
       ζ = ζML ∪ ζσ →
       dom ζML ## dom ζσ →
       (* Angelically pick an ML store σ where each location mapped to [Some
          ...] corresponds to a block in ζσ. *)
       is_store_blocks χML σ ζσ →
       (* The contents of ζ must represent the new σ. *)
       is_store χML ζ σ →
       (* Angelically pick a block-level return value lv that corresponds to the
          C value w. *)
       repr_lval (θC ρc) lv w →
       (* Angelically pick a ML return value v that corresponds to the
          block-level value lv. *)
       is_val χML ζ v lv →
       (* Split the C memory mem into the memory for the roots and the rest
          ("private" C memory). *)
       repr (θC ρc) rootsML privmemML mem →
       dom rootsML = rootsC ρc →
       X (WrSE (ExprML (language.fill [ki] (ML_lang.of_val v))),
           MLState (WrapstateML χML ζML rootsML privmemML) σ)) →
    head_step_mrel internalp p (WrE (ExprV w) [ki], CState ρc mem) X
  (* call from C to the "alloc" primitive *)
  | PrimAllocS tgnum tg sz roots ρc privmem mem γ a mem' ζC' θC' X :
    tgnum = tag_as_int tg →
    (0 ≤ sz)%Z →
    dom roots = rootsC ρc →
    repr (θC ρc) roots privmem mem →
    γ ∉ dom (ζC ρc) →
    ζC' = {[ γ := (Mut, (tg, List.repeat (Lint 0) (Z.to_nat sz))) ]} ∪ (ζC ρc) →
    GC_correct ζC' θC' →
    repr θC' roots privmem mem' →
    roots_are_live θC' roots →
    θC' !! γ = Some a →
    X (WrSE (ExprV (LitV (LitLoc a))),
       CState (WrapstateC (χC ρc) ζC' θC' (rootsC ρc)) mem') →
    head_step_mrel internalp p
      (WrSE (RunPrimitive Palloc [LitV (LitInt tgnum); LitV (LitInt sz)]),
        CState ρc mem) X
  (* call to "registerroot" *)
  | PrimRegisterrootS a ρc mem rootsC' X :
    a ∉ rootsC ρc →
    rootsC' = {[ a ]} ∪ rootsC ρc →
    X (WrSE (ExprV (LitV (LitInt 0))),
       CState (WrapstateC (χC ρc) (ζC ρc) (θC ρc) rootsC') mem) →
    head_step_mrel internalp p
      (WrSE (RunPrimitive Pregisterroot [LitV (LitLoc a)]),
        CState ρc mem) X
  (* call to "unregisterroot" *)
  | PrimUnregisterrootS a ρc mem rootsC' X :
    a ∈ rootsC ρc →
    rootsC' = rootsC ρc ∖ {[ a ]} →
    X (WrSE (ExprV (LitV (LitInt 0))),
       CState (WrapstateC (χC ρc) (ζC ρc) (θC ρc) rootsC') mem) →
    head_step_mrel internalp p
      (WrSE (RunPrimitive Punregisterroot [LitV (LitLoc a)]),
        CState ρc mem) X
  (* call to "modify" *)
  | PrimModifyS w i w' ρc mem γ lv blk blk' ζC' X :
    (0 ≤ i)%Z →
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some blk →
    repr_lval (θC ρc) lv w' →
    modify_block blk (Z.to_nat i) lv blk' →
    ζC' = <[ γ := blk' ]> (ζC ρc) →
    X (WrSE (ExprV (LitV (LitInt 0))),
       CState (WrapstateC (χC ρc) ζC' (θC ρc) (rootsC ρc)) mem) →
    head_step_mrel internalp p
      (WrSE (RunPrimitive Pmodify [w; LitV (LitInt i); w']),
        CState ρc mem) X
  (* call to "readfield" *)
  | PrimReadfieldS w i ρc mem γ mut tag lvs lv w' X :
    (0 ≤ i)%Z →
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some (mut, (tag, lvs)) →
    lvs !! (Z.to_nat i) = Some lv →
    repr_lval (θC ρc) lv w' →
    X (WrSE (ExprV w'), CState ρc mem) →
    head_step_mrel internalp p
      (WrSE (RunPrimitive Preadfield [w; LitV (LitInt i)]),
        CState ρc mem) X
  (* call to "val2int" *)
  | PrimVal2intS ρc mem w x X :
    repr_lval (θC ρc) (Lint x) w →
    X (WrSE (ExprV (LitV (LitInt x))), CState ρc mem) →
    head_step_mrel internalp p
      (WrSE (RunPrimitive Pval2int [w]), CState ρc mem) X
  (* call to "int2val" *)
  | PrimInt2valS ρc mem x w X :
    repr_lval (θC ρc) (Lint x) w →
    X (WrSE (ExprV w), CState ρc mem) →
    head_step_mrel internalp p
      (WrSE (RunPrimitive Pint2val [LitV (LitInt x)]), CState ρc mem) X.

Program Definition head_step (IP : ml_program) (P : prog) : umrel (expr * state) :=
  {| mrel := head_step_mrel IP P |}.
Next Obligation.
  unfold upclosed. intros ip p [e ρ] X Y H HXY.
  destruct H; [
    eapply StepCS
  | eapply ExprCallS
  | eapply MakeCallS
  | eapply RetS
  | eapply PrimAllocS
  | eapply PrimRegisterrootS
  | eapply PrimUnregisterrootS
  | eapply PrimModifyS
  | eapply PrimReadfieldS
  | eapply PrimVal2intS
  | eapply PrimInt2valS
  ]; naive_solver.
Qed.

Lemma mlanguage_mixin ip :
  MlanguageMixin (val:=word) of_class to_class [] comp_ectx fill
    apply_func (head_step ip).
Proof using.
  constructor.
  - intros c. destruct c; reflexivity.
  - intros e c. destruct e as [e k]. destruct e; cbn.
    1,2: destruct k. all: inversion 1; cbn; auto.
  - intros p v st X. cbn. inversion 1; subst; naive_solver.
  - intros p fname v st X. split.
    + cbn. inversion 1; subst; naive_solver.
    + intros (prm & e & ? & Hprm & ?). cbn. unfold apply_func in Hprm.
      simplify_eq. econstructor; eauto.
  - intros ? ? [? ?] ? ?. rewrite /fill /=. intros. simplify_eq/=. eauto.
  - intros [e k]. rewrite /fill /empty_ectx app_nil_r //.
  - intros K1 K2 [e k]. rewrite /fill /comp_ectx app_assoc //.
  - intros K [e1 k1] [e2 k2]. cbn. inversion 1; subst.
    rewrite (app_inv_tail K k1 k2) //.
  - intros K [e k]. unfold fill. intros Hsome.
    destruct (decide (K = [])). by left. exfalso.
    assert (k ++ K ≠ []). { intros [? ?]%app_eq_nil. done. }
    cbn in Hsome. destruct (k ++ K) eqn:?.
    2: destruct e; by inversion Hsome. by destruct e.
  - intros p K' K_redex [e1' k1'] [e1_redex k1_redex] σ X.
    rewrite /fill. inversion 1; subst.
    destruct e1_redex; destruct k1' as [|u1' k1']; cbn; try by inversion 1.
    all: intros _; inversion 1; subst; unfold comp_ectx; cbn; eauto.
    naive_solver.
  - intros p K [e k] σ X. rewrite /fill. inversion 1; subst.
    all: try match goal with H : _ |- _ => symmetry in H; apply app_nil in H end.
    all: try match goal with H : _ |- _ => symmetry in H; apply app_singleton in H end.
    all: naive_solver.
Qed.

End wrappersem.
End Wrap.

Notation WrSE se := (Wrap.WrE se []).

Canonical Structure wrap_lang ip : mlanguage word :=
  Mlanguage (Wrap.mlanguage_mixin ip).

Global Program Instance wrap_linkable ip : linkable (wrap_lang ip) memory := {
  private_state := wrapstateC;
  split_state := Wrap.split_state;
}.
Next Obligation. intros *. inversion 1; inversion 1; by simplify_eq. Qed.
