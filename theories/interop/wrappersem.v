From stdpp Require Import base strings list gmap.
From melocoton Require Import multirelations.
From melocoton.c_toy_lang Require Import melocoton.lang_instantiation.
From melocoton.ml_toy_lang Require Import melocoton.lang_instantiation.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.ml_toy_lang Require Import lang.
From melocoton.c_toy_lang Require Import lang.
From melocoton.interop Require Import basics linking wrapperstate prims.

Module Wrap.
Section wrappersem.

(* the wrapped C program accepts incoming function calls with ML values as
   arguments, and produces an ML value as output. *)
(* we don't have callbacks yet, so there's no "make an external call"
   expression: the wrapped C program can only be called into, not make "external
   calls" to ML yet. *)
Inductive expr : Type :=
  | ExprV (v : val)
  | ExprCall (fn_name : string) (args : list val)
  | RunFunction (fn : C_lang.function) (args : list val)
  | ExprC (ec : C_lang.expr).

Definition apply_func (fn : C_lang.function) (args : list val) : option expr :=
  Some (RunFunction fn args).

Definition of_class (c : mixin_expr_class val) : expr :=
  match c with
  | ExprVal v => ExprV v
  | commons.ExprCall fn_name args => ExprCall fn_name args
  end.

Definition to_class (e : expr) : option (mixin_expr_class val) :=
  match e with
  | ExprV v => Some (ExprVal v)
  | ExprCall fn_name args => Some (commons.ExprCall fn_name args)
  | _ => None
  end.

(* wrapper evaluation contexts should become more interesting when we add callbacks *)
Definition ectx : Type := unit.
Definition fill : ectx → expr → expr := λ _ e, e.

Inductive state : Type :=
  (* state of the wrapper, which depends on whether we are yielding control to
     ML or executing the wrapped C program. *)
  | MLState (ρml : wrapstateML) (σ : store)
  | CState (ρc : wrapstateC) (mem : memory).

Definition private_state : Type :=
  (* without callbacks we only need ML-related private state *)
  wrapstateML.

Local Notation public_state := store.

Inductive split_state : state → public_state → private_state → Prop :=
  | WrapSplitSt ρml σ :
    split_state (MLState ρml σ) σ ρml.

Local Notation prog := (gmap string C_lang.function).

Implicit Types X : expr * state → Prop.

Definition ml_to_c
  (vs : list val) (ρml : wrapstateML) (σ : store)
  (ws : list word) (ρc : wrapstateC) (mem : memory)
: Prop :=
  ∃ (ζσ ζnewimm : lstore) (lvs : list lval),
    (* Demonically get a new extended map χC. New bindings in χC correspond to
       new locations in the ML heap (e.g. allocated by ML). *)
    lloc_map_mono (χML ρml) (χC ρc) ∧
    (* The extended χC binds γs for all locations ℓ in σ; the ℓs that are mapped
       to [Some ...] in σ make up the domain of a map ζσ (whose contents are
       also chosen demonically). In other words, ζσ has exactly one block for
       each location in σ that is mapped to [Some ...]. *)
    is_store_blocks (χC ρc) σ ζσ ∧
    (* Representing the contents of the new ML heap may also require some new
       immutable blocks, which we represent in ζnewimm. The address of blocks
       in ζnewimm is LlocPrivate. *)
    is_private_blocks (χC ρc) ζnewimm ∧
    (* We take the new lstore ζC to be the old lstore + ζσ (the translation of σ
       into a lstore) + ζnewimm (new immutable blocks allocated from ML). These
       three parts must be disjoint. (ζσ and ζnewimm are disjoint by
       definition). [ζML ρml] may contain immutable blocks, mutable blocks
       allocated in C but not yet shared with the ML code, or mutable blocks
       exposed to ML but whose ownership was kept on the C side (and thus
       correspond to a [None] in σ). *)
    ζC ρc = ζML ρml ∪ ζσ ∪ ζnewimm ∧
    ζML ρml ##ₘ (ζσ ∪ ζnewimm) ∧
    (* Taken together, the contents of the new lloc_map χC and new lstore ζC
       must represent the contents of σ. (This further constraints the demonic
       choice of ζσ and ζnewimm.) *)
    is_store (χC ρc) (ζC ρc) σ ∧
    (* Demonically pick block-level values lvs that represent the arguments vs. *)
    Forall2 (is_val (χC ρc) (ζC ρc)) vs lvs ∧
    (* Demonically pick an addr_map θC satisfying the GC_correct property. *)
    GC_correct (ζC ρc) (θC ρc) ∧
    (* Rooted values must additionally be live in θC. *)
    roots_are_live (θC ρc) (rootsML ρml) ∧
    (* Pick C-level words that are live and represent the arguments of the
       function. (repr_lval on a location entails that it is live.) *)
    Forall2 (repr_lval (θC ρc)) lvs ws ∧
    (* Pick C memory (mem) that represents the roots (through θC) + the
       remaining private C memory. *)
    rootsC ρc = dom (rootsML ρml) ∧
    repr (θC ρc) (rootsML ρml) (privmemML ρml) mem.

Lemma ml_to_c_words_length vs ρml σ ws ρc mem :
  ml_to_c vs ρml σ ws ρc mem →
  length vs = length ws.
Proof.
  intros (?&?&?&HH). destruct_and! HH.
  repeat match goal with H : _ |- _ => apply Forall2_length in H end.
  lia.
Qed.

(* Note: I believe that the "freezing step" does properly forbid freezing a
   mutable block that has already been passed to the outside world --- but
   seeing why is not obvious. I expect it to work through the combination of:
   - sharing a logical block as a mutable value requires mapping its address to
     LlocPublic ℓ (cf is_store)
   - χ can only be updated to go from LlocPrivate to LlocPublic (cf expose_lloc)
     and otherwise grows monotonically
   - through is_store, blocks that have a public address must satisfy
     is_heap_elt and thus be mutable (cf is_heap_elt)
   - thus: trying to freeze a mutable block means breaking [is_store] unless
     we change back its address to private, which is not possible.
*)
Definition c_to_ml
  (w : word) (ρc : wrapstateC) (mem : memory)
  (X : val → wrapstateML → store → Prop)
: Prop :=
  ∀ σ lv v ζ ζσ χML ζML rootsML privmemML,
    (* Angelically allow freezing some blocks in (ζC ρc); the result is ζ.
       Freezing allows allocating a fresh block, mutating it, then changing
       it into an immutable block that represents an immutable ML value. *)
    freeze_lstore (ζC ρc) ζ →
    (* Angelically expose blocks by making their address public, picking a
       fresh ML location for them in the process. This makes it possible to
       expose new blocks to ML. *)
    expose_llocs (χC ρc) χML →
    (* Split the "current" lstore ζ into (ζML ρml) (the new lstore) and a
       part ζσ that is going to be converted into the ML store σ. *)
    ζ = ζML ∪ ζσ →
    ζML ##ₘ ζσ →
    (* Angelically pick an ML store σ where each location mapped to [Some
       ...] corresponds to a block in ζσ. *)
    is_store_blocks χML σ ζσ →
    (* The contents of ζ must represent the new σ. *)
    is_store χML ζ σ →
    (* Angelically pick a block-level value lv that corresponds to the
       C value w. *)
    repr_lval (θC ρc) lv w →
    (* Angelically pick an ML value v that correspond to the
       block-level value lv. *)
    is_val χML ζ v lv →
    (* Split the C memory mem into the memory for the roots and the rest
       ("private" C memory). *)
    repr (θC ρc) rootsML privmemML mem →
    dom rootsML = rootsC ρc →
    X v (WrapstateML χML ζML rootsML privmemML) σ.

Lemma c_to_ml_covariant_in_X w ρc mem (X X' : val → wrapstateML → store → Prop) :
  (∀ v ρml σ, X v ρml σ → X' v ρml σ) →
  c_to_ml w ρc mem X →
  c_to_ml w ρc mem X'.
Proof. intros HX HH. unfold c_to_ml; naive_solver. Qed.

Lemma c_to_ml_True w ρc mem : c_to_ml w ρc mem (λ _ _ _, True).
Proof. unfold c_to_ml; naive_solver. Qed.

(* Semantics of wrapper primitives, that can be called from the wrapped C
   program as external functions. *)
(* XXX naming issue: language interface prim_step vs this prim_step *)
Inductive c_prim_step :
  prim → list word → wrapstateC → memory →
  word → wrapstateC → memory → Prop
:=
  | PrimAllocS tgnum tg sz roots ρc privmem mem γ a mem' χC' ζC' θC' :
    tgnum = tag_as_int tg →
    (0 ≤ sz)%Z →
    dom roots = rootsC ρc →
    repr (θC ρc) roots privmem mem →
    χC ρc !! γ = None →
    χC' = {[ γ := LlocPrivate ]} ∪ (χC ρc) →
    ζC' = {[ γ := (Mut, (tg, List.repeat (Lint 0) (Z.to_nat sz))) ]} ∪ (ζC ρc) →
    GC_correct ζC' θC' →
    repr θC' roots privmem mem' →
    roots_are_live θC' roots →
    θC' !! γ = Some a →
    c_prim_step
      Palloc [LitV (LitInt tgnum); LitV (LitInt sz)] ρc mem
      (C_lang.LitV (C_lang.LitLoc a)) (WrapstateC χC' ζC' θC' (rootsC ρc)) mem'
  | PrimRegisterrootS a ρc mem rootsC' :
    a ∉ rootsC ρc →
    rootsC' = {[ a ]} ∪ rootsC ρc →
    c_prim_step
      Pregisterroot [LitV (LitLoc a)] ρc mem
      (LitV (LitInt 0)) (WrapstateC (χC ρc) (ζC ρc) (θC ρc) rootsC') mem
  | PrimUnregisterrootS a ρc mem rootsC' :
    a ∈ rootsC ρc →
    rootsC' = rootsC ρc ∖ {[ a ]} →
    c_prim_step
      Punregisterroot [LitV (LitLoc a)] ρc mem
      (LitV (LitInt 0)) (WrapstateC (χC ρc) (ζC ρc) (θC ρc) rootsC') mem
  | PrimModifyS w i w' ρc mem γ lv blk blk' ζC' :
    (0 ≤ i)%Z →
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some blk →
    repr_lval (θC ρc) lv w' →
    modify_block blk (Z.to_nat i) lv blk' →
    ζC' = <[ γ := blk' ]> (ζC ρc) →
    c_prim_step
      Pmodify [w; LitV (LitInt i); w'] ρc mem
      (LitV (LitInt 0)) (WrapstateC (χC ρc) ζC' (θC ρc) (rootsC ρc)) mem
  | PrimReadfieldS w i ρc mem γ mut tag lvs lv w' :
    (0 ≤ i)%Z →
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some (mut, (tag, lvs)) →
    lvs !! (Z.to_nat i) = Some lv →
    repr_lval (θC ρc) lv w' →
    c_prim_step
      Preadfield [w; LitV (LitInt i)] ρc mem
      w' ρc mem
  | PrimVal2intS ρc mem w x :
    repr_lval (θC ρc) (Lint x) w →
    c_prim_step
      Pval2int [w] ρc mem
      (LitV (LitInt x)) ρc mem
  | PrimInt2valS ρc mem x w :
    repr_lval (θC ρc) (Lint x) w →
    c_prim_step
      Pint2val [LitV (LitInt x)] ρc mem
      w ρc mem.

Inductive step_mrel (p : prog) : expr * state → (expr * state → Prop) → Prop :=
  (* Step in the underlying wrapped C program. *)
  | StepCS ec ρc mem ec' mem' X :
    (* TODO: make this head_step again when we add contexts *)
    language.language.prim_step p ec mem ec' mem' [] →
    X (ExprC ec', CState ρc mem') →
    step_mrel p (ExprC ec, CState ρc mem) X
  (* Administrative step for resolving a call from ML. *)
  | ExprCallS fn_name args fn ρ X :
    p !! fn_name = Some fn →
    X (RunFunction fn args, ρ) →
    step_mrel p (ExprCall fn_name args, ρ) X
  (* Incoming call of a C function from ML. *)
  | RunFunctionS fn vs ρml σ ws ρc mem ec X :
    (* Apply the C function; the result is a C expression ec. *)
    ml_to_c vs ρml σ ws ρc mem →
    C_lang.apply_function fn ws = Some ec →
    X (ExprC ec, CState ρc mem) →
    step_mrel p (RunFunction fn vs, MLState ρml σ) X
  (* Wrapped C function returning to ML. *)
  | RetS ec w ρc mem X :
    C_lang.to_val ec = Some w →
    c_to_ml w ρc mem (λ v ρml σ, X (ExprV v, MLState ρml σ)) →
    step_mrel p (ExprC ec, CState ρc mem) X
  (* call from C to a wrapper primitive *)
  | PrimS K ec prim_name prm ws w ρc mem ρc' mem' X :
    language.to_call ec = Some (prim_name, ws) →
    is_prim prim_name prm →
    c_prim_step prm ws ρc mem w ρc' mem' →
    X (ExprC (language.fill K (C_lang.of_val w)), CState ρc' mem') →
    step_mrel p (ExprC (language.fill K ec), CState ρc mem) X.

Program Definition step (P : prog) : umrel (expr * state) :=
  {| mrel := step_mrel P |}.
Next Obligation.
  unfold upclosed. intros p [e ρ] X Y H HXY.
  destruct H; [
    eapply StepCS
  | eapply ExprCallS
  | eapply RunFunctionS
  | eapply RetS
  | eapply PrimS
  ]; unfold c_to_ml in *; naive_solver.
Qed.

Lemma mlanguage_mixin :
  MlanguageMixin (val:=ML_lang.val) of_class to_class tt (λ _ _, tt) fill
    apply_func step.
Proof using.
  constructor.
  - intros c. destruct c; reflexivity.
  - intros e c. destruct e; cbn. all: inversion 1; cbn; auto.
  - intros p v st X. cbn. inversion 1; subst; naive_solver.
  - intros p fname v st X. split.
    + cbn. inversion 1; subst; naive_solver.
    + intros (fn & e & ? & Hfn & ?). cbn. unfold apply_func in Hfn.
      simplify_eq. econstructor; eauto.
  - intros ? [] ? ? ?. rewrite /fill /=. eauto.
  - eauto.
  - eauto.
  - intros [] ? ?. by unfold fill.
  - intros [] ? ?. eauto.
  - intros p [] [] ? ? ? ?. naive_solver.
  - intros ? []. naive_solver.
Qed.

End wrappersem.
End Wrap.

Canonical Structure wrap_lang : mlanguage val :=
  Mlanguage Wrap.mlanguage_mixin.

Global Program Instance wrap_linkable : linkable wrap_lang store := {
  private_state := Wrap.private_state;
  split_state := Wrap.split_state;
}.
Next Obligation. intros *. inversion 1; inversion 1; by simplify_eq. Qed.
