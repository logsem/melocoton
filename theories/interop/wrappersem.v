From stdpp Require Import base strings list gmap.
From melocoton Require Import multirelations.
From melocoton.language Require Import language.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_toy_lang Require Import lang.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation.
From melocoton.interop Require Import basics linking wrapperstate prims.

Module Wrap.
Section wrappersem.

Local Notation prog := (gmap string prim).

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

Definition ectx := list (language.ectx ML_lang).

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

Definition comp_ectx (K1 K2 : ectx) : ectx :=
  K2 ++ K1.

Definition fill (K : ectx) (e : expr) : expr :=
  let 'WrE se k := e in
  WrE se (k ++ K).

Inductive state : Type :=
  (* state of the wrapper, which depends on whether we are yielding control to
     C or executing the wrapped ML program. *)
  | MLState (ρml : wrapstateML) (σ : store)
  | CState (ρc : wrapstateC) (mem : memory).

Local Notation private_state := wrapstateC.
Local Notation public_state := memory.

(* boundary states are ones in the [CState _ _] case *)
Inductive split_state : state → public_state → private_state → Prop :=
  | WrapSplitSt ρc mem :
    split_state (CState ρc mem) mem ρc.

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

Local Notation CLocV w := (C_lang.LitV (C_lang.LitLoc w)).
Local Notation CIntV x := (C_lang.LitV (C_lang.LitInt x)).

(* Semantics of wrapper primitives, that can be called from the wrapped C
   program as external functions. The callback primitive is treated separately
   and has a dedicated case in [head_step_mrel] below. *)
(* XXX naming issue: language interface prim_step vs this prim_step *)
Inductive c_prim_step :
  prim → list word → wrapstateC → memory →
  word → wrapstateC → memory → Prop
:=
  | PrimAllocS tgnum tg sz roots ρc privmem mem γ a mem' χC' ζC' θC' :
    tgnum = vblock_tag_as_int tg →
    (0 ≤ sz)%Z →
    dom roots = rootsC ρc →
    repr (θC ρc) roots privmem mem →
    χC ρc !! γ = None →
    χC' = {[ γ := LlocPrivate ]} ∪ (χC ρc) →
    ζC' = {[ γ := (Bvblock (Mut, (tg, List.repeat (Lint 0) (Z.to_nat sz)))) ]} ∪ (ζC ρc) →
    GC_correct ζC' θC' →
    repr θC' roots privmem mem' →
    roots_are_live θC' roots →
    θC' !! γ = Some a →
    c_prim_step
      Palloc [CIntV tgnum; CIntV sz] ρc mem
      (C_lang.LitV (C_lang.LitLoc a)) (WrapstateC χC' ζC' θC' (rootsC ρc)) mem'
  | PrimRegisterrootS a ρc mem rootsC' :
    a ∉ rootsC ρc →
    rootsC' = {[ a ]} ∪ rootsC ρc →
    c_prim_step
      Pregisterroot [CLocV a] ρc mem
      (CIntV 0) (WrapstateC (χC ρc) (ζC ρc) (θC ρc) rootsC') mem
  | PrimUnregisterrootS a ρc mem rootsC' :
    a ∈ rootsC ρc →
    rootsC' = rootsC ρc ∖ {[ a ]} →
    c_prim_step
      Punregisterroot [CLocV a] ρc mem
      (CIntV 0) (WrapstateC (χC ρc) (ζC ρc) (θC ρc) rootsC') mem
  | PrimModifyS w i w' ρc mem γ lv blk blk' ζC' :
    (0 ≤ i)%Z →
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some blk →
    repr_lval (θC ρc) lv w' →
    modify_block blk (Z.to_nat i) lv blk' →
    ζC' = <[ γ := blk' ]> (ζC ρc) →
    c_prim_step
      Pmodify [w; CIntV i; w'] ρc mem
      (CIntV 0) (WrapstateC (χC ρc) ζC' (θC ρc) (rootsC ρc)) mem
  | PrimReadfieldS w i ρc mem γ mut tag lvs lv w' :
    (0 ≤ i)%Z →
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some (Bvblock (mut, (tag, lvs))) →
    lvs !! (Z.to_nat i) = Some lv →
    repr_lval (θC ρc) lv w' →
    c_prim_step
      Preadfield [w; CIntV i] ρc mem
      w' ρc mem
  | PrimVal2intS ρc mem w x :
    repr_lval (θC ρc) (Lint x) w →
    c_prim_step
      Pval2int [w] ρc mem
      (CIntV x) ρc mem
  | PrimInt2valS ρc mem x w :
    repr_lval (θC ρc) (Lint x) w →
    c_prim_step
      Pint2val [CIntV x] ρc mem
      w ρc mem.

Inductive head_step_mrel (p : prog) : expr * state → (expr * state → Prop) → Prop :=
  (* Step in the underlying wrapped ML program. *)
  | StepMLS eml ρml σ eml' σ' X :
    (* We assume a closed ML expression: the "prog" collection of functions does
       not make too much sense at the ML level. Composition of ML "modules" is
       better modeled by composing expressions/evaluation contexts. *)
    language.language.prim_step ∅ eml σ eml' σ' [] →
    X (WrSE (ExprML eml'), MLState ρml σ') →
    head_step_mrel p (WrSE (ExprML eml), MLState ρml σ) X
  (* Administrative step for resolving a call to a primitive. *)
  | ExprCallS fn_name args prm ρ X :
    p !! fn_name = Some prm →
    X (WrSE (RunPrimitive prm args), ρ) →
    head_step_mrel p (WrSE (ExprCall fn_name args), ρ) X
  (* External call of the ML code to a C function. *)
  | MakeCallS fn_name vs ρml σ ws ρc mem eml k X :
    language.to_class eml = Some (commons.ExprCall fn_name vs) →
    p !! fn_name = None →
    ml_to_c vs ρml σ ws ρc mem →
    X (WrE (ExprCall fn_name ws) [k], CState ρc mem) →
    head_step_mrel p (WrSE (ExprML (language.fill k eml)), MLState ρml σ) X
  (* Given a C value (result of a C extcall), resume execution into ML code. *)
  | RetS w ki ρc mem X :
    c_to_ml w ρc mem (λ v ρml σ,
      X (WrSE (ExprML (language.fill ki (of_val v))), MLState ρml σ)) →
    head_step_mrel p (WrE (ExprV w) [ki], CState ρc mem) X
  (* Execution finishes with an ML value, translate it into a C value *)
  | ValS eml ρml σ v w ρc mem X :
    language.language.to_val eml = Some v →
    ml_to_c [v] ρml σ [w] ρc mem →
    X (WrSE (ExprV w), CState ρc mem) →
    head_step_mrel p (WrSE (ExprML eml), MLState ρml σ) X
  (* Call to a primitive (except for callback, see next case) *)
  | PrimS prm ws w ρc mem ρc' mem' X :
    c_prim_step prm ws ρc mem w ρc' mem' →
    X (WrSE (ExprV w), CState ρc' mem') →
    head_step_mrel p (WrSE (RunPrimitive prm ws), CState ρc mem) X
  (* Call to the callback primitive *)
  | CallbackS ρc mem γ w w' f x e X :
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some (Bclosure f x e) →
    c_to_ml w' ρc mem (λ v ρml σ,
      X (WrSE (ExprML (App (Val (RecV f x e)) (Val v))),
          MLState ρml σ)) →
    head_step_mrel p (WrSE (RunPrimitive Pcallback [w; w']), CState ρc mem) X.

Program Definition head_step (P : prog) : umrel (expr * state) :=
  {| mrel := head_step_mrel P |}.
Next Obligation.
  unfold upclosed. intros p [e ρ] X Y H HXY.
  destruct H; [
    eapply StepMLS
  | eapply ExprCallS
  | eapply MakeCallS
  | eapply RetS
  | eapply ValS
  | eapply PrimS
  | eapply CallbackS
  ]; unfold c_to_ml in *; naive_solver.
Qed.

Lemma mlanguage_mixin :
  MlanguageMixin (val:=word) of_class to_class [] comp_ectx fill
    apply_func head_step.
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
    cbn in Hsome. destruct (k ++ K) eqn:Heqk; first done.
    destruct e; simplify_eq; rewrite ?Heqk in Hsome;
      by eapply is_Some_None.
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

Canonical Structure wrap_lang : mlanguage word :=
  Mlanguage Wrap.mlanguage_mixin.

Global Program Instance wrap_linkable : linkable wrap_lang memory := {
  private_state := wrapstateC;
  split_state := Wrap.split_state;
}.
Next Obligation. intros *. inversion 1; inversion 1; by simplify_eq. Qed.

(* inversion lemmas *)

Lemma prim_head_step_WrSE pe se st X :
  mlanguage.prim_step pe (WrSE se, st) X →
  mlanguage.head_step pe (WrSE se, st) X.
Proof using.
  intros Hstep%prim_head_step; eauto.
  intros ? [? ?] HH ?. rewrite /fill /= /Wrap.fill /= in HH.
  inversion HH; simplify_list_eq.
  symmetry in HH; apply app_nil in HH. naive_solver.
Qed.

Lemma wrap_step_call_inv pe K fn_name vs ρml σ X :
  prim_step pe
    (WrSE (Wrap.ExprML (language.fill K (language.of_call ML_lang fn_name vs))),
     Wrap.MLState ρml σ) X →
  ∃ ws ρc mem,
     pe !! fn_name = None ∧
     Wrap.ml_to_c vs ρml σ ws ρc mem ∧
     X (Wrap.WrE (Wrap.ExprCall fn_name ws) [K], Wrap.CState ρc mem).
Proof using.
  intros Hstep.
  eapply prim_head_step_WrSE in Hstep.
  inversion Hstep; simplify_eq.
  { exfalso.
    eapply (@language.prim_step_call_inv _ ML_lang) in H3
      as (? & ? & ? & ? & ? & ? & ?); simplify_eq. }
  2: { exfalso. by rewrite to_val_fill_call in H2. }
  apply language.of_to_class in H2. subst eml.
  eapply (@language.call_call_in_ctx _ ML_lang) in H.
  rewrite (_: ∀ k, language.comp_ectx k language.empty_ectx = k) // in H.
  destruct H as (<- & <- & <-). do 3 eexists. split_and!; eauto.
Qed.

Lemma wrap_step_ret_inv pe K wret ρc mem X :
  prim_step pe (Wrap.WrE (Wrap.ExprV wret) [K], Wrap.CState ρc mem) X →
  Wrap.c_to_ml wret ρc mem (λ v ρml σ,
    X (WrSE (Wrap.ExprML (language.fill K (Val v))), Wrap.MLState ρml σ)).
Proof using.
  intros Hstep.
  eapply head_reducible_prim_step in Hstep.
  2: { exists (λ _, True). eapply Wrap.RetS, Wrap.c_to_ml_True. }
  inversion Hstep; by simplify_eq.
Qed.

Lemma wrap_step_expr_inv pe eml ρml σ X :
  reducible_no_threads ∅ eml σ →
  prim_step pe (WrSE (Wrap.ExprML eml), Wrap.MLState ρml σ) X →
  ∃ eml' σ',
    language.language.prim_step ∅ eml σ eml' σ' [] ∧
    X (WrSE (Wrap.ExprML eml'), Wrap.MLState ρml σ').
Proof using.
  intros Hred Hstep.
  eapply prim_head_step_WrSE in Hstep.
  inversion Hstep; simplify_eq.
  2: { exfalso; eapply reducible_call_is_in_prog.
       { by eapply language.language.reducible_no_threads_reducible. }
       { rewrite /language.to_call H2 //. }
       { set_solver. } }
  2: { apply language.language.of_to_val in H2; subst eml.
       apply language.language.reducible_no_threads_reducible in Hred.
       apply language.language.reducible_not_val in Hred. cbn in Hred; congruence. }
  do 2 eexists. split; eauto.
Qed.

Lemma wrap_step_callback_inv pe w w' ρc mem X :
  prim_step pe (WrSE (Wrap.RunPrimitive Pcallback [w; w']), Wrap.CState ρc mem) X →
  ∃ γ f x e,
    repr_lval (θC ρc) (Lloc γ) w ∧
    ζC ρc !! γ = Some (Bclosure f x e) ∧
    Wrap.c_to_ml w' ρc mem (λ v ρml σ,
      X (WrSE (Wrap.ExprML (App (Val (RecV f x e)) (Val v))), Wrap.MLState ρml σ)).
Proof using.
  intros Hstep.
  apply prim_head_step_WrSE in Hstep.
  inversion Hstep; simplify_eq.
  { match goal with HH: Wrap.c_prim_step Pcallback _ _ _ _ _ _ |- _ => inversion HH end. }
  repeat eexists; eauto.
Qed.
