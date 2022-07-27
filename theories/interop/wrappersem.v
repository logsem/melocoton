From stdpp Require Import base strings list gmap.
From melocoton Require Import multirelations.
From melocoton.interop Require Import assums basics wrapperstate.

Inductive ml_or_c (A B: Type) : Type :=
  | ML : A → ml_or_c A B
  | C : B → ml_or_c A B.

Arguments ML {A B}.
Arguments C {A B}.

Section wrappersem.
Context {WPms: WrapperParameters}.

Definition stateW : Type :=
  (* state of the wrapper, which depends on whether we are yielding control to
     ML or executing the wrapped C program. *)
  ml_or_c
    (wrapstateML * store)
    (wrapstateC * memory).

Definition func : Type := string.

(* the wrapped C program accepts incoming function calls with ML values as
   arguments, and produces an ML value as output. *)
(* we don't have callbacks yet, so there's no "make an external call"
   expression: the wrapped C program can only be called into, not make "external
   calls" to ML yet. *)
Inductive exprW : Type :=
  | ValW (v : val)
  | RunningW (ec : exprC)
  | CallFunctionW (fn : func) (vs : list val).

(* wrapper evaluation contexts should become nontrivial when we add callbacks *)
Definition ectxW : Type := unit.
Definition fillW : ectxW → exprW → exprW := λ _ e, e.

Definition apply_func (fn : func) (vs : list val) : exprW :=
  CallFunctionW fn vs.

Definition wrapper_step (prog : progC) : mrel (exprW * stateW) (exprW * stateW) :=
  λ '(e, ρ) φ,
    (* step in the underlying wrapped C program *)
    (∀ ec ρc mem ec' mem',
       e = RunningW ec →
       ρ = C (ρc, mem) →
       head_step_C prog ec mem ec' mem' →
       φ (RunningW ec', C (ρc, mem')))
    ∨
    (* incoming call of a C function from ML *)
    (∀ fn vs ρml σ,
       e = CallFunctionW fn vs →
       ρ = ML (ρml, σ) →
       ∃ χ ζ privσ lvs,
         is_store χ ζ privσ σ ∧
         ML_change_lstore (χML ρml) (ζML ρml) ζ ∧
         ML_extends_lloc_map (ζML ρml) (χML ρml) χ ∧
         Forall2 (is_val χ ζ) vs lvs ∧
         ∀ ws mem ρc,
           (∀ γ (a:addr) v,
              (rootsML ρml) !! a = Some v →
              reachable ζ [v] γ →
              γ ∈ dom (gset lloc) (θC ρc)) →
           Forall2 (repr_lval (θC ρc)) lvs ws →
           repr (θC ρc) (rootsML ρml) (privmemML ρml) mem →
           χC ρc = χ →
           ζC ρc = ζ →
           rootsC ρc = dom (gset addr) (rootsML ρml) →
           privσC ρc = privσ →
           φ (RunningW (apply_func_C fn ws), C (ρc, mem)))
    ∨
    (* wrapped C function returning to ML *)
    (∀ ec w ρc mem,
       e = RunningW ec →
       to_val_C ec = Some w →
       ρ = C (ρc, mem) →
       ∃ σ lv v ρml,
         freeze_lstore (ζC ρc) (ζML ρml) ∧
         (χC ρc) ⊆ (χML ρml) ∧
         is_store (χML ρml) (ζML ρml) (privσC ρc) σ ∧
         repr_lval (θC ρc) lv w ∧
         is_val (χML ρml) (ζML ρml) v lv ∧
         dom (gset addr) (rootsML ρml) = rootsC ρc ∧
         repr (θC ρc) (rootsML ρml) (privmemML ρml) mem ∧
         φ (ValW v, ML (ρml, σ)))
    ∨
    (* call from C to the "alloc" primitive *)
    (∀ K ec tgnum tg sz ρc mem,
       e = RunningW (fillC K ec) →
       to_call_C ec = Some ("alloc", [tgnum; sz]) →
       ρ = C (ρc, mem) →
       tgnum = tag_as_int tg →
       (0 < sz)%Z →
       ∃ roots privmem,
         dom (gset addr) roots = rootsC ρc ∧
         repr (θC ρc) roots privmem mem ∧
         ∀ γ a mem' ρc',
           γ ∉ dom (gset lloc) (ζC ρc) →
           ζC ρc' = {[ γ := (Mut, tg, List.repeat (Lint 0) (Z.to_nat sz)) ]} ∪ (ζC ρc) →
           repr (θC ρc') roots privmem mem' →
           (θC ρc') !! γ = Some a →
           (∀ a v γ,
              roots !! a = Some v →
              reachable (ζC ρc) [v] γ →
              γ ∈ dom (gset lloc) (θC ρc')) →
           χC ρc' = χC ρc →
           rootsC ρc' = rootsC ρc →
           privσC ρc' = privσC ρc →
           φ (RunningW (fillC K (of_val_C a)), C (ρc', mem')))
    ∨
    (* call to "registerroot" *)
    (∀ K ec w ρc mem,
       e = RunningW (fillC K ec) →
       to_call_C ec = Some ("registerroot", [w]) →
       ρ = C (ρc, mem) →
       w ∉ rootsC ρc →
       ∀ ρc',
         rootsC ρc' = {[ w ]} ∪ rootsC ρc →
         χC ρc' = χC ρc →
         ζC ρc' = ζC ρc →
         θC ρc' = θC ρc →
         privσC ρc' = privσC ρc →
         φ (RunningW (fillC K (of_val_C 0%Z)), C (ρc', mem)))
    ∨
    (* call to "unregisterroot" *)
    (∀ K ec w ρc mem,
       e = RunningW (fillC K ec) →
       to_call_C ec = Some ("unregisterroot", [w]) →
       ρ = C (ρc, mem) →
       w ∈ rootsC ρc →
       ∀ ρc',
         rootsC ρc' = rootsC ρc ∖ {[ w ]} →
         χC ρc' = χC ρc →
         ζC ρc' = ζC ρc →
         θC ρc' = θC ρc →
         privσC ρc' = privσC ρc →
         φ (RunningW (fillC K (of_val_C 0%Z)), C (ρc', mem)))
    ∨
    (* call to "modify" *)
    (∀ K ec w i w' ρc mem γ lv blk blk',
       e = RunningW (fillC K ec) →
       to_call_C ec = Some ("modify", [w; i; w']) →
       ρ = C (ρc, mem) →
       (0 ≤ i)%Z →
       repr_lval (θC ρc) (Lloc γ) w →
       (ζC ρc) !! γ = Some blk →
       repr_lval (θC ρc) lv w' →
       modify_block blk (Z.to_nat i) lv blk' →
       ∀ ρc',
         χC ρc' = χC ρc →
         ζC ρc' = <[ γ := blk' ]> (ζC ρc) →
         θC ρc' = θC ρc →
         rootsC ρc' = rootsC ρc →
         privσC ρc' = privσC ρc →
         φ (RunningW (fillC K (of_val_C 0%Z)), C (ρc', mem)))
    ∨
    (* call to "readfield" *)
    (∀ K ec w i ρc mem γ mut tag lvs lv w',
       e = RunningW (fillC K ec) →
       to_call_C ec = Some ("readfield", [w; i]) →
       ρ = C (ρc, mem) →
       (0 ≤ i)%Z →
       repr_lval (θC ρc) (Lloc γ) w →
       (ζC ρc) !! γ = Some (mut, tag, lvs) →
       lvs !! (Z.to_nat i) = Some lv →
       repr_lval (θC ρc) lv w' →
       φ (RunningW (fillC K (of_val_C w')), C (ρc, mem)))
    ∨
    (* call to "val2int" *)
    (∀ K ec ρc mem w w',
       e = RunningW (fillC K ec) →
       to_call_C ec = Some ("val2int", [w]) →
       ρ = C (ρc, mem) →
       repr_lval (θC ρc) (Lint w') w →
       φ (RunningW (fillC K (of_val_C w')), (C (ρc, mem))))
    ∨
    (* call to "int2val" *)
    (∀ K ec ρc mem w w',
       e = RunningW (fillC K ec) →
       to_call_C ec = Some ("int2val", [w]) →
       ρ = C (ρc, mem) →
       repr_lval (θC ρc) (Lint w) w' →
       φ (RunningW (fillC K (of_val_C w')), (C (ρc, mem)))).

Program Definition wrapper_step_umrel (p : progC) : umrel (exprW * stateW) (exprW * stateW) :=
  {| rel := wrapper_step p |}.
Next Obligation.
  unfold upclosed. intros p [e ρ] φ ψ H Hφψ.
  destruct_or! H; naive_solver.
Qed.

End wrappersem.
