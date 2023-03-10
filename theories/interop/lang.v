From stdpp Require Import base strings list gmap.
From melocoton Require Import multirelations.
From melocoton.language Require Import language.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_interface Require Import defs.
From melocoton.ml_lang Require Import lang lang_instantiation.
From melocoton.interop Require Import basics basics_constructions state prims.

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

Definition cont := list (language.ectx ML_lang).

Inductive expr : Type :=
  WrE (se: simple_expr) (k: cont).

Definition apply_func (prm : prim) (args : list word) : option expr :=
  Some (WrE (RunPrimitive prm args) []).

Definition of_val (w : word) : expr := WrE (ExprV w) [].

Definition to_val (e : expr) : option word :=
  match e with
  | WrE (ExprV w) [] => Some w
  | _ => None
  end.

Definition is_call e f vs C := e = WrE (ExprCall f vs) C.

Definition comp_cont (K1 K2 : cont) : cont :=
  K2 ++ K1.

Definition resume_with (K : cont) (e : expr) : expr :=
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

Hint Resolve c_to_ml_True : core.

Local Notation CLocV w := (C_intf.LitV (C_intf.LitLoc w)).
Local Notation CIntV x := (C_intf.LitV (C_intf.LitInt x)).

(* Semantics of wrapper primitives, that can be called from the wrapped C
   program as external functions. The callback primitive is treated separately
   and has a dedicated case in [head_step_mrel] below. *)
(* XXX naming issue: language interface prim_step vs this prim_step *)
Implicit Types Y : word → wrapstateC → memory → Prop.
Inductive c_prim_step :
  prim → list word → wrapstateC → memory →
  (word → wrapstateC → memory → Prop) → Prop
:=
  | PrimAllocS ls ρc mem Y :
    (∀ tgnum sz tg roots privmem,
       ls = [CIntV tgnum; CIntV sz] →
       tgnum = vblock_tag_as_int tg →
       (0 ≤ sz)%Z →
       dom roots = rootsC ρc →
       repr (θC ρc) roots privmem mem →
       GC_correct (ζC ρc) (θC ρc) →
       roots_are_live (θC ρc) roots →
     ∃ γ χC' ζC' θC' a mem',
         χC ρc !! γ = None ∧
         χC' = <[ γ := LlocPrivate ]> (χC ρc) ∧
         ζC' = <[ γ := (Bvblock (Mut, (tg, List.repeat (Lint 0) (Z.to_nat sz)))) ]> (ζC ρc) ∧
         GC_correct ζC' θC' ∧
         repr θC' roots privmem mem' ∧
         roots_are_live θC' roots ∧
         θC' !! γ = Some a ∧
         Y (C_intf.LitV (C_intf.LitLoc a)) (WrapstateC χC' ζC' θC' (rootsC ρc)) mem') →
    c_prim_step Palloc ls ρc mem Y
  | PrimRegisterrootS ls ρc mem Y :
    (∀ a rootsC',
       ls = [CLocV a] →
       a ∉ rootsC ρc →
       rootsC' = {[ a ]} ∪ rootsC ρc →
       Y (CIntV 0) (WrapstateC (χC ρc) (ζC ρc) (θC ρc) rootsC') mem) →
    c_prim_step Pregisterroot ls ρc mem Y
  | PrimUnregisterrootS ls ρc mem Y :
    (∀ a rootsC',
       ls = [CLocV a] →
       a ∈ rootsC ρc →
       rootsC' = rootsC ρc ∖ {[ a ]} →
       Y (CIntV 0) (WrapstateC (χC ρc) (ζC ρc) (θC ρc) rootsC') mem) →
    c_prim_step Punregisterroot ls ρc mem Y
  | PrimModifyS ls ρc mem Y :
    (* blk' is uniquely chosen *)
    (∀ w i w' γ lv blk ζC' blk',
       ls = [w; CIntV i; w'] →
       (0 ≤ i)%Z →
       repr_lval (θC ρc) (Lloc γ) w →
       (ζC ρc) !! γ = Some blk →
       repr_lval (θC ρc) lv w' →
       modify_block blk (Z.to_nat i) lv blk' →
       ζC' = <[ γ := blk' ]> (ζC ρc) →
       Y (CIntV 0) (WrapstateC (χC ρc) ζC' (θC ρc) (rootsC ρc)) mem) →
    c_prim_step Pmodify ls ρc mem Y
  | PrimReadfieldS ls ρc mem Y :
    (∀ w i γ mut tag lvs lv w',
       ls = [w; CIntV i] →
       (0 ≤ i)%Z →
       repr_lval (θC ρc) (Lloc γ) w →
       (ζC ρc) !! γ = Some (Bvblock (mut, (tag, lvs))) →
       lvs !! (Z.to_nat i) = Some lv →
       repr_lval (θC ρc) lv w' →
       Y w' ρc mem) →
    c_prim_step Preadfield ls ρc mem Y
  | PrimVal2intS ls ρc mem Y :
    (∀ w x,
       ls = [w] →
       repr_lval (θC ρc) (Lint x) w →
       Y (CIntV x) ρc mem) →
    c_prim_step Pval2int ls ρc mem Y
  | PrimInt2valS ls ρc mem Y :
    (∀ x w,
       ls = [CIntV x] →
       repr_lval (θC ρc) (Lint x) w →
       Y w ρc mem) →
    c_prim_step Pint2val ls ρc mem Y
  | PrimAllocForeignS ls ρc mem Y :
    (∀ aforeign roots privmem,
       ls = [CLocV aforeign] →
       dom roots = rootsC ρc →
       GC_correct (ζC ρc) (θC ρc) →
       repr (θC ρc) roots privmem mem →
       roots_are_live (θC ρc) roots →
       ∃ γ id χC' ζC' θC' a mem',
         χC ρc !! γ = None ∧
         (∀ γ' id', χC ρc !! γ' = Some (LlocForeign id') → id' ≠ id) ∧
         χC' = <[ γ := LlocForeign id ]> (χC ρc) ∧
         ζC' = <[ γ := Bforeign aforeign ]> (ζC ρc) ∧
         GC_correct ζC' θC' ∧
         repr θC' roots privmem mem' ∧
         roots_are_live θC' roots ∧
         θC' !! γ = Some a ∧
         Y (CLocV a) (WrapstateC χC' ζC' θC' (rootsC ρc)) mem') →
    c_prim_step Pallocforeign ls ρc mem Y
  | PrimReadForeignS ls ρc mem Y :
    (∀ w γ aforeign,
       ls = [w] →
       repr_lval (θC ρc) (Lloc γ) w →
       (ζC ρc) !! γ = Some (Bforeign aforeign) →
       Y (CLocV aforeign) ρc mem) →
    c_prim_step Preadforeign ls ρc mem Y
  | PrimWriteForeignS ls ρc mem Y :
    (∀ w γ aforeign aforeign' ζC',
       ls = [w; CLocV aforeign'] →
       repr_lval (θC ρc) (Lloc γ) w →
       (ζC ρc) !! γ = Some (Bforeign aforeign) →
       ζC' = <[ γ := Bforeign aforeign' ]> (ζC ρc) →
       Y (CIntV 0) (WrapstateC (χC ρc) ζC' (θC ρc) (rootsC ρc)) mem) →
    c_prim_step Pwriteforeign ls ρc mem Y.

Lemma c_prim_step_total p ws ρc mem : p ≠ Pcallback → c_prim_step p ws ρc mem (λ _ _ _, True).
Proof.
  (* TODO: refactor *)
  intros H; destruct p; try done.
  all: econstructor; try by eauto.

  (* alloc *)
  { intros tgnum sz tg roots privmem
      -> -> Hsz Hroots [pubmem Hrepr2] [Hθinj HGCOK] Hrootslive.
    pose (tg, repeat (Lint 0) (Z.to_nat sz)) as blk.
    pose ((map_to_set (fun a b => b) (θC ρc) : gset loc)) as fresh_not_θ_cod.
    pose (dom (χC ρc) ∪ dom (θC ρc) ∪ dom (ζC ρc : gmap _ _)) as fresh_src.
    pose (fresh fresh_src) as γ.
    pose (fresh fresh_not_θ_cod) as w.
    pose proof (is_fresh fresh_src) as ((HFχ&HFθ)%not_elem_of_union&HFζ)%not_elem_of_union.
    exists
      γ,
      (<[ γ := LlocPrivate ]> (χC ρc)),
      (<[ γ := Bvblock (Mut, blk) ]> (ζC ρc)),
      (<[ γ := w ]> (θC ρc)),
      w,
      mem. split_and!; try done.
    - by eapply not_elem_of_dom.
    - split.
      + eapply gmap_inj_extend; try done.
        intros k' v' Hin <-. eapply (is_fresh fresh_not_θ_cod).
        eapply elem_of_map_to_set. do 2 eexists; repeat split. apply Hin.
      + intros γ1 blk1 γ' H1 [(->&HH)|(HH1&HH2)]%lookup_insert_Some H3.
        1: subst blk1; by apply lval_in_vblock, elem_of_list_In, repeat_spec in H3.
        rewrite dom_insert_L in H1.
        apply elem_of_union in H1 as [->%elem_of_singleton|H1]; first done.
        rewrite dom_insert_L; eapply elem_of_union_r. eapply HGCOK; done.
    - eapply repr_mono; last by eexists.
      eapply insert_subseteq, not_elem_of_dom, HFθ.
    - intros l γ1 Hin. rewrite dom_insert_L; eapply elem_of_union_r.
      by eapply Hrootslive.
    - apply lookup_insert. }

  (* alloc_foreign *)
  { intros aforeign roots privmem
      -> Hroots [Hθinj HGCOK] [pubmem Hrepr2] Hrootslive.
    pose ((map_to_set (fun a b => b) (θC ρc) : gset loc)) as fresh_not_θ_cod.
    pose (dom (χC ρc) ∪ dom (θC ρc) ∪ dom (ζC ρc : gmap _ _)) as fresh_src.
    pose (fresh fresh_src) as γ.
    pose (fresh fresh_not_θ_cod) as w.
    pose proof (is_fresh fresh_src) as ((HFχ&HFθ)%not_elem_of_union&HFζ)%not_elem_of_union.
    pose (map_to_set (fun a b => b) (lloc_map_foreign (χC ρc)) : gset nat)
      as χforeignids.
    pose (fresh χforeignids) as id.

    exists
      γ, id,
      (<[ γ := LlocForeign id ]> (χC ρc)),
      (<[ γ := Bforeign aforeign ]> (ζC ρc)),
      (<[ γ := w ]> (θC ρc)),
      w,
      mem. split_and!; try done.
    - by eapply not_elem_of_dom.
    - intros * ?%lloc_map_foreign_lookup_Some ->.
      apply (is_fresh χforeignids). rewrite -/id.
      rewrite elem_of_map_to_set. eauto.
    - split.
      + eapply gmap_inj_extend; try done.
        intros k' v' Hin <-. eapply (is_fresh fresh_not_θ_cod).
        eapply elem_of_map_to_set. do 2 eexists; repeat split. apply Hin.
      + intros γ1 blk1 γ' H1 [(->&HH)|(HH1&HH2)]%lookup_insert_Some H3.
        1: subst; by inversion H3.
        rewrite dom_insert_L in H1.
        apply elem_of_union in H1 as [->%elem_of_singleton|H1]; first done.
        rewrite dom_insert_L; eapply elem_of_union_r. eapply HGCOK; done.
    - eapply repr_mono; last by eexists.
      eapply insert_subseteq, not_elem_of_dom, HFθ.
    - intros l γ1 Hin. rewrite dom_insert_L; eapply elem_of_union_r.
      by eapply Hrootslive.
    - apply lookup_insert. }
Qed.

Hint Resolve c_prim_step_total : core.

Local Definition is_ML_call (e : ML_lang.expr) fn_name vs K :=
  e = language.fill K (of_class _ (commons.ExprCall fn_name vs)).

Inductive prim_step_mrel (p : prog) : expr * state → (expr * state → Prop) → Prop :=
  | StepMLS eml ρ K X :
    (* Step in the underlying wrapped ML program. *)
    (∀ ρml σ,
       ρ = MLState ρml σ →
       language.language.to_val eml = None →
       (¬ ∃ K fn_name arg, is_ML_call eml fn_name arg K) →
       reducible ∅ eml σ →
       ∃ eml' σ',
         (* We assume a closed ML expression: the "prog" collection of functions does
            not make too much sense at the ML level. Composition of ML "modules" is
            better modeled by composing expressions/evaluation contexts. *)
         language.language.prim_step ∅ eml σ eml' σ' ∧
         X (WrE (ExprML eml') K, MLState ρml σ')) →

    (* External call of the ML code to a C function. *)
    (∀ ρml σ fn_name vs k,
       ρ = MLState ρml σ →
       is_ML_call eml fn_name vs k →
       p !! fn_name = None →
       (∃ ws ρc mem, ml_to_c vs ρml σ ws ρc mem) →
       ∃ ws ρc mem,
         ml_to_c vs ρml σ ws ρc mem ∧
         X (WrE (ExprCall fn_name ws) (k::K), CState ρc mem)) →

    (* Execution finishes with an ML value, translate it into a C value *)
    (∀ ρml σ v,
       ρ = MLState ρml σ →
       language.language.to_val eml = Some v →
       (∃ w ρc mem, ml_to_c [v] ρml σ [w] ρc mem) →
       ∃ w ρc mem,
         ml_to_c [v] ρml σ [w] ρc mem ∧
         X (WrE (ExprV w) K, CState ρc mem)) →

    prim_step_mrel p (WrE (ExprML eml) K, ρ) X

  (* Given a C value (result of a C extcall), resume execution into ML code. *)
  | RetS w ki ρ K X :
    (∀ ρc mem,
       ρ = CState ρc mem →
       c_to_ml w ρc mem (λ v ρml σ,
         X (WrE (ExprML (language.fill ki (ML_lang.of_val v))) K, MLState ρml σ))) →
    prim_step_mrel p (WrE (ExprV w) (ki::K), ρ) X

  (* Administrative step for resolving a call to a primitive. *)
  | ExprCallS fn_name args ρ K X :
    (∀ prm,
       p !! fn_name = Some prm →
       X (WrE (RunPrimitive prm args) K, ρ)) →
    prim_step_mrel p (WrE (ExprCall fn_name args) K, ρ) X

  (* Call to a primitive (except for callback, see next case) *)
  | PrimS prm ws ρ K X :
    (∀ ρc mem,
       ρ = CState ρc mem →
       c_prim_step prm ws ρc mem (λ w ρc' mem',
         X (WrE (ExprV w) K, CState ρc' mem'))) →
    prim_step_mrel p (WrE (RunPrimitive prm ws) K, ρ) X

  (* Call to the callback primitive *)
  | CallbackS ls ρ K X :
    (∀ w w' ρc mem γ f x e,
       ls = [w; w'] →
       ρ = CState ρc mem →
       repr_lval (θC ρc) (Lloc γ) w →
       (ζC ρc) !! γ = Some (Bclosure f x e) →
       c_to_ml w' ρc mem (λ v ρml σ,
         X (WrE (ExprML (App (Val (RecV f x e)) (Val v))) K,
             MLState ρml σ))) →
    prim_step_mrel p (WrE (RunPrimitive Pcallback ls) K, ρ) X.

Program Definition prim_step (P : prog) : umrel (expr * state) :=
  {| mrel := prim_step_mrel P |}.
Next Obligation.
  unfold upclosed. intros p [e ρ] X Y H HXY.
  destruct H; [
    eapply StepMLS
  | eapply RetS
  | eapply ExprCallS
  | eapply PrimS
  | eapply CallbackS
  ]; unfold c_to_ml in *; eauto; [naive_solver..|].
  { (* PrimS case: need to perform inversion on c_prim_step *)
    intros * ->. specialize (H _ _ eq_refl).
    inversion H; econstructor; eauto; naive_solver. }
Qed.

Lemma mlanguage_mixin :
  MlanguageMixin (val:=word) of_val to_val is_call resume_with
    comp_cont apply_func prim_step.
Proof using.
  constructor.
  - intros c. destruct c; reflexivity.
  - intros e c. destruct e as [e k]. destruct e; cbn.
    1,2: destruct k. all: inversion 1; cbn; auto.
  - intros p v st X. cbn. inversion 1; subst; naive_solver.
  - intros p e fname vs C σ X ->. rewrite /apply_func; split.
    + inversion 1; intros ????; simplify_map_eq. naive_solver.
    + intros H; eapply ExprCallS. naive_solver.
  - by intros e [v Hv] f vs C ->.
  - by intros e C1 C2 s vv ->.
  - intros [] C1 C2 s vv Hv Hcall; cbn in *.
    rewrite /is_call /resume_with in Hcall; simplify_eq.
    by eexists.
  - intros [] C [v Hv]. rewrite /to_val /resume_with in Hv.
    repeat case_match; try congruence.
    apply app_eq_nil in H0 as (->&->); done.
  - intros [] C1 C2.
    rewrite /resume_with /comp_cont app_assoc //.
  - intros e ?????? -> H. cbv in H; by simplify_eq.
  - intros p C [] σ X Hnv. rewrite /resume_with.
    inversion 1; simplify_eq.
    all: try (econstructor; eauto; done).
    destruct k; simplify_list_eq.
    by econstructor.
  - intros p [[] ] σ H; cbv; try (by (econstructor; eauto)).
    + destruct k; cbv in H; try done.
      econstructor; eauto.
    + destruct prm; econstructor; by eauto.
    + econstructor; try by naive_solver.
      intros ?? -> Hnone _ (?&?&Hstep). by do 2 eexists.
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

(* inversion lemmas *)
(* XXX are they still useful?
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
  eapply prim_prim_step_WrSE in Hstep.
  inversion Hstep; simplify_eq.
  { exfalso.
    eapply (@language.prim_step_call_inv _ ML_lang) in H3
      as (? & ? & ? & ? & ? & ? & ?); simplify_eq. }
  2: { exfalso. by rewrite to_val_fill_call in H2. }
  apply language.of_to_class in H2. subst eml.
  eapply (@language.call_call_in_ctx _ ML_lang) in H.
  rewrite (_: ∀ k, language.comp_cont k language.empty_cont = k) // in H.
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
  eapply prim_prim_step_WrSE in Hstep.
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
  apply prim_prim_step_WrSE in Hstep.
  inversion Hstep; simplify_eq.
  { match goal with HH: Wrap.c_prim_step Pcallback _ _ _ _ _ _ |- _ => inversion HH end. }
  repeat eexists; eauto.
Qed.
*)
