From stdpp Require Import base strings list gmap.
From melocoton Require Import multirelations stdpp_extra.
From melocoton.language Require Import language.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_interface Require Import defs.
From melocoton.ml_lang Require Import lang lang_instantiation.
From melocoton.interop Require Import basics basics_constructions state prims.

Module Wrap.
Section wrappersem.

(** A wrapped program is a collection of builtins; in practice always an instance
   of [wrap_prog]. *)
Local Notation prog := (gmap string prim).

Inductive simple_expr : Type :=
  (** the wrapped module returns with a C value *)
  | ExprO  (o : outcome word)
  (* (** the wrapped module returns with a C catch value *) *)
  | ExprOC (o : outcome word)
  (** A call to a C function, which can be either:
     - an outgoing call by the wrapped code to an external C function;
     - an incoming call to a runtime primitive, which will be implemented by the wrapper
   *)
  | ExprCall (fn_name : string) (args : list word)
  (** Call to a builtin (primitive or main) *)
  | RunPrimitive (prm : prim) (args : list word)
  (** Execution of wrapped ML code *)
  | ExprML (eml : ML_lang.expr) (catch : bool).

Definition ectx := list (language.ectx ML_lang * bool).

Inductive expr : Type :=
  WrE (se: simple_expr) (k: ectx).

Definition apply_func (prm : prim) (args : list word) : option expr :=
  Some (WrE (RunPrimitive prm args) []).

Definition of_val (w : word) : expr := WrE (ExprO (OVal w)) [].

Definition to_val (e : expr) : option word :=
  match e with
  | WrE (ExprO (OVal w)) [] => Some w
  | _ => None
  end.

Definition of_outcome (o : outcome word) : expr := WrE (ExprO o) [].

Definition to_outcome (e : expr) : option (outcome word) :=
  match e with
  | WrE (ExprO o) [] => Some o
  | _ => None
  end.

Definition is_call e f vs C := e = WrE (ExprCall f vs) C.
Definition to_call f vs := WrE (ExprCall f vs) [].

Definition comp_ectx (K1 K2 : ectx) : ectx :=
  (K2 ++ K1).

Definition fill (K : ectx) (e : expr) : expr :=
  let 'WrE se k := e in
  WrE se (comp_ectx K k).

(** state of the wrapper, which depends on whether we are yielding control to
    C or executing the wrapped ML program. *)
Inductive state : Type :=
  | MLState (ρml : wrapstateML) (σ : store)
  | CState (ρc : wrapstateC) (mem : memory).

Local Notation private_state := wrapstateC.
Local Notation public_state := memory.

(** boundary states are ones in the [CState _ _] case *)
Inductive split_state : state → public_state → private_state → Prop :=
  | WrapSplitStC ρc mem :
    split_state (CState ρc mem) mem ρc.

Implicit Types X : expr * state → Prop.

Definition check_ml_state (ρml : wrapstateML) (σ : store) :=
  lloc_map_inj (χML ρml) ∧
  dom (ζML ρml) ⊆ dom (χML ρml) ∧
  dom (privmemML ρml) ## dom (rootsML ρml) ∧
  map_Forall (λ _ ℓ, σ !! ℓ = Some None) (pub_locs_in_lstore (χML ρml) (ζML ρml)).

Definition ml_to_c_heap
  (ρml : wrapstateML) (σ : store)
  (ρc : wrapstateC) (mem : memory)
: Prop :=
  ∃ (ζσ ζnewimm : lstore),
    (** Demonically get a new extended map χC. New bindings in χC correspond to
       new locations in the ML heap (e.g. allocated by ML). *)
    lloc_map_mono (χML ρml) (χC ρc) ∧
    (** The extended χC binds γs for all locations ℓ in σ; the ℓs that are mapped
       to [Some ...] in σ make up the domain of a map ζσ (whose contents are
       also chosen demonically). In other words, ζσ has exactly one block for
       each location in σ that is mapped to [Some ...]. *)
    is_store_blocks (χC ρc) σ ζσ ∧
    (** Representing the contents of the new ML heap may also require some new
       immutable blocks, which we represent in ζnewimm. The address of blocks
       in ζnewimm is LlocPrivate. *)
    is_private_blocks (χC ρc) ζnewimm ∧
    (** We take the new lstore ζC to be the old lstore + ζσ (the translation of σ
       into a lstore) + ζnewimm (new immutable blocks allocated from ML). These
       three parts must be disjoint. (ζσ and ζnewimm are disjoint by
       definition). [ζML ρml] may contain immutable blocks, mutable blocks
       allocated in C but not yet shared with the ML code, or mutable blocks
       exposed to ML but whose ownership was kept on the C side (and thus
       correspond to a [None] in σ). *)
    ζC ρc = ζML ρml ∪ ζσ ∪ ζnewimm ∧
    ζML ρml ##ₘ (ζσ ∪ ζnewimm) ∧
    (** Taken together, the contents of the new lloc_map χC and new lstore ζC
       must represent the contents of σ. (This further constraints the demonic
       choice of ζσ and ζnewimm.) *)
    is_store (χC ρc) (ζC ρc) σ ∧
    (** Demonically pick an addr_map θC satisfying the GC_correct property. *)
    GC_correct (ζC ρc) (θC ρc) ∧
    (** Rooted values must additionally be live in θC. *)
    roots_are_live (θC ρc) (rootsML ρml) ∧
    (** Pick C memory (mem) that represents the roots (through θC) + the
       remaining private C memory. *)
    rootsC ρc = dom (rootsML ρml) ∧
    repr (θC ρc) (rootsML ρml) (privmemML ρml) mem.

Definition ml_to_c_val (v : val) (w : word) (ρc : wrapstateC) : Prop :=
  ∃ (lv : lval),
    is_val (χC ρc) (ζC ρc) v lv ∧
    repr_lval (θC ρc) lv w.

Definition ml_to_c_vals
  (vs : list val) (ws : list word) (ρc : wrapstateC) : Prop :=
  ∃ (lvs : list lval),
    Forall2 (is_val (χC ρc) (ζC ρc)) vs lvs ∧
    Forall2 (repr_lval (θC ρc)) lvs ws.

Definition ml_to_c_outcome
  (ov : outcome val) (ow : outcome word) (ρc : wrapstateC) : Prop :=
  ∃ olv,
    (** Demonically pick block-level outcome value olv
        that represent the arguments ov. *)
    is_val_out (χC ρc) (ζC ρc) ov olv ∧
    (** Pick C-level outcome words that are live and represent the arguments of
        the function. (repr_lval on a location entails that it is live.) *)
    repr_lval_out (θC ρc) olv ow.

Lemma ml_to_c_words_length vs ws ρml :
  ml_to_c_vals vs ws ρml →
  length ws = length vs.
Proof.
  intros * (?&(?&?)).
  repeat match goal with H : _ |- _ => apply Forall2_length in H end.
  lia.
Qed.

Lemma ml_to_c_no_NB vs ρml σ :
  check_ml_state ρml σ →
  ∃ ws ρc mem, ml_to_c_heap ρml σ ρc mem ∧ ml_to_c_vals vs ws ρc.
Proof.
  intros (Hχinj & Hζdom & Hpublocs & Hprivmem).
  destruct (deserialize_ML_heap_extra (ζML ρml) (χML ρml) σ)
        as (χ1 & ζσ & ζσimm & Hext & Hstorebl & Hdisj & Hstore).
  1-3: done.
  destruct (deserialize_ML_values χ1 vs) as (χ2 & ζimm & lvs & Hext2 & Hvs).
  1: apply Hext.

  assert (ζML ρml ∪ ζσ ∪ ζσimm ##ₘ ζimm) as Hdis1.
  1: { eapply map_disjoint_dom. eapply disjoint_weaken. 1: eapply Hext2. 2: done.
       rewrite dom_union_L. eapply union_subseteq. split. 2: by eapply extended_to_dom_subset.
       rewrite dom_union_L. eapply union_subseteq; split.
       1: etransitivity; first by eapply elem_of_subseteq. 1: eapply subseteq_dom, Hext.
       intros γ Hγ.
       destruct Hstorebl as [_ HR]. apply HR in Hγ.
       destruct Hγ as (ℓ & ? & HH & _); by eapply elem_of_dom_2. }

  pose (ζML ρml ∪ ζσ ∪ (ζσimm ∪ ζimm)) as ζC.

  destruct (collect_dom_θ_ζ ∅ ζC) as (θdom1 & Hθdom1).
  destruct (collect_dom_θ_vs θdom1 lvs) as (θdom2 & Hθdom2).
  destruct (collect_dom_θ_roots θdom2 (rootsML ρml)) as (θdom3 & Hθdom3).
  destruct (injectivify_map θdom3) as (θC & Hdom & Hinj).
  destruct (find_repr_lval_vs θC lvs) as (ws & Hws).
  1: intros γ Hγ; subst θdom3; apply Hθdom3; right; apply Hθdom2; left; done.
  assert (roots_are_live θC (rootsML ρml)) as Hrootslive.
  1: { intros a γ ?. subst θdom3. apply Hθdom3. left. by eexists. }
  destruct (find_repr_roots θC (rootsML ρml) (privmemML ρml)) as (mem & Hrepr); [done..|].

  eexists ws, (WrapstateC χ2 ζC θC _), mem. split.
  { unfold ml_to_c_heap; eexists _, _; split_and!; try done; cbn.
    { eapply extended_to_trans; done. }
    { destruct Hstorebl as [HL HR]; split.
      { intros ℓ  Hℓ. destruct (HL ℓ Hℓ) as (γ & Hγ).
        exists γ. eapply lookup_weaken; first done. apply Hext2. }
      { intros γ; destruct (HR γ) as [HRL HRH]; split.
         1: intros H; destruct (HRL H) as (ℓ & Vs & H1 & H2);
            exists ℓ, Vs; split; try done; eapply lookup_weaken;
            first done; apply Hext2.
         intros (ℓ & Vs & H1 & H2). apply HRH.
         exists ℓ, Vs. split; try done. eapply elem_of_dom_2 in H2.
         destruct (HL _ H2) as (γ2 & Hγ2).
         enough (γ2 = γ) as -> by done. eapply Hext2. 2,3: done.
         eapply lookup_weaken; first done; eapply Hext2. } }
    { intros γ. rewrite dom_union_L. intros [H|H]%elem_of_union; eapply lookup_weaken.
      1: by eapply Hext. 2: by eapply Hext2. 2: done. 1: apply Hext2. }
    { rewrite map_union_assoc. apply map_disjoint_union_r_2. 1: done.
      eapply map_disjoint_dom, disjoint_weaken;
      first eapply map_disjoint_dom, Hdis1; try done.
      erewrite ! dom_union_L; set_solver. }
    { intros ℓ vs' γ b H1 H2 H3. unfold ζC in *.
      rewrite ! map_union_assoc. rewrite ! map_union_assoc in H3.
      apply lookup_union_Some_inv_l in H3.
      2: apply not_elem_of_dom; intros Hc; apply Hext2 in Hc; congruence.
      eapply is_heap_elt_weaken. 1: eapply Hstore; try done.
      2: apply Hext2.
      + destruct Hstorebl as [HL HR]; destruct (HL ℓ) as [v Hv];
        first by eapply elem_of_dom_2.
        rewrite <- Hv; f_equal; eapply Hext2; try done; eapply lookup_weaken, Hext2; try done.
      + eapply map_union_subseteq_l. }
    { split; first done. subst θdom3. intros γ blk γ' _ H2 H3.
      apply Hθdom3. right. apply Hθdom2. right. apply Hθdom1.
      right. left. do 2 eexists; done. } }
  { exists lvs; cbn; split; try done.
    eapply Forall2_impl; first done. intros * Hval;
    eapply is_val_mono; first done; last done.
    unfold ζC. rewrite ! map_union_assoc. eapply map_union_subseteq_r. done. }
Qed.

Lemma ml_to_c_no_NB_val v ρml σ :
  check_ml_state ρml σ →
  ∃ w ρc mem, ml_to_c_heap ρml σ ρc mem ∧ ml_to_c_val v w ρc.
Proof.
  intros H.
  eapply (ml_to_c_no_NB [v]) in H as (ws & ρc & mem & ? & H).
  assert (∃w, ws = [w]) as (w & ->).
  { eapply ml_to_c_words_length in H; cbn in H. destruct ws;
    cbn in H; try congruence.
    destruct ws; eauto; inversion H. }
  exists w, ρc, mem; split; eauto. destruct H as (lvs & Hval & Hrepr).
  assert (∃lv, lvs = [lv]) as (lv & ->).
  { apply Forall2_length in Hval. cbn in Hval. destruct lvs;
    cbn in Hval; try congruence.
    destruct lvs; eauto; inversion Hval. }
  exists lv. inversion Hrepr; subst. inversion Hval; subst.
  split; eauto.
Qed.

Lemma ml_to_c_no_NB_outcome ov ρml σ :
  check_ml_state ρml σ →
  ∃ ow ρc mem, ml_to_c_heap ρml σ ρc mem ∧ ml_to_c_outcome ov ow ρc.
Proof.
  intros H. destruct ov;
  apply (ml_to_c_no_NB_val v) in H as (w & ρc & mem & ? & (lv & Hval & Hrepr)).
  { eexists (OVal w), ρc, mem; split; eauto; exists (OVal lv).
    split; now econstructor. }
  { eexists (OExn w), ρc, mem; split; eauto; exists (OExn lv).
    split; now econstructor. }
Qed.

(* Note: The "freezing step" does properly forbid freezing a
   mutable block that has already been passed to the outside world --- but
   seeing why is not obvious. I works through the combination of:
   - sharing a logical block as a mutable value requires mapping its address to
     LlocPublic ℓ (cf is_store)
   - χ can only be updated to go from LlocPrivate to LlocPublic (cf expose_lloc)
     and otherwise grows monotonically
   - through is_store, blocks that have a public address must satisfy
     is_heap_elt and thus be mutable (cf is_heap_elt)
   - thus: trying to freeze a mutable block means breaking [is_store] unless
     we change back its address to private, which is not possible.
*)
Definition c_to_ml_heap
  (ρc : wrapstateC) (mem : memory)
  (ρml : wrapstateML) (σ : store) (ζ : lstore)
: Prop :=
  ∃ ζσ,
    (** Angelically allow freezing some blocks in (ζC ρc); the result is ζ.
       Freezing allows allocating a fresh block, mutating it, then changing
       it into an immutable block that represents an immutable ML value. *)
    freeze_lstore (ζC ρc) ζ ∧
    (** Angelically expose blocks by making their address public, picking a
       fresh ML location for them in the process. This makes it possible to
       expose new blocks to ML. *)
    expose_llocs (χC ρc) (χML ρml) ∧
    (** Split the "current" lstore ζ into (ζML ρml) (the new lstore) and a
       part ζσ that is going to be converted into the ML store σ. *)
    ζ = (ζML ρml) ∪ ζσ ∧
    (ζML ρml) ##ₘ ζσ ∧
    (** Angelically pick an ML store σ where each location mapped to [Some
       ...] corresponds to a block in ζσ. *)
    is_store_blocks (χML ρml) σ ζσ ∧
    (** The contents of ζ must represent the new σ. *)
    is_store (χML ρml) ζ σ ∧
    (** Split the C memory mem into the memory for the roots and the rest
       ("private" C memory). *)
    repr (θC ρc) (rootsML ρml) (privmemML ρml) mem ∧
    dom (rootsML ρml) = rootsC ρc.

Definition c_to_ml_vals
  (ws : list word) (ρc : wrapstateC)
  (vs : list val) (ρml : wrapstateML) (ζ : lstore)
: Prop :=
  ∃ lvs,
    Forall2 (repr_lval (θC ρc)) lvs ws ∧
    Forall2 (is_val (χML ρml) ζ) vs lvs.

Definition c_to_ml_outcome
  (ow : outcome word) (ρc : wrapstateC)
  (ov : outcome val) (ρml : wrapstateML) (ζ : lstore)
  : Prop :=
  ∃ olv,
    (** Angelically pick a block-level outcome value olv that corresponds to the
      C outcome value ow. *)
    repr_lval_out (θC ρc) olv ow ∧
    (** Angelically pick an ML outcome value ov that correspond to the
      block-level outcome value olv. *)
    is_val_out (χML ρml) ζ ov olv.

Local Notation CLocV w := (C_intf.LitV (C_intf.LitLoc w)).
Local Notation CIntV x := (C_intf.LitV (C_intf.LitInt x)).

(** Semantics of wrapper primitives, that can be called from the wrapped C
   program as external functions. The callback primitive is treated separately
   and has a dedicated case in [head_step_mrel] below. *)
(* XXX naming issue: language interface prim_step vs this prim_step *)
Implicit Types Y : outcome word → wrapstateC → memory → Prop.
Inductive c_prim_step :
  prim → list word → wrapstateC → memory →
  (outcome word → wrapstateC → memory → Prop) → Prop
:=
  | PrimAllocS ρc mem tgnum sz tg roots privmem Y :
    tgnum = vblock_tag_as_int tg →
    (0 ≤ sz)%Z →
    dom roots = rootsC ρc →
    repr (θC ρc) roots privmem mem →
    GC_correct (ζC ρc) (θC ρc) →
    roots_are_live (θC ρc) roots →
    (∀ γ χC' ζC' θC' a mem',
      χC ρc !! γ = None →
      χC' = <[ γ := LlocPrivate ]> (χC ρc) →
      ζC' = <[ γ := (Bvblock (Mut, (tg, List.repeat (Lint 0) (Z.to_nat sz)))) ]> (ζC ρc) →
      GC_correct ζC' θC' →
      repr θC' roots privmem mem' →
      roots_are_live θC' roots →
      θC' !! γ = Some a →
      Y (OVal (C_intf.LitV (C_intf.LitLoc a))) (WrapstateC χC' ζC' θC' (rootsC ρc)) mem') →
    c_prim_step Palloc [CIntV tgnum; CIntV sz] ρc mem Y
  | PrimRegisterrootS ρc mem a rootsC' Y :
    a ∉ rootsC ρc →
    rootsC' = {[ a ]} ∪ rootsC ρc →
    Y (OVal (CIntV 0)) (WrapstateC (χC ρc) (ζC ρc) (θC ρc) rootsC') mem →
    c_prim_step Pregisterroot [CLocV a] ρc mem Y
  | PrimUnregisterrootS ρc mem a rootsC' Y :
    a ∈ rootsC ρc →
    rootsC' = rootsC ρc ∖ {[ a ]} →
    Y (OVal (CIntV 0)) (WrapstateC (χC ρc) (ζC ρc) (θC ρc) rootsC') mem →
    c_prim_step Punregisterroot [CLocV a] ρc mem Y
  | PrimModifyS ρc mem w i w' γ lv blk ζC' blk' Y :
    (0 ≤ i)%Z →
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some blk →
    repr_lval (θC ρc) lv w' →
    modify_block blk (Z.to_nat i) lv blk' →
    ζC' = <[ γ := blk' ]> (ζC ρc) →
    Y (OVal (CIntV 0)) (WrapstateC (χC ρc) ζC' (θC ρc) (rootsC ρc)) mem →
    c_prim_step Pmodify [w; CIntV i; w'] ρc mem Y
  | PrimReadfieldS ρc mem w i γ mut tag lvs lv w' Y :
    (0 ≤ i)%Z →
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some (Bvblock (mut, (tag, lvs))) →
    lvs !! (Z.to_nat i) = Some lv →
    repr_lval (θC ρc) lv w' →
    Y (OVal w') ρc mem →
    c_prim_step Preadfield [w; CIntV i] ρc mem Y
  | PrimIsblockTrueS ρc mem w γ Y :
    repr_lval (θC ρc) (Lloc γ) w →
    Y (OVal (CIntV 1)) ρc mem →
    c_prim_step Pisblock [w] ρc mem Y
  | PrimIsblockFalseS ρc mem w z Y :
    repr_lval (θC ρc) (Lint z) w →
    Y (OVal (CIntV 0)) ρc mem →
    c_prim_step Pisblock [w] ρc mem Y
  | PrimReadTagS ρc mem w γ bl tg tgnum Y :
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some bl →
    tg = block_tag bl →
    tgnum = tag_as_int tg →
    Y (OVal (CIntV tgnum)) ρc mem →
    c_prim_step Pread_tag [w] ρc mem Y
  | PrimLengthS ρc mem w γ mut tag lvs Y :
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some (Bvblock (mut, (tag, lvs))) →
    Y (OVal (CIntV (length lvs))) ρc mem →
    c_prim_step Plength [w] ρc mem Y
  | PrimVal2intS ρc mem w x Y :
    repr_lval (θC ρc) (Lint x) w →
    Y (OVal (CIntV x)) ρc mem →
    c_prim_step Pval2int [w] ρc mem Y
  | PrimInt2valS ρc mem x w Y :
    repr_lval (θC ρc) (Lint x) w →
    Y (OVal w) ρc mem →
    c_prim_step Pint2val [CIntV x] ρc mem Y
  | PrimAllocForeignS roots privmem ρc mem Y :
    dom roots = rootsC ρc →
    repr (θC ρc) roots privmem mem →
    GC_correct (ζC ρc) (θC ρc) →
    roots_are_live (θC ρc) roots →
    (∀ γ χC' ζC' θC' a mem',
      χC ρc !! γ = None →
      χC' = <[ γ := LlocPrivate ]> (χC ρc) →
      ζC' = <[ γ := Bforeign (Mut, None) ]> (ζC ρc) →
      GC_correct ζC' θC' →
      repr θC' roots privmem mem' →
      roots_are_live θC' roots →
      θC' !! γ = Some a →
      Y (OVal (CLocV a)) (WrapstateC χC' ζC' θC' (rootsC ρc)) mem') →
    c_prim_step Pallocforeign [] ρc mem Y
  | PrimReadForeignS w γ mut aforeign ρc mem Y :
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some (Bforeign (mut, Some aforeign)) →
    Y (OVal aforeign) ρc mem →
    c_prim_step Preadforeign [w] ρc mem Y
  | PrimWriteForeignS w γ aforeigno aforeign' ζC' ρc mem Y :
    repr_lval (θC ρc) (Lloc γ) w →
    (ζC ρc) !! γ = Some (Bforeign (Mut, aforeigno)) →
    ζC' = <[ γ := Bforeign (Mut, Some aforeign') ]> (ζC ρc) →
    Y (OVal (CIntV 0)) (WrapstateC (χC ρc) ζC' (θC ρc) (rootsC ρc)) mem →
    c_prim_step Pwriteforeign [w; aforeign'] ρc mem Y
  | RaiseS w ρc mem Y :
    Y (OExn w) ρc mem  →
    c_prim_step Praise [w] ρc mem Y.


Lemma c_prim_step_covariant_in_Y prm ws ρc mem Y Y' :
  c_prim_step prm ws ρc mem Y →
  (∀ w ρc' mem', Y w ρc' mem' → Y' w ρc' mem') →
  c_prim_step prm ws ρc mem Y'.
Proof. intros HH Hsub. inversion HH; try (econstructor; eauto; fail). Qed.

Lemma c_prim_step_no_NB prm ws ρc mem Y :
  c_prim_step prm ws ρc mem Y →
  ∃ ws' ρc' mem', Y ws' ρc' mem'.
Proof.
  (* TODO: refactor *)
  inversion 1; simplify_eq; eauto;[|].
  { (* alloc case *)
    destruct H3 as [pubmem Hrepr2].
    destruct H4 as [? HGCOK].
    rename H5 into Hrootslive.
    pose (tg, repeat (Lint 0) (Z.to_nat sz)) as blk.
    pose ((map_to_set (fun a b => b) (θC ρc) : gset loc)) as fresh_not_θ_cod.
    pose (dom (χC ρc) ∪ dom (θC ρc) ∪ dom (ζC ρc : gmap _ _)) as fresh_src.
    pose (fresh fresh_src) as γ.
    pose (fresh fresh_not_θ_cod) as w.
    pose proof (is_fresh fresh_src) as ((HFχ&HFθ)%not_elem_of_union&HFζ)%not_elem_of_union.
    specialize (H6 γ
                  (<[ γ := LlocPrivate ]> (χC ρc))
                 (<[ γ := Bvblock (Mut, blk) ]> (ζC ρc))
                 (<[ γ := w ]> (θC ρc))
                 w mem).
    do 3 eexists. eapply H6; eauto.
    - by eapply not_elem_of_dom.
    - split.
      + eapply gmap_inj_extend; try done.
        intros k' v' Hin <-. eapply (is_fresh fresh_not_θ_cod).
        eapply elem_of_map_to_set. do 2 eexists; repeat split. apply Hin.
      + intros γ1 blk1 γ' HH1 [(->&HH)|(HA&HB)]%lookup_insert_Some HH3.
        1: subst blk1; by apply lval_in_vblock, elem_of_list_In, repeat_spec in HH3.
        rewrite dom_insert_L in HH1.
        apply elem_of_union in HH1 as [->%elem_of_singleton|HH1]; first done.
        rewrite dom_insert_L; eapply elem_of_union_r. eapply HGCOK; done.
    - eapply repr_mono; last by eexists.
      eapply insert_subseteq, not_elem_of_dom, HFθ.
    - intros l γ1 Hin. rewrite dom_insert_L; eapply elem_of_union_r.
      by eapply Hrootslive.
    - apply lookup_insert. }
  { (* alloc_foreign *)
    destruct H1 as [pubmem Hrepr2].
    destruct H2 as [? HGCOK].
    rename H3 into Hrootslive.
    pose ((map_to_set (fun a b => b) (θC ρc) : gset loc)) as fresh_not_θ_cod.
    pose (dom (χC ρc) ∪ dom (θC ρc) ∪ dom (ζC ρc : gmap _ _)) as fresh_src.
    pose (fresh fresh_src) as γ.
    pose (fresh fresh_not_θ_cod) as w.
    pose proof (is_fresh fresh_src) as ((HFχ&HFθ)%not_elem_of_union&HFζ)%not_elem_of_union.
    specialize (H4 γ
                 (<[ γ := LlocPrivate ]> (χC ρc))
                 (<[ γ := Bforeign (Mut, None) ]> (ζC ρc))
                 (<[ γ := w ]> (θC ρc))
                 w mem).
    do 3 eexists. eapply H4; eauto.
    - by eapply not_elem_of_dom.
    - split.
      + eapply gmap_inj_extend; try done.
        intros k' v' Hin <-. eapply (is_fresh fresh_not_θ_cod).
        eapply elem_of_map_to_set. do 2 eexists; repeat split. apply Hin.
      + intros γ1 blk1 γ' HH0 [(->&HH)|(HH1&HH2)]%lookup_insert_Some H3.
        1: subst; by inversion H3.
        rewrite dom_insert_L in HH0.
        apply elem_of_union in HH0 as [->%elem_of_singleton|HH0]; first done.
        rewrite dom_insert_L; eapply elem_of_union_r. eapply HGCOK; done.
    - eapply repr_mono; last by eexists.
      eapply insert_subseteq, not_elem_of_dom, HFθ.
    - intros l γ1 Hin. rewrite dom_insert_L; eapply elem_of_union_r.
      by eapply Hrootslive.
    - apply lookup_insert. }
Qed.

Local Definition is_ML_call (e : ML_lang.expr) fn_name vs K :=
  e = language.fill K (of_call _ fn_name vs).

Local Notation HVal v := (Some (Some v)).

Inductive prim_step_mrel (p : prog) : expr * state → (expr * state → Prop) → Prop :=
  (** Step in the underlying wrapped ML program. *)
  | StepMLS eml c K ρml σ X :
    (* We assume a closed ML expression: the "prog" collection of functions does
       not make too much sense at the ML level. Composition of ML "modules" is
       better modeled by composing expressions/evaluation contexts. *)
    language.language.to_val eml = None →
    reducible ∅ eml σ →
    (∀ eml' σ',
       language.language.prim_step ∅ eml σ eml' σ' →
       X (WrE (ExprML eml' c) K, MLState ρml σ')) →
    prim_step_mrel p (WrE (ExprML eml c) K, MLState ρml σ) X
  (** External call of the ML code to a C function. *)
  | MakeCallS eml c K ρml fn_name vs k σ X :
    is_ML_call eml fn_name vs k →
    p !! fn_name = None →
    check_ml_state ρml σ →
    (∀ ws ρc mem,
       ml_to_c_heap ρml σ ρc mem →
       ml_to_c_vals vs ws ρc →
       X (WrE (ExprCall fn_name ws) ((k, c)::K), CState ρc mem)) →
    prim_step_mrel p (WrE (ExprML eml c) K, MLState ρml σ) X
  (** Execution finishes with an ML value, translate it into a C value *)
  | OutS eml (c : bool) K ρml σ ov X :
    language.to_outcome eml = Some ov →
    check_ml_state ρml σ →
    (∀ ow ρc mem,
       ml_to_c_heap ρml σ ρc mem →
       ml_to_c_outcome ov ow ρc →
       if c
       then X (WrE (ExprOC ow) K, CState ρc mem)
       else X (WrE (ExprO  ow) K, CState ρc mem)) →
    prim_step_mrel p (WrE (ExprML eml c) K, MLState ρml σ) X
  (** Given a C value (result of a C extcall), resume execution into ML code. *)
  | RetS ow ki c ρc mem ov ρml σ K X ζ:
    c_to_ml_heap ρc mem ρml σ ζ →
    c_to_ml_outcome ow ρc ov ρml ζ →
    X (WrE (ExprML (language.fill ki (lang.ML_lang.of_outcome ov)) c) K, MLState ρml σ) →
    prim_step_mrel p (WrE (ExprO ow) ((ki,c)::K), CState ρc mem) X
  (** Given a C value (result of a C extcall), resume execution into ML code. *)
  | RetCS ow ρc mem K X:
    (∀ a (mem' : public_state),
      mem !! a = None →
      mem !! (a +ₗ 1) = None →
      match ow with
      | OVal v => mem' = heap_array a [HVal (CIntV 0); HVal v] ∪ mem
      | OExn v => mem' = heap_array a [HVal (CIntV 1); HVal v] ∪ mem
      end →
      X (WrE (ExprO (OVal (CLocV a))) K, CState ρc mem')) →
    prim_step_mrel p (WrE (ExprOC ow) K, CState ρc mem) X
  (** Administrative step for resolving a call to a primitive. *)
  | ExprCallS fn_name args ρ K prm X :
    p !! fn_name = Some prm →
    X (WrE (RunPrimitive prm args) K, ρ) →
    prim_step_mrel p (WrE (ExprCall fn_name args) K, ρ) X
  (** Call to a primitive (except for callback/main, see next cases) *)
  | PrimS prm ws ρc mem K X :
    c_prim_step prm ws ρc mem (λ ow ρc' mem',
        X (WrE (ExprO ow) K, CState ρc' mem')) →
    prim_step_mrel p (WrE (RunPrimitive prm ws) K, CState ρc mem) X
  (** Call to the callback primitive *)
  | CallbackS K w w' ρc mem f x e v ρml σ X ζ:
    c_to_ml_heap ρc mem ρml σ ζ →
    c_to_ml_vals [w; w'] ρc [RecV f x e; v] ρml ζ →
    X (WrE (ExprML (App (Val (RecV f x e)) (Val v)) false) K,
        MLState ρml σ) →
    prim_step_mrel p (WrE (RunPrimitive Pcallback [w; w']) K, CState ρc mem) X
  | CallbackexnS K w w' ρc mem f x e v ρml σ X ζ:
    c_to_ml_heap ρc mem ρml σ ζ →
    c_to_ml_vals [w; w'] ρc [RecV f x e; v] ρml ζ →
    X (WrE (ExprML (App (Val (RecV f x e)) (Val v)) true) K, MLState ρml σ) →
    prim_step_mrel p (WrE (RunPrimitive Pcallbackexn [w; w']) K, CState ρc mem) X

  (** Call to the main function *)
  | MainS e K mem X :
    X (WrE (ExprML e false) K, MLState (WrapstateML ∅ ∅ ∅ mem) ∅) →
    prim_step_mrel p (WrE (RunPrimitive (Pmain e) []) K, CState (WrapstateC ∅ ∅ ∅ ∅) mem) X

  (** Terminate execution with NB on values *)
  | ValStopS o σ X :
    prim_step_mrel p (of_outcome o, σ) X.

Program Definition prim_step (P : prog) : umrel (expr * state) :=
  {| mrel := prim_step_mrel P |}.
Next Obligation.
  unfold upclosed. intros p [e ρ] X Y H HXY.
  destruct H; [
    eapply StepMLS
  | eapply MakeCallS
  | eapply OutS
  | eapply RetS
  | eapply RetCS
  | eapply ExprCallS
  | eapply PrimS
  | eapply CallbackS
  | eapply CallbackexnS
  | eapply MainS
  | eapply ValStopS
  ]; unfold c_to_ml_heap in *; eauto.
  { intros * Hh Ho. destruct c; naive_solver. }
  { (* PrimS case: need to perform inversion on c_prim_step *)
    inversion H; econstructor; eauto; naive_solver. }
Qed.

Lemma mlanguage_mixin :
  MlanguageMixin (val:=word) of_outcome to_outcome to_call is_call [] comp_ectx fill
    apply_func prim_step.
Proof using.
  constructor.
  - intros c. destruct c; reflexivity.
  - intros e c. destruct e as [e k]. destruct e; cbn.
    1,2: destruct k. all: inversion 1; cbn; auto.
  - intros p v σ. eapply ValStopS.
  - intros p e fname vs K σ X ->. rewrite /apply_func; split.
    + inversion 1; simplify_map_eq. naive_solver.
    + intros (?&?&?&?&?); eapply ExprCallS; simplify_eq; eauto.
  - by intros e [v Hv] f vs K ->.
  - by intros e K1 K2 s vv ->.
  - intros. reflexivity.
  - by intros * ->.
  - intros *. inversion 1; eauto.
  - intros [] K [v Hv]. rewrite /to_outcome /fill in Hv.
    repeat case_match; try congruence.
    apply app_eq_nil in H0 as (->&->); done.
  - intros e K [o Ho]. rewrite /to_outcome /fill in Ho.
    repeat case_match; try congruence. inversion H; subst.
    apply app_eq_nil in H5 as (->&->); done.
  - intros [] K1 K2.
    rewrite /fill /comp_ectx app_assoc //.
  - intros [? ?]. rewrite /= /comp_ectx app_nil_r //.
  - intros p C [es eK] σ X Hnv. inversion 1; simplify_eq.
    all: try (econstructor; eauto; naive_solver).
    + eapply OutS; eauto. intros; unfold comp_ectx, fill.
      destruct c; eexists _; cbn; split; eauto; cbn; unfold comp_ectx; eauto.
    + unfold fill, comp_ectx; cbn. eapply RetS; eauto; eexists; split; eauto.
      cbn; eauto.
    + econstructor; eauto. intros.
      eexists (WrE (ExprO (OVal (CLocV a))) _); split; eauto.
    + econstructor; eauto. eexists (WrE _ _); eauto.
    + econstructor; eauto.
      eapply c_prim_step_covariant_in_Y; eauto. cbn.
      intros. eexists (WrE _ _); eauto.
    + eapply CallbackS; eauto. eexists (WrE _ _); eauto.
    + eapply CallbackexnS; eauto. eexists (WrE _ _); eauto.
    + eapply MainS; eauto. eexists (WrE _ _); eauto.
  - intros p [[]] σ X; cbn.
    + destruct k; try done; intros _.
      inversion 1; simplify_eq. eauto.
    + intros _. inversion 1; simplify_eq.
      pose (fresh_locs (dom mem)) as a.
      pose (match o with OVal _ => 0 | OExn _ => 1 end) as is_exn.
      pose (match o with OVal v | OExn v => v end) as ov.
      assert (mem !! a = None ∧ mem !! (a +ₗ 1) = None) as [Ha Ha1].
      { split; eapply not_elem_of_dom; unfold a.
        - rewrite -(loc_add_0 (fresh_locs _)). eapply (fresh_locs_fresh). lia.
        - eapply fresh_locs_fresh. lia. }
      pose (heap_array a [HVal (CIntV is_exn); HVal ov] ∪ mem) as mem'.
      eexists (WrE (ExprO (OVal (CLocV a))) k), (CState ρc mem').
      destruct o; eapply H4; eauto.
    + intros _. inversion 1; simplify_eq; eauto.
    + intros _. inversion 1; simplify_eq; eauto.
      apply c_prim_step_no_NB in H5 as (?&?&?&?); eauto.
    + intros _. inversion 1; simplify_eq.
      * destruct H6 as (?&?&?). eauto.
      * apply (ml_to_c_no_NB vs) in H7 as (?&?&?&?&?); eauto.
      * apply (ml_to_c_no_NB_outcome ov) in H6 as (?&?&?&?&?).
        destruct catch; eauto.
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

Notation wrap_prog e := (wrap_prog e : mlang_prog wrap_lang).
