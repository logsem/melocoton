(** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)

From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import mono_nat.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From melocoton.language Require Export weakestpre lifting.
From melocoton.c_toy_lang Require Export melocoton.class_instances.
From melocoton.c_toy_lang Require Import tactics melocoton.tactics notation.
From iris.prelude Require Import options.

Class heapGS_C Σ := HeapGS {
  heapGS_gen_heapGS :> gen_heapGS loc heap_cell Σ;
  heapGS_inv_heapGS :> inv_heapGS loc heap_cell Σ;
  heapGS_proph_mapGS :> proph_mapGS positive (prod val val) Σ;
  heapGS_step_name : gname;
  heapGS_step_cnt : mono_natG Σ;
}.
Local Existing Instance heapGS_step_cnt.

Section steps.
  Context `{!heapGS_C Σ}.

  Local Definition steps_auth (n : nat) : iProp Σ :=
    mono_nat_auth_own heapGS_step_name 1 n.

  Definition steps_lb (n : nat) : iProp Σ :=
    mono_nat_lb_own heapGS_step_name n.

  Local Lemma steps_lb_valid n m :
    steps_auth n -∗ steps_lb m -∗ ⌜m ≤ n⌝.
  Proof.
    iIntros "Hauth Hlb".
    by iDestruct (mono_nat_lb_own_valid with "Hauth Hlb") as %[_ Hle].
  Qed.

  Local Lemma steps_lb_get n :
    steps_auth n -∗ steps_lb n.
  Proof. apply mono_nat_lb_own_get. Qed.

  Local Lemma steps_auth_update n n' :
    n ≤ n' → steps_auth n ==∗ steps_auth n' ∗ steps_lb n'.
  Proof. intros Hle. by apply mono_nat_own_update. Qed.

  Local Lemma steps_auth_update_S n :
    steps_auth n ==∗ steps_auth (S n).
  Proof.
    iIntros "Hauth".
    iMod (mono_nat_own_update with "Hauth") as "[$ _]"; [lia|done].
  Qed.

  Lemma steps_lb_le n n' :
    n' ≤ n → steps_lb n -∗ steps_lb n'.
  Proof. intros Hle. by apply mono_nat_lb_own_le. Qed.

End steps.

Global Program Instance heapGS_melocotonGS_C `{heapGS_C Σ}
      : melocotonGS val C_lang Σ := {
  state_interp σ step_cnt :=
    (gen_heap_interp σ ∗ steps_auth step_cnt)%I
}.
Next Obligation.
  iIntros (???? σ ns E)  "/= ($ & H)".
  by iMod (steps_auth_update_S with "H") as "$".
Qed.

(** Since we use an [option val] instance of [gen_heap], we need to overwrite
the notations.  That also helps for scopes and coercions. *)
(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)

Notation "l O↦{ dq } v" := (mapsto (L:=loc) (V:=heap_cell) l dq (v))
  (at level 20, format "l  O↦{ dq }  v") : bi_scope.
Notation "l O↦□ v" := (mapsto (L:=loc) (V:=heap_cell) l DfracDiscarded (v))
  (at level 20, format "l  O↦□  v") : bi_scope.
Notation "l O↦{# q } v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn q) (v))
  (at level 20, format "l  O↦{# q }  v") : bi_scope.
Notation "l O↦ v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn 1) (v))
  (at level 20, format "l  O↦  v") : bi_scope.

Notation "l I↦{ dq } v" := (mapsto (L:=loc) (V:=heap_cell) l dq (Some v))
  (at level 20, format "l  I↦{ dq }  v") : bi_scope.
Notation "l I↦□ v" := (mapsto (L:=loc) (V:=heap_cell) l DfracDiscarded (Some v))
  (at level 20, format "l  I↦□  v") : bi_scope.
Notation "l I↦{# q } v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn q) (Some v))
  (at level 20, format "l  I↦{# q }  v") : bi_scope.
Notation "l I↦ v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn 1) (Some v))
  (at level 20, format "l  I↦  v") : bi_scope.

Notation "l ↦C{ dq } v" := (mapsto (L:=loc) (V:=heap_cell) l dq (Some (Some v%V)))
  (at level 20, format "l  ↦C{ dq }  v") : bi_scope.
Notation "l ↦C□ v" := (mapsto (L:=loc) (V:=heap_cell) l DfracDiscarded (Storing v%V))
  (at level 20, format "l  ↦C□  v") : bi_scope.
Notation "l ↦C{# q } v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn q) (Storing v%V))
  (at level 20, format "l  ↦C{# q }  v") : bi_scope.
Notation "l ↦C v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn 1) (Storing v%V))
  (at level 20, format "l  ↦C  v") : bi_scope.
Notation "l ↦C{ dq } '?'" := (mapsto (L:=loc) (V:=heap_cell) l dq (Uninitialized))
  (at level 20, format "l  ↦C{ dq }  ?") : bi_scope.
Notation "l ↦C□ '?'" := (mapsto (L:=loc) (V:=heap_cell) l DfracDiscarded (Uninitialized))
  (at level 20, format "l  ↦C□  ?") : bi_scope.
Notation "l ↦C{# q } '?'" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn q) (Uninitialized))
  (at level 20, format "l  ↦C{# q }  ?") : bi_scope.
Notation "l ↦C '?'" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn 1) (Uninitialized))
  (at level 20, format "l  ↦C  ?") : bi_scope.

(** Same for [gen_inv_heap], except that these are higher-order notations so to
make setoid rewriting in the predicate [I] work we need actual definitions
here. *)
Section definitions.
  Context `{!heapGS_C Σ}.

  Definition from_storing (I : val → Prop) (Puninit Pfree : Prop) (k : heap_cell) :=
    match k with
    | None => Pfree
    | Some None => Puninit
    | Some (Some v) => I v
    end.

  Definition inv_mapsto_own (l : loc) (v : val) (I : val → Prop) : iProp Σ :=
    inv_mapsto_own l (Storing v) (from_storing I False False).
  Definition inv_mapsto (l : loc) (I : val → Prop) : iProp Σ :=
    inv_mapsto l (from_storing I False False).
End definitions.

Global Instance: Params (@inv_mapsto_own) 4 := {}.
Global Instance: Params (@inv_mapsto) 3 := {}.

Notation inv_heap_inv := (inv_heap_inv loc heap_cell).
Notation "l '↦_' I □" := (inv_mapsto l I%stdpp%type)
  (at level 20, I at level 9, format "l  '↦_' I  '□'") : bi_scope.
Notation "l ↦_ I v" := (inv_mapsto_own l v I%stdpp%type)
  (at level 20, I at level 9, format "l  ↦_ I  v") : bi_scope.

Section lifting.
Context `{!heapGS_C Σ, !invGS_gen hlc Σ}.
Context {p:prog_environ C_lang Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(*
#[global] Instance wp'': Wp (iProp Σ) expr val stuckness := (@wp' (C_lang p) Σ _).
#[global] Instance twp'': Twp (iProp Σ) expr val stuckness := (@twp' (C_lang p) Σ _).
*)

Lemma wp_lb_init s E e Φ :
  TCEq (to_val e) None →
  (steps_lb 0 -∗ WP e @ s; E {{ v, Φ v }}) -∗
  WP e @ s; E {{ Φ }}.
Proof.
  (** TODO: We should try to use a generic lifting lemma (and avoid [wp_unfold])
  here, since this breaks the WP abstraction. *)
  rewrite !wp_unfold /wp_pre /=. iIntros (Heq) "Hwp".
  iIntros (σ1 ns) "(Hσ & Hsteps)".
  iDestruct (steps_lb_get with "Hsteps") as "#Hlb".
  iDestruct (steps_lb_le _ 0 with "Hlb") as "Hlb0"; [lia|].
  iSpecialize ("Hwp" with "Hlb0"). iApply ("Hwp" $! σ1 ns). iFrame.
Qed.

Lemma wp_lb_update s n E e Φ :
  TCEq (to_val e) None →
  steps_lb n -∗
  WP e @ s; E {{ v, steps_lb n -∗ Φ v }} -∗
  WP e @ s; E {{ Φ }}.
Proof.
  (** TODO: We should try to use a generic lifting lemma (and avoid [wp_unfold])
  here, since this breaks the WP abstraction. *)
  rewrite !wp_unfold /wp_pre /=. iIntros (Heq) "Hlb Hwp".
  iIntros (σ1 ns) "(Hσ & Hsteps)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %?.
  iMod ("Hwp" $! σ1 ns with "[$Hσ $Hsteps]") 
      as "[(%v & -> & Hσ & Hv)|[(%s0 & %vv & %K & -> & Hprog & Hwp)|(%Hred & Hwp)]]".
  - cbn in Heq. apply TCEq_eq in Heq. congruence.
  - iModIntro. iRight. iLeft. iExists s0, vv, K. iFrame. iSplitR; first done.
    iMod "Hwp" as "(%Ξ & (Hσ & Hsteps) & HΞ & Hwp)". iModIntro. 
    iDestruct (steps_lb_get with "Hsteps") as "#HlbS".
    iExists Ξ. iFrame. iNext.
    iIntros (r) "Hr". iSpecialize ("Hwp" $! r with "Hr").
    iApply (wp_wand with "Hwp"). iIntros (v) "Hv". by iApply "Hv".
  - iModIntro. iRight. iRight. iSplitR; first done.
    iIntros (e2 σ2 Hstep). iMod ("Hwp" with "[//]") as "Hwp".
    iIntros "!> !>". iMod "Hwp" as "((Hσ & Hsteps) & Hwp)". iIntros "!>".
    iDestruct (steps_lb_get with "Hsteps") as "#HlbS".
    iDestruct (steps_lb_le _ (S n) with "HlbS") as "#HlbS'"; [lia|].
    iFrame.
    iApply (wp_wand with "Hwp"). iIntros (v) "HΦ". by iApply "HΦ".
Qed.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb
induction directly, but this demonstrates that we can state the expected
reasoning principle for recursive functions, without any visible ▷. *)
Lemma wp_rec_löb s E f e args Φ (Ψ : list val → iProp Σ) :
   ⌜penv_prog s !! f = Some (Fun args e)⌝ -∗
  □ ( □ (∀ vs res, Ψ vs -∗ ⌜zip_args args vs = Some res⌝ -∗ WP (FunCall ((&f)%V) (map Val vs)) @ s; E {{ Φ }}) -∗
     ∀ vs res, Ψ vs -∗ ⌜zip_args args vs = Some res⌝ -∗ WP (subst_all res e) @ s; E {{ Φ }}) -∗
  ∀ vs res , Ψ vs -∗ ⌜zip_args args vs = Some res⌝ -∗ WP (FunCall ((&f)%V) (map Val vs)) @ s; E {{ Φ }}.
Proof.
  iIntros "%Hp #Hrec". iLöb as "IH". iIntros (v res) "HΨ %Hres".
  iApply lifting.wp_pure_step_later. 1: eauto.
  iIntros "!>". iApply ("Hrec" with "[] HΨ"). 2:done. iIntros "!>" (w res') "HΨ %Hres'".
  iApply ("IH" with "HΨ"). iPureIntro. apply Hres'.
Qed.


(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [option val]. *)

Lemma mapsto_valid l dq v : l ↦C{dq} v -∗ ⌜✓ dq⌝.
Proof. apply mapsto_valid. Qed.
Lemma mapsto_valid_2 l dq1 dq2 v1 v2 :
  l ↦C{dq1} v1 -∗ l ↦C{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  iIntros "H1 H2". iDestruct (mapsto_valid_2 with "H1 H2") as %[? [=?]]. done.
Qed.
Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦C{dq1} v1 -∗ l ↦C{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %[=?]. done. Qed.

Lemma mapsto_combine l dq1 dq2 v1 v2 :
  l ↦C{dq1} v1 -∗ l ↦C{dq2} v2 -∗ l ↦C{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  iIntros "Hl1 Hl2". iDestruct (mapsto_combine with "Hl1 Hl2") as "[$ Heq]".
  by iDestruct "Heq" as %[= ->].
Qed.

Lemma mapsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦C{dq1} v1 -∗ l2 ↦C{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_frac_ne. Qed.
Lemma mapsto_ne l1 l2 dq2 v1 v2 : l1 ↦C v1 -∗ l2 ↦C{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_ne. Qed.

Lemma mapsto_persist l dq v : l ↦C{dq} v ==∗ l ↦C□ v.
Proof. apply mapsto_persist. Qed.

Global Instance inv_mapsto_own_proper l v :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_mapsto_own l v).
Proof.
  intros I1 I2 HI. rewrite /inv_mapsto_own. f_equiv=>-[[w|]|]; [|done|done].
  simpl. apply HI.
Qed.
Global Instance inv_mapsto_proper l :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_mapsto l).
Proof.
  intros I1 I2 HI. rewrite /inv_mapsto. f_equiv=>-[[w|]|]; [|done|done].
  simpl. apply HI.
Qed.

Lemma make_inv_mapsto l v (I : val → Prop) E :
  ↑inv_heapN ⊆ E →
  I v →
  inv_heap_inv -∗ l ↦C v ={E}=∗ l ↦_I v.
Proof. iIntros (??) "#HI Hl". iApply make_inv_mapsto; done. Qed.
Lemma inv_mapsto_own_inv l v I : l ↦_I v -∗ l ↦_I □.
Proof. apply inv_mapsto_own_inv. Qed.

Lemma inv_mapsto_own_acc_strong E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv ={E, E ∖ ↑inv_heapN}=∗ ∀ l v I, l ↦_I v -∗
    (⌜I v⌝ ∗ l ↦C v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦C w ==∗
      inv_mapsto_own l w I ∗ |={E ∖ ↑inv_heapN, E}=> True)).
Proof.
  iIntros (?) "#Hinv".
  iMod (inv_mapsto_own_acc_strong with "Hinv") as "Hacc"; first done.
  iIntros "!>" (l v I) "Hl". iDestruct ("Hacc" with "Hl") as "(% & Hl & Hclose)".
  iFrame "%∗". iIntros (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_mapsto_own_acc E l v I:
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I v ={E, E ∖ ↑inv_heapN}=∗
    (⌜I v⌝ ∗ l ↦C v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦C w ={E ∖ ↑inv_heapN, E}=∗ l ↦_I w)).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_mapsto_own_acc with "Hinv Hl") as "(% & Hl & Hclose)"; first done.
  iFrame "%∗". iIntros "!>" (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_mapsto_acc l I E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I □ ={E, E ∖ ↑inv_heapN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦C v ∗ (l ↦C v ={E ∖ ↑inv_heapN, E}=∗ ⌜True⌝).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_mapsto_acc with "Hinv Hl") as ([[v|]|]) "(% & Hl & Hclose)"; [done| |done|done].
  iIntros "!>". iExists (v). iFrame "%∗".
Qed.

(** The usable rules for [allocN] stated in terms of the [array] proposition
are derived in te file [array]. *)
Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&?)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_mapsto l (v:heap_cell) (n : nat) :
  ([∗ map] l' ↦ ov ∈ heap_array l (replicate n v), gen_heap.mapsto l' (DfracOwn 1) ov) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) O↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma wp_Malloc_seq E n :
  (0 < n)%Z →
  {{{ True }}} Malloc (Val $ LitV $ LitInt $ n) @ p; E
  {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦C ? ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1 ns) "(Hσ & Hsteps)". iModIntro. iSplit; first (destruct n; eauto with lia head_step).
  iIntros (e2 σ2 Hstep). inv_head_step. iModIntro.
  iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) Uninitialized)) with "Hσ")
    as "(Hσ & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite replicate_length Z2Nat.id; auto with lia. }
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iFrame. iApply "HΦ".
  iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_mapsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.

Lemma wp_free s E l (v:option val) :
  {{{ ▷ l O↦ Some v}}} Free (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt 1) @ s; E
  {{{ RET LitV LitUnit; True }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply (wp_step with "HΦ"). iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1 ns) "(Hσ & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (e2 σ2 Hstep); inv_head_step.
  rewrite state_init_heap_singleton. iModIntro.
  iMod (gen_heap_update (σ1) l (Some v) Deallocated with "Hσ Hl") as "[$ Hl]".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iFrame. iIntros "HΦ". iModIntro. by iApply "HΦ".
Qed.

Lemma wp_load s E l dq v :
  {{{ ▷ l ↦C{dq} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦C{dq} v }}}.
Proof.
  iIntros (Φ) "> Hl HΦ". iApply (wp_step with "HΦ"). iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1 ns) "(Hσ & Hsteps)". iDestruct (gen_heap_valid with "Hσ Hl") as "%HH". iModIntro.
  iSplitR; first ( iPureIntro; eauto with head_step).
  iIntros (e2 σ2 Hstep); inv_head_step. iModIntro.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iFrame. iIntros "HΦ". iModIntro.
  by iApply "HΦ".
Qed.

Lemma wp_store s E l (v':option val) v :
  {{{ ▷ l O↦ Some v' }}} Store (Val $ LitV $ LitLoc l) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦C v }}}.
Proof.
  iIntros (Φ) "> Hl HΦ". iApply (wp_step with "HΦ"). iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1 ns) "(Hσ & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (e2 σ2 Hstep); inv_head_step. iModIntro.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iFrame. iIntros "HΦ". iModIntro. by iApply "HΦ".
Qed.

Lemma wp_call' (s:prog_environ C_lang Σ) n args body body' vv E Φ :
     ⌜(penv_prog s) !! n = Some (Fun args body)⌝
  -∗ ⌜apply_function (Fun args body) vv = Some body'⌝
  -∗ (|={E}=> ▷ |={E}=> WP body' @ s ; E {{v, Φ v}})
  -∗ WP (FunCall ((&n)) (map Val vv)) @ s ; E {{v, Φ v}}.
Proof.
  iIntros (Hlookup Happly) "Hcont". iApply wp_lift_step_fupd.
  { cbv -[map unmap_val]. now rewrite map_unmap_val. }
  iIntros (σ1 ns) "(Hσ & Hsteps) !>".
  iSplit.
  { iPureIntro. eexists _,_. apply head_prim_step. do 2 econstructor; done. }
  iIntros (v2 σ2 Hstep). apply head_reducible_prim_step in Hstep. 2: { eexists _,_,_. do 2 econstructor; done. }
  inv_head_step. iMod "Hcont". do 2 iModIntro.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod "Hcont".
  do 2 iModIntro. iFrame.
Qed.

Lemma wp_call (s:prog_environ C_lang Σ) n args body body' vv E Φ :
     ⌜penv_prog s !! n = Some (Fun args body)⌝
  -∗ ⌜apply_function (Fun args body) vv = Some body'⌝
  -∗ (WP body' @ s ; E {{v, Φ v}})
  -∗ WP (FunCall ((&n)) (map Val vv)) @ s ; E {{v, Φ v}}.
Proof.
  iIntros (Hlookup Happly) "Hcont".
  iApply wp_call'. 1-2: done. do 3 iModIntro. done.
Qed.

(*
Lemma twp_xchg s E l v' v :
  [[{ l ↦ v' }]] Xchg (Val $ LitV $ LitLoc l) (Val v) @ s; E
  [[{ RET v'; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_xchg s E l v' v :
  {{{ ▷ l ↦ v' }}} Xchg (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET v'; l ↦ v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_xchg with "H"); [by auto..|]. iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_fail s E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  [[{ l ↦{dq} v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_false //.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro; iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_cmpxchg_fail s E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{dq} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_fail with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  [[{ l ↦ v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_true //.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_faa s E l i1 i2 :
  [[{ l ↦ LitV (LitInt i1) }]] FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  [[{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (κ e2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. do 2 (iSplit; first done). iFrame. by iApply "HΦ".
Qed.
Lemma wp_faa s E l i1 i2 :
  {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa with "H"); [by auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma wp_new_proph s E :
  {{{ True }}}
    NewProph @ s; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 ns κ κs nt) "(Hσ & HR & Hsteps) !>". iSplit; first by eauto with head_step.
  iIntros "!>" (v2 σ2 efs Hstep). inv_head_step.
  rename select proph_id into p.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (proph_map_new_proph p with "HR") as "[HR Hp]"; first done.
  iModIntro; iSplit; first done. iFrame. by iApply "HΦ".
Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a head step for [Resolve e _ _] not to be (head) stuck. *)

Lemma resolve_reducible e σ (p : proph_id) v :
  Atomic StronglyAtomic e → reducible e σ →
  reducible (Resolve e (Val (LitV (LitProphecy p))) (Val v)) σ.
Proof.
  intros A (κ & e' & σ' & efs & H).
  exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', efs.
  eapply (Ectx_step []); try done.
  assert (∃w, Val w = e') as [w <-].
  { unfold Atomic in A. apply (A σ e' κ σ' efs) in H. unfold is_Some in H.
    destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H). }
  simpl. constructor. by apply prim_step_to_val_is_head_step.
Qed.

Lemma step_resolve e vp vt σ1 κ e2 σ2 efs :
  Atomic StronglyAtomic e →
  prim_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs →
  head_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs.
Proof.
  intros A [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind.
  + simpl in *. subst. inv_head_step. by constructor.
  + rewrite fill_app /= in Hfill. destruct K; inversion Hfill; subst; clear Hfill.
    - rename select ectx_item into Ki.
      assert (fill_item Ki (fill Ks e1') = fill (Ks ++ [Ki]) e1') as Eq1;
        first by rewrite fill_app.
      assert (fill_item Ki (fill Ks e2') = fill (Ks ++ [Ki]) e2') as Eq2;
        first by rewrite fill_app.
      rewrite fill_app /=. rewrite Eq1 in A.
      assert (is_Some (to_val (fill (Ks ++ [Ki]) e2'))) as H.
      { apply (A σ1 _ κ σ2 efs). eapply (Ectx_step (Ks ++ [Ki])); done. }
      destruct H as [v H]. apply to_val_fill_some in H. by destruct H, Ks.
    - rename select (of_val vp = _) into Hvp.
      assert (to_val (fill Ks e1') = Some vp) as Hfillvp by rewrite -Hvp //.
      apply to_val_fill_some in Hfillvp as [-> ->]. inv_head_step.
    - rename select (of_val vt = _) into Hvt.
      assert (to_val (fill Ks e1') = Some vt) as Hfillvt by rewrite -Hvt //.
      apply to_val_fill_some in Hfillvt as [-> ->]. inv_head_step.
Qed.

Lemma wp_resolve s E e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  to_val e = None →
  proph p pvs -∗
  WP e @ s; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }} -∗
  WP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; E {{ Φ }}.
Proof.
  (* TODO we should try to use a generic lifting lemma (and avoid [wp_unfold])
     here, since this breaks the WP abstraction. *)
  iIntros (A He) "Hp WPe". rewrite !wp_unfold /wp_pre /= He. simpl in *.
  iIntros (σ1 ns κ κs nt) "(Hσ & Hκ & Hsteps)".
  destruct κ as [|[p' [w' v']] κ' _] using rev_ind.
  - iMod ("WPe" $! σ1 ns [] κs nt with "[$Hσ $Hκ $Hsteps]") as "[Hs WPe]".
    iModIntro. iSplit.
    { iDestruct "Hs" as "%". iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). exfalso. apply step_resolve in step; last done.
    inv_head_step. match goal with H: ?κs ++ [_] = [] |- _ => by destruct κs end.
  - rewrite -assoc.
    iMod ("WPe" $! σ1 ns _ _ nt with "[$Hσ $Hκ $Hsteps]") as "[Hs WPe]". iModIntro. iSplit.
    { iDestruct "Hs" as %?. iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). apply step_resolve in step; last done.
    inv_head_step; simplify_list_eq.
    iMod ("WPe" $! (Val w') σ2 efs with "[%]") as "WPe".
    { by eexists [] _ _. }
    iModIntro. iNext. iMod "WPe" as "WPe". iModIntro.
    iApply (step_fupdN_wand with "WPe"); iIntros "> [($ & Hκ & $) WPe]".
    iMod (proph_map_resolve_proph p' (w',v') κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]".
    iModIntro. rewrite !wp_unfold /wp_pre /=. iDestruct "WPe" as "[HΦ $]".
    iMod "HΦ". iModIntro. by iApply "HΦ".
Qed. *)

End lifting.
