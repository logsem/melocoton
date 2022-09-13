(** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)

From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import mono_nat.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From melocoton.language Require Import mlanguage.
From melocoton.c_toy_mlang Require Import weakestpre.
From melocoton.c_toy_mlang Require Import lifting.
From melocoton.c_toy_mlang Require Export lang_instantiation.
From melocoton.c_toy_mlang Require Export class_instances.
From melocoton.c_toy_mlang Require Import tactics notation.
From iris.prelude Require Import options.

Class heapGS_gen hlc Σ := HeapGS {
  heapGS_invGS : invGS_gen hlc Σ;
  heapGS_gen_heapGS :> gen_heapGS loc heap_cell Σ;
  heapGS_inv_heapGS :> inv_heapGS loc heap_cell Σ;
  heapGS_proph_mapGS :> proph_mapGS positive (prod val val) Σ;
  heapGS_step_name : gname;
  heapGS_step_cnt : mono_natG Σ;
}.
Local Existing Instance heapGS_step_cnt.

Notation heapGS := (heapGS_gen HasLc).

Section steps.
  Context `{!heapGS_gen hlc Σ}.

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

Global Program Instance heapGS_irisGS `{heapGS_gen hlc Σ} : irisGS_gen hlc C_mlang_melocoton Σ := {
  iris_invGS := heapGS_invGS;
  state_interp σ step_cnt :=
    (gen_heap_interp σ.(heap) ∗ steps_auth step_cnt)%I;
  num_laters_per_step n := n;
}.
Next Obligation.
  iIntros (??? σ ns)  "/= ($ & H)".
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

Notation "l ↦{ dq } v" := (mapsto (L:=loc) (V:=heap_cell) l dq (Some (Some v%V)))
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (mapsto (L:=loc) (V:=heap_cell) l DfracDiscarded (Storing v%V))
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn q) (Storing v%V))
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn 1) (Storing v%V))
  (at level 20, format "l  ↦  v") : bi_scope.
Notation "l ↦{ dq } '?'" := (mapsto (L:=loc) (V:=heap_cell) l dq (Uninitialized))
  (at level 20, format "l  ↦{ dq }  ?") : bi_scope.
Notation "l ↦□ '?'" := (mapsto (L:=loc) (V:=heap_cell) l DfracDiscarded (Uninitialized))
  (at level 20, format "l  ↦□  ?") : bi_scope.
Notation "l ↦{# q } '?'" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn q) (Uninitialized))
  (at level 20, format "l  ↦{# q }  ?") : bi_scope.
Notation "l ↦ '?'" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn 1) (Uninitialized))
  (at level 20, format "l  ↦  ?") : bi_scope.

(** Same for [gen_inv_heap], except that these are higher-order notations so to
make setoid rewriting in the predicate [I] work we need actual definitions
here. *)
Section definitions.
  Context `{!heapGS Σ}.

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
Context `{!heapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types p : program.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(*
#[global] Instance wp'': Wp (iProp Σ) expr val stuckness := (@wp' (C_lang p) Σ _).
#[global] Instance twp'': Twp (iProp Σ) expr val stuckness := (@twp' (C_lang p) Σ _).
*)

(* FIXME? *)
#[global] Instance c_mlang_wp : Wp (iProp Σ) expr val program := (@wp' _ C_mlang_melocoton Σ _).

Lemma to_val_eq_mlanguage e :
  to_val e = mlanguage.to_val e.
Proof.
  destruct e; cbn; auto.
  unfold mlanguage.to_val, mlanguage.to_class. cbn.
  repeat case_match; cbn; subst; congruence.
Qed.

Lemma wp_lb_init p E e Φ :
  TCEq (to_val e) None →
  (steps_lb 0 -∗ WP e @ p; E {{ v, Φ v }}) -∗
  WP e @ p; E {{ Φ }}.
Proof.
  (** TODO: We should try to use a generic lifting lemma (and avoid [wp_unfold])
  here, since this breaks the WP abstraction. *)
  rewrite to_val_eq_mlanguage !wp_unfold /wp_pre /=.
  iIntros (->) "Hwp".
  iIntros (σ1 ns) "(Hσ & Hsteps)".
  iDestruct (steps_lb_get with "Hsteps") as "#Hlb".
  iDestruct (steps_lb_le _ 0 with "Hlb") as "Hlb0"; [lia|].
  iSpecialize ("Hwp" with "Hlb0"). iApply ("Hwp" $! σ1 ns). iFrame.
Qed.

Lemma wp_lb_update s n E e Φ :
  TCEq (to_val e) None →
  steps_lb n -∗
  WP e @ s; E {{ v, steps_lb (S n) -∗ Φ v }} -∗
  WP e @ s; E {{ Φ }}.
Proof.
  (** TODO: We should try to use a generic lifting lemma (and avoid [wp_unfold])
  here, since this breaks the WP abstraction. *)
  rewrite to_val_eq_mlanguage !wp_unfold /wp_pre /=.
  iIntros (->) "Hlb Hwp".
  iIntros (σ1 ns) "(Hσ & Hsteps)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %?.
  iMod ("Hwp" $! σ1 ns with "[$Hσ $Hsteps]") as "[%Hs Hwp]".
  iModIntro. iSplit; [done|].
  iIntros (φ Hstep) "Hcred".
  iMod ("Hwp" with "[//] Hcred") as "Hwp".
  iIntros "!> !>". iMod "Hwp" as "Hwp". iIntros "!>".
  iApply (step_fupdN_wand with "Hwp").
  iIntros "Hwp". iMod "Hwp" as (e2 σ2 Hφ2) "((? & Hsteps) & Hwp)".
  iModIntro. iExists e2, σ2. iSplitR; auto.
  iDestruct (steps_lb_get with "Hsteps") as "#HlbS".
  iDestruct (steps_lb_le _ (S n) with "HlbS") as "#HlbS'"; [lia|].
  iFrame.
  iApply (wp_wand with "Hwp"). iIntros (v) "HΦ". by iApply "HΦ".
Qed.

Lemma wp_step_fupdN_lb s n E1 E2 e P Φ :
  TCEq (to_val e) None →
  E2 ⊆ E1 →
  steps_lb n -∗
  (|={E1∖E2,∅}=> |={∅}▷=>^(S n) |={∅,E1∖E2}=> P) -∗
  WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite to_val_eq_mlanguage.
  iIntros (He HE) "Hlb HP Hwp".
  iApply wp_step_fupdN; [done|].
  iSplit; [|by iFrame].
  iIntros (σ ns) "(? & Hsteps)".
  iDestruct (steps_lb_valid with "Hsteps Hlb") as %Hle.
  iApply fupd_mask_intro; [set_solver|].
  iIntros "_". iPureIntro. rewrite /num_laters_per_step /=. lia.
Qed.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb
induction directly, but this demonstrates that we can state the expected
reasoning principle for recursive functions, without any visible ▷. *)
Lemma wp_rec_löb p E f e args Φ (Ψ : list val → iProp Σ) :
   ⌜(p : gmap string function) !! f = Some (Fun args e)⌝ -∗
  □ ( □ (∀ vs res, Ψ vs -∗ ⌜zip_args args vs = Some res⌝ -∗ WP (FunCall ((&f)%V) (map Val vs)) @ p; E {{ Φ }}) -∗
     ∀ vs res, Ψ vs -∗ ⌜zip_args args vs = Some res⌝ -∗ WP (subst_all res e) @ p; E {{ Φ }}) -∗
  ∀ vs res , Ψ vs -∗ ⌜zip_args args vs = Some res⌝ -∗ WP (FunCall ((&f)%V) (map Val vs)) @ p; E {{ Φ }}.
Proof.
  iIntros "%Hp #Hrec". iLöb as "IH". iIntros (v res) "HΨ %Hres".
  iApply wp_pure_step_later; first done.
  iIntros "!> _". iApply ("Hrec" with "[] HΨ"). 2:done. iIntros "!>" (w res') "HΨ %Hres'".
  iApply ("IH" with "HΨ"). iPureIntro. apply Hres'.
Qed.


(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [option val]. *)

Lemma mapsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝.
Proof. apply mapsto_valid. Qed.
Lemma mapsto_valid_2 l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  iIntros "H1 H2". iDestruct (mapsto_valid_2 with "H1 H2") as %[? [=?]]. done.
Qed.
Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %[=?]. done. Qed.

Lemma mapsto_combine l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  iIntros "Hl1 Hl2". iDestruct (mapsto_combine with "Hl1 Hl2") as "[$ Heq]".
  by iDestruct "Heq" as %[= ->].
Qed.

Lemma mapsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_frac_ne. Qed.
Lemma mapsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_ne. Qed.

Lemma mapsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
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
  inv_heap_inv -∗ l ↦ v ={E}=∗ l ↦_I v.
Proof. iIntros (??) "#HI Hl". iApply make_inv_mapsto; done. Qed.
Lemma inv_mapsto_own_inv l v I : l ↦_I v -∗ l ↦_I □.
Proof. apply inv_mapsto_own_inv. Qed.

Lemma inv_mapsto_own_acc_strong E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv ={E, E ∖ ↑inv_heapN}=∗ ∀ l v I, l ↦_I v -∗
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ==∗
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
    (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ={E ∖ ↑inv_heapN, E}=∗ l ↦_I w)).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_mapsto_own_acc with "Hinv Hl") as "(% & Hl & Hclose)"; first done.
  iFrame "%∗". iIntros "!>" (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_mapsto_acc l I E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦_I □ ={E, E ∖ ↑inv_heapN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦ v ∗ (l ↦ v ={E ∖ ↑inv_heapN, E}=∗ ⌜True⌝).
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

Lemma wp_Malloc_seq p E v n :
  (0 < n)%Z →
  {{{ True }}} Malloc (Val $ LitV $ LitInt $ n) @ p; E
  {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ ? ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ".
  iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1 ns) "(Hσ & Hsteps) !>"; iSplit; first by auto with lia head_step.
  iIntros "!>" (φ Hstep) "Hcred"; inv_head_step.
  iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) Uninitialized)) with "Hσ")
    as "(Hσ & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite replicate_length Z2Nat.id; auto with lia. }
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iExists _, _. iSplit; first by eauto. iFrame "Hσ Hsteps". iApply "HΦ".
  iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_mapsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.

Lemma wp_free p E l (v:option val) :
  {{{ ▷ l O↦ Some v }}} Free (Val $ LitV (LitLoc l)) (Val $ LitV $ LitInt 1) @ p; E
  {{{ RET LitV LitUnit; True }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1 ns) "(Hσ & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros "!>" (φ Hstep) "Hcred"; inv_head_step.
  iMod (gen_heap_update (heap σ1) l (Some v) Deallocated with "Hσ Hl") as "[Hσ Hl]".
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iExists _, _. iSplit; first by eauto. iFrame "Hsteps".
  rewrite /state_init_heap /= map_union_empty -insert_union_singleton_l.
  iFrame "Hσ". by iApply "HΦ".
Qed.

Lemma wp_load p E l dq v :
  {{{ ▷ l ↦{dq} v }}} Load (Val $ LitV $ LitLoc l) @ p; E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1 ns) "(Hσ & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros "!>" (φ Hstep) "Hcred"; inv_head_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iExists _, _. iSplit; first by eauto. iFrame "Hsteps Hσ".
  by iApply "HΦ".
Qed.

Lemma wp_store p E l (v':option val) v :
  {{{ ▷ l O↦ Some v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ p; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1 ns) "(Hσ & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros "!>" (φ Hstep) "Hcred"; inv_head_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iMod (gen_heap_update with "Hσ Hl") as "[Hσ Hl]".
  iModIntro. iExists _, _. iSplit; first done. iFrame. by iApply "HΦ".
Qed.

Lemma wp_choice p E n :
  {{{ True }}} Choice @ p; E {{{ RET LitV (LitInt n); True }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1 ns) "(Hσ & Hsteps) !>". iSplit; first by eauto with head_step.
  iIntros "!>" (φ Hstep) "Hcred"; inv_head_step.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro. iExists _, _. iSplit; first done. iFrame. by iApply "HΦ".
Qed.

End lifting.
