From Coq Require Import ZArith.
From stdpp Require Import base gmap list.
From melocoton Require Import commons.
From melocoton.c_toy_lang Require Import lang.
From melocoton.ml_toy_lang Require Import lang.

(* the type of memory addresses used by the C semantics *)
Notation addr := iris.heap_lang.locations.loc (only parsing).
(* We call "mem" a C memory and "word" a C value. *)
Notation memory := (gmap loc heap_cell).
Notation word := C_lang.val.
(* We call "store" an ML memory and "val" an ML value. *)
Notation store := (gmap loc (option (list val))).
Notation val := ML_lang.val.

(************
   Block-level "logival" values and store.

   Block-level values and store exist as an intermediate abstraction that helps
   bridging the gap between ML memory/values and C memory/values.

   These block-level values and store are part of the wrapper private state, and
   help specify many of the "runtime invariants" modeled by the wrapper.

   Indeed, most runtime/GC invariants make the most sense when expressed at the
   level of this abstract block layer.
*)

(* The idea is that a block-level value is either an immediate integer, or a
   reference to a block in the block-level store. A block then stores an array
   of block-level values.

   The block-level store contains blocks that can be either mutable or
   immutable, and always stay at the same location. In fact, the block-level
   store monotonically grows: blocks are never deallocated at that level.

   NB: this means that blocks in the block-level store represent both mutable ML
   values (e.g. references, arrays) that are already "heap-allocated" in the ML
   semantics, but also *immutable values* (e.g. pairs) that are not
   heap-allocated in ML semantics, but are given an identity (a location) in the
   block-level layer.
*)

(* locations in the block-level store *)
Notation lloc := nat (only parsing).
Implicit Type γ : lloc.

(* block-level values *)
Inductive lval :=
  | Lint : Z → lval
  | Lloc : lloc → lval.

Inductive ismut := Mut | Immut.

(* Right now the tag is only used to distinguish between InjLV and InjRV (the
   constructors of the basic sum-type). In the future we might want to expand
   this to handle richer kinds of values. *)
Inductive tag : Type :=
  | TagDefault (* the default tag, used for InjLV and other blocks (pairs, refs, arrays) *)
  | TagInjRV (* the tag for InjRV *)
  .

Definition tag_as_int (tg : tag) : Z :=
  match tg with
  | TagDefault => 0
  | TagInjRV => 1
  end.

Global Instance tag_as_int_inj : Inj (=) (=) tag_as_int.
Proof using. intros t t'. destruct t; destruct t'; by inversion 1. Qed.

(* a block in the block-level store *)
Definition block :=
  (ismut * (tag * list lval))%type.

Definition mutability (b:block) : ismut := let '(i,_) := b in i.
Definition block_tag (b:block) : tag := let '(i,(t,d)) := b in t.
Definition block_data (b:block) : list lval := let '(i,(t,d)) := b in d.

(* a block-level store *)
Notation lstore := (gmap lloc block).
Implicit Type ζ : lstore.


(************
   In order to tie the logical block-level store to the ML and C stores, the
   wrapper also maintains a number of mappings, that e.g. relate ML locations to
   block-level locations. *)

(* maps an ML location to its corresponding logical location *)
Notation lloc_map := (gmap loc lloc).
Implicit Type χ : lloc_map.

(* maps a logical location to its address in C memory.
   Note: since blocks do not move around in the logical store, even though they
   *are* moved around by the GC in the actual memory, this means that "the
   current θ" will often arbitrarily change during the execution, each time a GC
   might occur. *)
Notation addr_map := (gmap lloc addr).
Implicit Type θ : addr_map.

(* maps each root (a heap cell in C memory) to the logical value it is tracking
   and keeping alive *)
Notation roots_map := (gmap addr lval).


(************
   Block-level state changes.

   These relations define various transitions that might need to happen on the
   logical store; these are used to define the wrapper semantics.
*)

(* freezing: turning a mutable block into an immutable block. (This is typically
   only legal as long as the mutable block has not been "observable" by other
   code than the wrapper..) *)
Inductive freeze_block : block → block → Prop :=
  | freeze_block_mut tgvs m' :
    freeze_block (Mut, tgvs) (m', tgvs)
  | freeze_block_refl b :
    freeze_block b b.

Definition freeze_lstore (ζ1 ζ2 : lstore) : Prop :=
  dom ζ1 = dom ζ2 ∧
  (∀ γ b1 b2, ζ1 !! γ = Some b1 → ζ2 !! γ = Some b2 → freeze_block b1 b2).

Definition is_store_blocks (χ : lloc_map) (σ : store) (ζ : lstore) : Prop :=
  dom σ = dom χ ∧
  (∀ γ, γ ∈ dom ζ ↔ ∃ ℓ Vs, χ !! ℓ = Some γ ∧ σ !! ℓ = Some (Some Vs)).

(* An lloc_map χ maintains a monotonically growing correspondance between ML
   locations and block-level locations. When crossing a wrapper boundary, χ
   typically needs to be extended to account for allocation of new blocks on
   either side.

   Additionally, we enforce here that the new χ2 must be injective. (Typically,
   we already know that χ1 is injective, and we are trying to impose constraints
   on χ2.) *)
Definition lloc_map_mono (χ1 χ2 : lloc_map) : Prop :=
  χ1 ⊆ χ2 ∧ gmap_inj χ2.

(* Helper relation to modify the contents of a block at a given index (which has
   to be in the bounds). Used to define the semantics of the "modify" primitive.
*)
Inductive modify_block : block → nat → lval → block → Prop :=
  | mk_modify_block tg vs i v :
    i < length vs →
    modify_block (Mut, (tg, vs)) i v (Mut, (tg, (<[ i := v ]> vs))).

(* "GC correctness": a sanity condition when picking a fresh addr_map that
   assigns C-level identifiers to the subset of "currently live" block-level
   locations.

   If a block is live in memory (its block-level location γ is in θ), then all
   the locations it points to are also live. By transitivity, all blocks
   reachable from live blocks are also live.

   (+ administrative side-conditions: θ must be injective and map locations that
   exist in ζ) *)
Definition GC_correct (ζ : lstore) (θ : addr_map) : Prop :=
  gmap_inj θ ∧
  ∀ γ, γ ∈ dom θ →
    ∃ m tg vs,
      ζ !! γ = Some (m, (tg, vs)) ∧
        ∀ γ', Lloc γ' ∈ vs → γ' ∈ dom θ.

Definition roots_are_live (θ : addr_map) (roots : roots_map) : Prop :=
  ∀ a γ, roots !! a = Some (Lloc γ) → γ ∈ dom θ.

(* C representation of block-level values, roots and memory *)

Inductive repr_lval : addr_map → lval → C_lang.val → Prop :=
  | repr_lint θ x :
    repr_lval θ (Lint x) (C_lang.LitV (C_lang.LitInt x))
  | repr_lloc θ γ a :
    θ !! γ = Some a →
    repr_lval θ (Lloc γ) (C_lang.LitV (C_lang.LitLoc a)).

Inductive repr_roots : addr_map → roots_map → memory → Prop :=
  | repr_roots_emp θ :
    repr_roots θ ∅ ∅
  | repr_roots_elem θ a v w roots mem :
    repr_roots θ roots mem →
    repr_lval θ v w →
    a ∉ dom roots →
    a ∉ dom (mem) →
    repr_roots θ (<[ a := v ]> roots)
                 (<[ a := Storing w ]> mem).

Definition repr (θ : addr_map) (roots : roots_map) (privmem mem : memory) : Prop :=
  ∃ memr, repr_roots θ roots memr ∧
  privmem ##ₘ memr ∧
  mem = memr ∪ privmem.

(* Block-level representation of ML values and store *)
Inductive is_val : lloc_map → lstore → val → lval → Prop :=
  (* non-loc base literals *)
  | is_val_int χ ζ x :
    is_val χ ζ (ML_lang.LitV (ML_lang.LitInt x)) (Lint x)
  | is_val_bool χ ζ b :
    is_val χ ζ (ML_lang.LitV (ML_lang.LitBool b)) (Lint (if b then 1 else 0))
  | is_val_unit χ ζ :
    is_val χ ζ (ML_lang.LitV ML_lang.LitUnit) (Lint 0)
  (* locations *)
  | is_val_loc χ ζ ℓ γ :
    χ !! ℓ = Some γ →
    is_val χ ζ (ML_lang.LitV (ML_lang.LitLoc ℓ)) (Lloc γ)
  (* pairs *)
  | is_val_pair χ ζ v1 v2 γ lv1 lv2 :
    ζ !! γ = Some (Immut, (TagDefault, [lv1; lv2])) →
    is_val χ ζ v1 lv1 →
    is_val χ ζ v2 lv2 →
    is_val χ ζ (ML_lang.PairV v1 v2) (Lloc γ)
  (* sum-type constructors *)
  | is_val_injl χ ζ v lv γ :
    ζ !! γ = Some (Immut, (TagDefault, [lv])) →
    is_val χ ζ v lv →
    is_val χ ζ (ML_lang.InjLV v) (Lloc γ)
  | is_val_injr χ ζ v lv γ :
    ζ !! γ = Some (Immut, (TagInjRV, [lv])) →
    is_val χ ζ v lv →
    is_val χ ζ (ML_lang.InjRV v) (Lloc γ)
  | is_val_funcall χ ζ b1 b2 e lv:
    is_val χ ζ (RecV b1 b2 e) lv.

(* Elements of the ML store are lists of values representing refs and arrays;
   they correspond to a mutable block with the default tag. *)
Inductive is_heap_elt (χ : lloc_map) (ζ : lstore) : list val → block → Prop :=
| is_heap_elt_block vs lvs :
  Forall2 (is_val χ ζ) vs lvs →
  is_heap_elt χ ζ vs (Mut, (TagDefault, lvs)).

Definition is_store (χ : lloc_map) (ζ : lstore) (σ : store) : Prop :=
  ∀ ℓ vs γ blk,
    σ !! ℓ = Some (Some vs) → χ !! ℓ = Some γ → ζ !! γ = Some blk →
    is_heap_elt χ ζ vs blk.


(******************************************************************************)
(* lemmas *)

Lemma lloc_map_mono_inj χ1 χ2 :
  lloc_map_mono χ1 χ2 →
  gmap_inj χ2.
Proof. intro H. apply H. Qed.
Global Hint Resolve lloc_map_mono_inj : core.

Lemma is_val_mono χ χL ζ ζL x y : χ ⊆ χL -> ζ ⊆ ζL -> is_val χ ζ x y → is_val χL ζL x y.
Proof.
  intros H1 H2; induction 1 in χL,ζL,H1,H2|-*; econstructor; eauto.
  all: eapply lookup_weaken; done.
Qed.

Lemma is_val_insert_immut χ ζ γ bb bb2 x y :
  ζ !! γ = Some bb2 →
  mutability bb2 = Mut →
  is_val χ ζ x y →
  is_val χ (<[γ := bb]> ζ) x y.
Proof.
  intros H1 H2; induction 1; econstructor; eauto.
  all: rewrite lookup_insert_ne; first done.
  all: intros ->; destruct bb2 as [mut [? ?]]; cbn in *.
  all: subst mut; rewrite H1 in H; congruence.
Qed.

Lemma is_store_blocks_has_loc χ σ ζ ℓ Vs :
  is_store_blocks χ σ ζ →
  σ !! ℓ = Some (Some Vs) →
  ∃ γ, χ !! ℓ = Some γ ∧ γ ∈ dom ζ.
Proof.
  intros [H1 H2] Hℓ.
  destruct (χ !! ℓ) as [γ|] eqn:Hlχ.
  2: { exfalso. apply not_elem_of_dom_2 in Hlχ. rewrite -H1 in Hlχ.
       by apply elem_of_dom_2 in Hℓ. }
  exists γ. split; auto. apply H2. eauto.
Qed.

Lemma is_store_blocks_discarded_loc χ σ ζ ℓ γ :
  is_store_blocks χ σ ζ →
  gmap_inj χ →
  σ !! ℓ = Some None →
  χ !! ℓ = Some γ →
  γ ∉ dom ζ.
Proof.
  intros [Hdom Hstore] Hinj Hσ Hχ [ℓ' (Hℓ' & Hχ' & ?)]%Hstore.
  specialize (Hinj _ _ _ Hχ Hχ'). subst ℓ'. congruence.
Qed.

Lemma is_store_blocks_discard_loc χ σ ζ ℓ γ Vs :
  is_store_blocks χ σ ζ →
  gmap_inj χ →
  χ !! ℓ = Some γ →
  σ !! ℓ = Some (Some Vs) →
  is_store_blocks χ (<[ℓ:=None]> σ) (delete γ ζ).
Proof.
  intros [Hs1 Hs2] χinj Hχℓ Hσℓ. split.
  { rewrite -Hs1 dom_insert_L. apply elem_of_dom_2 in Hσℓ. set_solver. }
  intros γ'. destruct (decide (γ = γ')) as [<-|].
  { split. { rewrite dom_delete_L. set_solver. }
    intros (ℓ' & Vs' & Hχℓ' & Hσℓ'). exfalso.
    pose proof (χinj _ _ _ Hχℓ Hχℓ') as <-. rewrite lookup_insert in Hσℓ'.
    congruence. }
  { rewrite dom_delete_L elem_of_difference. split.
    { intros [Hγ' _]. apply Hs2 in Hγ' as (ℓ'' & ? & ? & ?).
      do 2 eexists. split; eauto. rewrite lookup_insert_ne //.
      intros ->. simplify_map_eq. }
    { intros (ℓ' & Vs' & Hχℓ' & Hσℓ').
      rewrite lookup_insert_ne in Hσℓ'. 2: by intros ->; simplify_map_eq.
      split; [| set_solver]. apply Hs2. do 2 eexists. split; eauto. } }
Qed.

Lemma is_store_discard_loc χ ζ σ ℓ :
  is_store χ ζ σ →
  is_store χ ζ (<[ℓ:=None]> σ).
Proof.
  intros Hstore ℓ' Vs γ blk HH1 HH2 HH3.
  eapply Hstore; try done. destruct (decide (ℓ = ℓ')) as [<-|].
  { rewrite lookup_insert in HH1; done. }
  rewrite lookup_insert_ne in HH1; try done.
Qed.

Lemma is_store_blocks_restore_loc χ σ ζ ℓ γ Vs blk:
  is_store_blocks χ σ ζ →
  χ !! ℓ = Some γ →
  σ !! ℓ = Some None →
  is_store_blocks χ (<[ℓ:=Some Vs]> σ) (<[γ:=blk]> ζ).
Proof.
  intros [Hsl Hsr] Hχℓ Hσℓ. split.
  { rewrite <-Hsl. rewrite dom_insert_lookup_L //. }
  intros γ'. destruct (Hsr γ') as [Hsrl Hsrr]; split.
  * intros Hin. rewrite dom_insert_L in Hin. apply elem_of_union in Hin.
    destruct Hin as [->%elem_of_singleton|Hin2].
    - exists ℓ, Vs. split; try done. by rewrite lookup_insert.
    - destruct (Hsrl Hin2) as (ℓ2 & Vs2 & H1 & H2); exists ℓ2, Vs2; split; try done.
      rewrite lookup_insert_ne; first done; congruence.
  * intros (ℓ2 & Vs2 & H1 & H2). destruct (decide (ℓ2 = ℓ)) as [->|Hne].
    - rewrite Hχℓ in H1. injection H1; intros ->. rewrite dom_insert_L.
      apply elem_of_union; left. by apply elem_of_singleton.
    - rewrite dom_insert_L. apply elem_of_union; right. apply Hsrr.
      eexists _, _; split; try done. rewrite lookup_insert_ne in H2; done.
Qed.

Lemma is_store_restore_loc χ ζ σ ℓ γ Vs blk :
  is_store χ ζ σ →
  χ !! ℓ = Some γ →
  ζ !! γ = Some blk →
  is_heap_elt χ ζ Vs blk →
  is_store χ ζ (<[ℓ:=Some Vs]> σ).
Proof.
  intros Hstore Hχℓ Hζγ Hblk ℓ1 vs1 γ1 bl1 Hs1 Hs2 Hs3.
  destruct (decide (ℓ = ℓ1)) as [<- | Hne].
  * rewrite Hχℓ in Hs2. rewrite lookup_insert in Hs1. by simplify_map_eq.
  * rewrite lookup_insert_ne in Hs1; last done. eapply Hstore; done.
Qed.

Lemma is_store_blocks_expose_lloc χ ζ σ ℓ γ :
  is_store_blocks χ σ ζ →
  ℓ ∉ dom χ →
  is_store_blocks (<[ℓ:=γ]> χ) (<[ℓ:=None]> σ) ζ.
Proof.
  intros [Hsl Hsr] Hℓdom. split.
  - rewrite ! dom_insert_L. rewrite Hsl; done.
  - intros γ1; destruct (Hsr γ1) as [Hsrl Hsrr]; split.
    * intros Hin. destruct (Hsrl Hin) as (ℓ1 & Vs & H1 & H2).
      exists ℓ1, Vs. destruct (decide (ℓ1 = ℓ)) as [-> | Hn].
      2: rewrite ! lookup_insert_ne; try done.
      exfalso. apply Hℓdom. by eapply elem_of_dom.
    * intros (ℓ2 & Vs & H1 & H2). destruct (decide (ℓ = ℓ2)) as [<- | Hn].
      1: rewrite lookup_insert in H2; congruence.
      apply Hsrr. exists ℓ2, Vs.
      rewrite lookup_insert_ne in H1; last done.  rewrite lookup_insert_ne in H2; done.
Qed.

Lemma is_store_expose_lloc χ ζ σ ℓ γ :
  is_store χ ζ σ →
  ℓ ∉ dom χ →
  is_store (<[ℓ:=γ]> χ) ζ (<[ℓ:=None]> σ).
Proof.
  intros Hstore Hℓdom ℓ1 vs γ1 blk H1 H2 H3. destruct (decide (ℓ = ℓ1)) as [<- | Hn].
  1: rewrite lookup_insert in H1; congruence.
  rewrite lookup_insert_ne in H1; last done. rewrite lookup_insert_ne in H2; last done.
  specialize (Hstore _ _ _ _ H1 H2 H3).
  inversion Hstore; subst.
  econstructor. eapply Forall2_impl; first apply H.
  intros x y Hval. eapply is_val_mono; last done; eauto.
  apply insert_subseteq. by eapply not_elem_of_dom.
Qed.

Lemma is_store_freeze_lloc χ ζ σ γ b:
  is_store χ ζ σ →
  (∀ ℓ' γ', χ !! ℓ' = Some γ' → γ ≠ γ') →
  ζ !! γ = Some (Mut, b) →
  is_store χ (<[γ:=(Immut, b)]> ζ) σ.
Proof.
  intros Hstore Hfreshχ Hζγ l vs' γ1 bb H1 H2 H3.
  destruct (decide (γ = γ1)) as [<- | H4].
  * exfalso. eapply Hfreshχ; eauto.
  * rewrite lookup_insert_ne in H3; last done.
    specialize (Hstore _ _ _ _ H1 H2 H3).
    inversion Hstore. subst vs bb.
    econstructor. eapply Forall2_impl; first done.
    intros x y H5. eapply is_val_insert_immut; eauto.
Qed.

Lemma GC_correct_freeze_lloc ζ θ γ b :
  GC_correct ζ θ →
  ζ !! γ = Some (Mut, b) →
  GC_correct (<[γ := (Immut, b)]> ζ) θ.
Proof.
  intros [H1 H2] Hζγ; split; first done.
  intros γ1 Hγ. destruct (H2 γ1 Hγ) as (m & tgt & vs' & Hfreeze & Hlloc).
  destruct (decide (γ1 = γ)) as [-> |].
  - simplify_map_eq. eauto.
  - rewrite lookup_insert_ne; eauto.
Qed.

Lemma freeze_lstore_freeze_lloc ζ ζ' γ b :
  freeze_lstore ζ ζ' →
  ζ' !! γ = Some (Mut, b) →
  freeze_lstore ζ (<[γ:=(Immut, b)]> ζ').
Proof.
  intros [HL HR] Hζ'γ. split.
  - rewrite HL. rewrite dom_insert_L. rewrite subseteq_union_1_L. 1:done.
    intros ? ->%elem_of_singleton. by eapply elem_of_dom.
  - intros γ1 b1 b2 H1 H2. destruct (decide (γ = γ1)) as [<- |H3].
    * rewrite lookup_insert in H2. injection H2; intros <-.
      specialize (HR γ b1 (Mut, b) H1 Hζ'γ).
      inversion HR; subst; econstructor.
    * rewrite lookup_insert_ne in H2; last done. by eapply HR.
Qed.
