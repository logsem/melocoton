From Coq Require Import ZArith.
From stdpp Require Import base gmap list.
From iris.heap_lang Require Export locations.
From melocoton Require Import stdpp_extra language_commons.
From melocoton.c_interface Require Import defs.
From melocoton.ml_lang Require Import lang.

(** the type of memory addresses used by the C semantics *)
Notation addr := iris.heap_lang.locations.loc (only parsing).
(** We call "mem" a C memory and "word" a C value. *)
Notation memory := (gmap loc heap_cell).
Notation word := C_intf.val.
(** We call "store" an ML memory and "val" an ML value. *)
Notation store := (gmap loc (option (list val))).
Notation val := ML_lang.val.

(** Block-level values and store.

   Block-level values and store exist as an intermediate abstraction that helps
   bridging the gap between ML memory/values and C memory/values.

   These block-level values and store are part of the wrapper private state, and
   help specify many of the "runtime invariants" modeled by the wrapper.

   Indeed, most runtime/GC invariants make the most sense when expressed at the
   level of this abstract block layer.
*)

(** The idea is that a block-level value is either an immediate integer, or a
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

(** locations in the block-level store *)
Notation lloc := nat (only parsing).
Implicit Type γ : lloc.

(** block-level values *)
Inductive lval :=
  | Lint : Z → lval
  | Lloc : lloc → lval.

(** Currently the mutability tag applies to a whole block; but ultimately we want
   each field of the block to have its [ismut] tag (to handle record types of
   the form { foo : int; mutable bar : int }) *)
Inductive ismut := Mut | Immut.

(** Possible tags for "value blocks", i.e. blocks that contain ML values. *)
(** Right now the tag is only used to distinguish between InjLV and InjRV (the
   constructors of the basic sum-type). In the future we might want to expand
   this to handle richer kinds of values (e.g. richer sum types). *)
Inductive vblock_tag :=
  | TagDefault (** the default tag, used for InjLV and other blocks (pairs, refs, arrays) *)
  | TagInjRV. (** the tag for InjRV *)

(** Possible tags for blocks in the general case. *)
Inductive tag : Type :=
  | TagVblock (vtg : vblock_tag)
  | TagClosure
  | TagForeign.

Definition vblock_tag_as_int (vtg : vblock_tag) : Z :=
  match vtg with
  | TagDefault => 0
  | TagInjRV => 1
  end.

Definition tag_as_int (tg : tag) : Z :=
  match tg with
  | TagVblock vtg => vblock_tag_as_int vtg
  | TagClosure => 247
  | TagForeign => 255
  end.

Global Instance vblock_tag_as_int_inj : Inj (=) (=) vblock_tag_as_int.
Proof using.
  intros t t'. destruct t; destruct t'; by inversion 1.
Qed.

Global Instance tag_as_int_inj : Inj (=) (=) tag_as_int.
Proof using.
  intros t t'.
  destruct t as [vt| |]; destruct t' as [vt'| |];
    try destruct vt; try destruct vt';
    by inversion 1.
Qed.

(** a "value block" (the most common type of block) *)
Notation vblock :=
  (ismut * (vblock_tag * list lval))%type.

Notation fblock :=
  (ismut * option C_intf.val)%type.

(** a block in the block-level store *)
Inductive block :=
  | Bvblock (vblk : vblock)
  | Bclosure (clos_f clos_x : binder) (clos_body : ML_lang.expr)
  (** A limited form of OCaml's "custom blocks", storing a C value *)
  | Bforeign (fblk : fblock).

Definition vblock_mutability (vb: vblock) : ismut :=
  let '(i,_) := vb in i.

Definition fblock_mutability (fb: fblock) : ismut :=
  let '(i,_) := fb in i.

Definition mutability (b: block) : ismut :=
  match b with
  | Bvblock vblk => vblock_mutability vblk
  | Bclosure _ _ _ => Immut
  | Bforeign fblk => fblock_mutability fblk
  end.

Definition vblock_get_tag (vb: vblock) : vblock_tag :=
  let '(_,(tg,_)) := vb in tg.

Definition block_tag (b: block) : tag :=
  match b with
  | Bvblock vblk => TagVblock (vblock_get_tag vblk)
  | Bclosure _ _ _ => TagClosure
  | Bforeign _ => TagForeign
  end.

Inductive lval_in_block : block → lval → Prop :=
  | ValInVblock v m tg vs :
    v ∈ vs → lval_in_block (Bvblock (m, (tg, vs))) v.

(** a block-level store *)
Notation lstore := (gmap lloc block).
Implicit Type ζ : lstore.


(** In order to tie the logical block-level store to the ML and C stores, the
   wrapper maintains a map that relates block-level locations to ML locations,
   and a map that relates block-level locations with C values. *)

(** For each block-level location, we track whether it correspond to a ML-level
   location ℓ (case [LlocPublic ℓ]), or whether it only exists in the
   block-level heap (case [LlocPrivate]). *)
Inductive lloc_visibility :=
  | LlocPublic (ℓ : loc)
  | LlocPrivate.

(** An [lloc_map] maps a block location to its visibility status *)
Notation lloc_map := (gmap lloc lloc_visibility).
Implicit Type χ : lloc_map.

(** An [addr_map] maps a block location to its "current" C address.
   Note: since blocks do not move around in the logical store, even though they
   *are* moved around by the GC in the actual memory, this means that "the
   current θ" will often arbitrarily change during the execution, each time a GC
   might occur. *)
Notation addr_map := (gmap lloc addr).
Implicit Type θ : addr_map.

(** maps each root (a heap cell in C memory) to the logical value it is tracking
   and keeping alive *)
Notation roots_map := (gmap addr lval).


(** lloc_map injectivity: lloc_maps are always injective wrt public locs and
   foreign ids
*)

Definition lloc_map_inj χ :=
  ∀ γ1 γ2 vis,
    χ !! γ1 = Some vis →
    χ !! γ2 = Some vis →
    vis ≠ LlocPrivate →
    γ1 = γ2.

(** Block-level state changes.

   These relations define various transitions that might need to happen on the
   logical store; these are used to define the wrapper semantics.
*)

(** freezing: turning a mutable block into an immutable block. (This is typically
   only legal as long as the mutable block has not been "observable" by other
   code than the wrapper..) *)
Inductive freeze_block : block → block → Prop :=
  | freeze_block_mut tgvs :
    freeze_block (Bvblock (Mut, tgvs)) (Bvblock (Immut, tgvs))
  | freeze_block_foreign w :
    freeze_block (Bforeign (Mut, w)) (Bforeign (Immut, w))
  | freeze_block_refl b :
    freeze_block b b.

Definition freeze_lstore (ζ1 ζ2 : lstore) : Prop :=
  dom ζ1 = dom ζ2 ∧
  (∀ γ b1 b2, ζ1 !! γ = Some b1 → ζ2 !! γ = Some b2 → freeze_block b1 b2).

Inductive expose_lloc : lloc_visibility → lloc_visibility → Prop :=
  | expose_lloc_private ℓ : expose_lloc LlocPrivate (LlocPublic ℓ)
  | expose_lloc_refl vis : expose_lloc vis vis.

Definition expose_llocs (χ1 χ2 : lloc_map) : Prop :=
  dom χ1 = dom χ2 ∧
  lloc_map_inj χ2 ∧
  (∀ γ vis1 vis2, χ1 !! γ = Some vis1 → χ2 !! γ = Some vis2 → expose_lloc vis1 vis2).

Definition is_store_blocks (χ : lloc_map) (σ : store) (ζ : lstore) : Prop :=
  (∀ ℓ, ℓ ∈ dom σ → ∃ γ, χ !! γ = Some (LlocPublic ℓ)) ∧
  (∀ γ, γ ∈ dom ζ ↔ ∃ ℓ Vs, χ !! γ = Some (LlocPublic ℓ) ∧ σ !! ℓ = Some (Some Vs)).

Definition is_private_blocks (χ : lloc_map) (ζ : lstore) : Prop :=
  ∀ γ, γ ∈ dom ζ → χ !! γ = Some LlocPrivate.

(** An lloc_map χ maintains a monotonically growing correspondance between ML
   locations and block-level locations. When crossing a wrapper boundary, χ
   typically needs to be extended to account for allocation of new blocks on
   either side.

   Additionally, we enforce here that the new χ2 must be injective. (Typically,
   we already know that χ1 is injective, and we are trying to impose constraints
   on χ2.) *)
Definition lloc_map_mono (χ1 χ2 : lloc_map) : Prop :=
  χ1 ⊆ χ2 ∧ lloc_map_inj χ2.

(** Helper relation to modify the contents of a block at a given index (which has
   to be in the bounds). Used to define the semantics of the "modify" primitive.
*)
Inductive modify_block : block → nat → lval → block → Prop :=
  | mk_modify_block tg vs i v :
    i < length vs →
    modify_block (Bvblock (Mut, (tg, vs))) i v (Bvblock (Mut, (tg, (<[ i := v ]> vs)))).

(** "GC correctness": a sanity condition when picking a fresh addr_map that
   assigns C-level identifiers to the subset of "currently live" block-level
   locations.

   If a block is live in memory (its block-level location γ is in θ), then all
   the locations it points to are also live. By transitivity, all blocks
   reachable from live blocks are also live.

   (+ administrative side-conditions: θ must be injective and map locations that
   exist in ζ) *)
Definition GC_correct (ζ : lstore) (θ : addr_map) : Prop :=
  gmap_inj θ ∧
  ∀ γ blk γ',
    γ ∈ dom θ →
    ζ !! γ = Some blk →
    lval_in_block blk (Lloc γ') →
    γ' ∈ dom θ.

Definition roots_are_live (θ : addr_map) (roots : roots_map) : Prop :=
  ∀ a γ, roots !! a = Some (Lloc γ) → γ ∈ dom θ.

(** C representation of block-level values, roots and memory *)

Definition code_int (z:Z) : word := (C_intf.LitV (C_intf.LitInt (2*z + 1))).

Inductive repr_lval : addr_map → lval → C_intf.val → Prop :=
  | repr_lint θ x :
    repr_lval θ (Lint x) (code_int x)
  | repr_lloc θ γ a :
    θ !! γ = Some a →
    repr_lval θ (Lloc γ) (C_intf.LitV (C_intf.LitLoc a)).

Inductive repr_lval_out : addr_map → outcome lval → outcome C_intf.val → Prop :=
  | repr_lval_val θ lv v :
    repr_lval θ lv v →
    repr_lval_out θ (OVal lv) (OVal v).

Inductive repr_roots : addr_map → roots_map → memory → Prop :=
  | repr_roots_empty θ :
    repr_roots θ ∅ ∅
  | repr_roots_elem θ a v w roots mem :
    repr_roots θ roots mem →
    repr_lval θ v w →
    a ∉ dom roots →
    a ∉ dom (mem) →
    repr_roots θ (<[ a := v ]> roots)
                 (<[ a := Storing w ]> mem).

Definition repr_mem (θ : addr_map) (roots : roots_map) (privmem mem : memory) : Prop :=
  ∃ memr,
    repr_roots θ roots memr ∧
    privmem ##ₘ memr ∧
    mem = memr ∪ privmem.

(** Block-level representation of ML values and store *)
Inductive is_val : lloc_map → lstore → val → lval → Prop :=
  (** non-loc base literals *)
  | is_val_int χ ζ x :
    is_val χ ζ (ML_lang.LitV (ML_lang.LitInt x)) (Lint x)
  | is_val_bool χ ζ b :
    is_val χ ζ (ML_lang.LitV (ML_lang.LitBool b)) (Lint (if b then 1 else 0))
  | is_val_unit χ ζ :
    is_val χ ζ (ML_lang.LitV ML_lang.LitUnit) (Lint 0)
  (** locations *)
  | is_val_boxedint χ ζ γ x :
    ζ !! γ = Some (Bforeign (Immut, Some (C_intf.LitV (C_intf.LitInt x)))) →
    is_val χ ζ (ML_lang.LitV (ML_lang.LitBoxedInt x)) (Lloc γ)
  | is_val_loc χ ζ ℓ γ :
    χ !! γ = Some (LlocPublic ℓ) →
    is_val χ ζ (ML_lang.LitV (ML_lang.LitLoc ℓ)) (Lloc γ)
  (** pairs *)
  | is_val_pair χ ζ v1 v2 γ lv1 lv2 :
    ζ !! γ = Some (Bvblock (Immut, (TagDefault, [lv1; lv2]))) →
    is_val χ ζ v1 lv1 →
    is_val χ ζ v2 lv2 →
    is_val χ ζ (ML_lang.PairV v1 v2) (Lloc γ)
  (** sum-type constructors *)
  | is_val_injl χ ζ v lv γ :
    ζ !! γ = Some (Bvblock (Immut, (TagDefault, [lv]))) →
    is_val χ ζ v lv →
    is_val χ ζ (ML_lang.InjLV v) (Lloc γ)
  | is_val_injr χ ζ v lv γ :
    ζ !! γ = Some (Bvblock (Immut, (TagInjRV, [lv]))) →
    is_val χ ζ v lv →
    is_val χ ζ (ML_lang.InjRV v) (Lloc γ)
  (** closures *)
  | is_val_closure χ ζ γ f x e :
    ζ !! γ = Some (Bclosure f x e) →
    is_val χ ζ (ML_lang.RecV f x e) (Lloc γ)
  (** foreign blocks *)
  | is_val_private χ ζ γ :
    is_val χ ζ (ML_lang.LitV (ML_lang.LitForeign γ)) (Lloc γ).

(** Elements of the ML store are lists of values representing refs and arrays;
   they correspond to a mutable block with the default tag. *)
Inductive is_heap_elt (χ : lloc_map) (ζ : lstore) : list val → block → Prop :=
| is_heap_elt_block vs lvs :
  Forall2 (is_val χ ζ) vs lvs →
  is_heap_elt χ ζ vs (Bvblock (Mut, (TagDefault, lvs))).

Definition is_store (χ : lloc_map) (ζ : lstore) (σ : store) : Prop :=
  ∀ ℓ vs γ blk,
    σ !! ℓ = Some (Some vs) → χ !! γ = Some (LlocPublic ℓ) → ζ !! γ = Some blk →
    is_heap_elt χ ζ vs blk.

Inductive is_val_out : lloc_map → lstore → outcome val → outcome lval → Prop :=
  | is_val_out_val χ ζ v lv:
    is_val χ ζ v lv →
    is_val_out χ ζ (OVal v) (OVal lv).

(******************************************************************************)
(** auxiliary definitions and lemmas *)

Global Hint Resolve freeze_block_refl : core.
Global Hint Resolve expose_lloc_refl : core.

Global Instance ismut_eqdecision : EqDecision ismut.
Proof. intros [] []; solve_decision. Qed.

Global Instance lloc_visibility_eqdecision : EqDecision lloc_visibility.
Proof. intros [] []; solve_decision. Qed.

Definition lloc_map_pubs (χ : lloc_map) : gmap lloc loc :=
  omap (λ vis, match vis with LlocPublic ℓ => Some ℓ | _ => None end) χ.

Definition lloc_map_pub_locs (χ : lloc_map) : gset loc :=
  list_to_set ((map_to_list (lloc_map_pubs χ)).*2).

Definition pub_locs_in_lstore (χ : lloc_map) (ζ : lstore) : gmap lloc loc :=
  filter (λ '(γ, _), γ ∈ dom ζ) (lloc_map_pubs χ).

Definition lstore_immut_blocks (ζ : lstore) : lstore :=
  filter (λ '(_, bb), mutability bb = Immut) ζ.

Lemma lloc_map_pubs_empty : lloc_map_pubs ∅ = ∅.
Proof. rewrite /lloc_map_pubs omap_empty //. Qed.

Lemma lloc_map_pubs_lookup_Some χ γ ℓ :
  lloc_map_pubs χ !! γ = Some ℓ ↔ χ !! γ = Some (LlocPublic ℓ).
Proof.
  rewrite /lloc_map_pubs lookup_omap.
  destruct (χ !! γ) as [[]|]; naive_solver.
Qed.

Lemma lloc_map_pubs_lookup_Some_1 χ γ ℓ :
  lloc_map_pubs χ !! γ = Some ℓ → χ !! γ = Some (LlocPublic ℓ).
Proof. apply lloc_map_pubs_lookup_Some. Qed.
Global Hint Resolve lloc_map_pubs_lookup_Some_1 : core.

Lemma lloc_map_pubs_lookup_Some_2 χ γ ℓ :
  χ !! γ = Some (LlocPublic ℓ) → lloc_map_pubs χ !! γ = Some ℓ.
Proof. apply lloc_map_pubs_lookup_Some. Qed.
Global Hint Resolve lloc_map_pubs_lookup_Some_2 : core.

Lemma lloc_map_pubs_lookup_None χ γ :
  lloc_map_pubs χ !! γ = None ↔
  χ !! γ = None ∨
  χ !! γ = Some LlocPrivate.
Proof.
  rewrite /lloc_map_pubs lookup_omap.
  destruct (χ !! γ) as [[]|]; naive_solver.
Qed.

Lemma lloc_map_pubs_insert_pub χ γ ℓ :
  lloc_map_pubs (<[γ:=LlocPublic ℓ]> χ) = <[γ:=ℓ]> (lloc_map_pubs χ).
Proof. rewrite /lloc_map_pubs omap_insert //. Qed.

Lemma lloc_map_pubs_insert_priv χ γ :
  lloc_map_pubs (<[γ:=LlocPrivate]> χ) = delete γ (lloc_map_pubs χ).
Proof. rewrite /lloc_map_pubs omap_insert //. Qed.

Lemma elem_of_lloc_map_pub_locs ℓ χ :
  ℓ ∈ lloc_map_pub_locs χ ↔ ∃ γ, χ !! γ = Some (LlocPublic ℓ).
Proof.
  rewrite elem_of_list_to_set elem_of_list_fmap.
  split; [intros ([? ?] & -> & HH) | intros (? & ?)].
  { rewrite elem_of_map_to_list in HH. eauto. }
  { eexists (_, _). cbn. split; eauto. rewrite elem_of_map_to_list. eauto. }
Qed.

Lemma elem_of_lloc_map_pub_locs_1 ℓ γ χ :
  χ !! γ = Some (LlocPublic ℓ) → ℓ ∈ lloc_map_pub_locs χ.
Proof. intros HH. apply elem_of_lloc_map_pub_locs. eauto. Qed.
Global Hint Resolve elem_of_lloc_map_pub_locs_1 : core.

Lemma pub_locs_in_lstore_empty :
  pub_locs_in_lstore ∅ ∅ = ∅.
Proof. rewrite /pub_locs_in_lstore lloc_map_pubs_empty //. Qed.

Lemma pub_locs_in_lstore_lookup χ ζ γ ℓ :
  γ ∈ dom ζ
→ χ !! γ = Some (LlocPublic ℓ)
→ pub_locs_in_lstore χ ζ !! γ = Some ℓ.
Proof.
  intros H1 H2. unfold pub_locs_in_lstore.
  erewrite map_filter_lookup_Some_2. 3: done. 1: done.
  erewrite lloc_map_pubs_lookup_Some_2; done.
Qed.

Lemma pub_locs_in_lstore_lookup_notin χ ζ γ :
  ζ !! γ = None →
  pub_locs_in_lstore χ ζ !! γ = None.
Proof.
  intros Hnotin. apply map_filter_lookup_None. right.
  intros ? ?%lloc_map_pubs_lookup_Some ?.
  by apply not_elem_of_dom_2 in Hnotin.
Qed.
Global Hint Resolve pub_locs_in_lstore_lookup_notin : core.

Lemma pub_locs_in_lstore_insert_lstore_pub χ ζ γ ℓ blk :
  χ !! γ = Some (LlocPublic ℓ) →
  pub_locs_in_lstore χ (<[γ:=blk]> ζ) = <[γ:=ℓ]> (pub_locs_in_lstore χ ζ).
Proof.
  intros Hγ. rewrite /pub_locs_in_lstore dom_insert_L. eapply map_eq.
  intros γ'. destruct (decide (γ = γ')) as [<-|].
  { rewrite lookup_insert. apply map_filter_lookup_Some.
    rewrite lloc_map_pubs_lookup_Some. set_solver. }
  rewrite lookup_insert_ne//. rewrite !map_filter_lookup.
  destruct (lloc_map_pubs χ !! γ'); eauto; cbn.
  apply option_guard_iff. set_solver.
Qed.

Lemma pub_locs_in_lstore_insert_existing χ ζ γ blk :
  γ ∈ dom ζ →
  pub_locs_in_lstore χ (<[γ:=blk]> ζ) = pub_locs_in_lstore χ ζ.
Proof.
  intros Hγζ. rewrite /pub_locs_in_lstore dom_insert_L. eapply map_eq.
  intros γ'. rewrite !map_filter_lookup.
  destruct (lloc_map_pubs χ !! γ'); eauto; cbn.
  destruct (decide (γ = γ')) as [<-|].
  { rewrite !option_guard_True; set_solver. }
  apply option_guard_iff. set_solver.
Qed.

Lemma pub_locs_in_lstore_insert_pub χ ζ γ ℓ :
  γ ∈ dom ζ →
  pub_locs_in_lstore (<[γ:=LlocPublic ℓ]> χ) ζ = <[γ:=ℓ]> (pub_locs_in_lstore χ ζ).
Proof.
  intros Hγ. rewrite /pub_locs_in_lstore lloc_map_pubs_insert_pub. eapply map_eq.
  intros γ'. rewrite map_filter_lookup.
  destruct (decide (γ = γ')) as [<-|]; simplify_map_eq.
  { destruct (decide (γ ∈ dom ζ)); by simplify_map_eq. }
  rewrite map_filter_lookup //.
Qed.

Lemma pub_locs_in_lstore_insert_pub_sub χ ζ γ ℓ :
  pub_locs_in_lstore (<[γ:=LlocPublic ℓ]> χ) ζ ⊆ <[γ:=ℓ]> (pub_locs_in_lstore χ ζ).
Proof.
  rewrite /pub_locs_in_lstore lloc_map_pubs_insert_pub.
  eapply map_subseteq_spec. intros γ' ℓ'.
  rewrite map_filter_lookup.
  destruct (decide (γ = γ')) as [<-|]; simplify_map_eq.
  { destruct (decide (γ ∈ dom ζ)); by simplify_map_eq. }
  rewrite map_filter_lookup //.
Qed.

Lemma pub_locs_in_lstore_insert_priv χ ζ γ b :
  χ !! γ = Some LlocPrivate →
  pub_locs_in_lstore χ (<[γ:=b]> ζ) = pub_locs_in_lstore χ ζ.
Proof.
  intros Hγ. rewrite /pub_locs_in_lstore.
  apply map_filter_strong_ext_1.
  intros γ' ℓ; split; intros [H1 H2]; split; try done.
  2: erewrite dom_insert_L; eapply elem_of_union; by right.
  erewrite dom_insert_L in H1; eapply elem_of_union in H1; destruct H1 as [H1%elem_of_singleton|H1].
  2: done.
  apply lloc_map_pubs_lookup_Some_1 in H2. congruence.
Qed.

Lemma pub_locs_in_lstore_alloc_priv χ ζ γ b:
  χ !! γ = None →
  pub_locs_in_lstore (<[γ:=LlocPrivate]> χ) (<[γ:=b]>ζ) = pub_locs_in_lstore χ ζ.
Proof.
  intros Hγ. rewrite pub_locs_in_lstore_insert_priv.
  2: apply lookup_insert.
  rewrite /pub_locs_in_lstore lloc_map_pubs_insert_priv delete_notin.
  2: apply lloc_map_pubs_lookup_None; by left.
  done.
Qed.

Lemma pub_locs_in_lstore_insert_priv_store χ ζ ζ2 :
  is_private_blocks χ ζ2 →
  pub_locs_in_lstore χ (ζ ∪ ζ2) = pub_locs_in_lstore χ ζ.
Proof.
  intros Hγ. rewrite /pub_locs_in_lstore.
  apply map_filter_strong_ext_1.
  intros γ' ℓ; split; intros [H1 H2]; split; try done.
  2: erewrite dom_union_L; eapply elem_of_union; by left.
  erewrite dom_union_L in H1; eapply elem_of_union in H1; destruct H1 as [H1|H1].
  1: done.
  specialize (Hγ γ' H1).
  apply lloc_map_pubs_lookup_Some_1 in H2.
  congruence.
Qed.

Lemma pub_locs_in_lstore_mono χ1 χ2 ζ :
  dom ζ ⊆ dom χ1 →
  lloc_map_mono χ1 χ2 →
  pub_locs_in_lstore χ1 ζ = pub_locs_in_lstore χ2 ζ.
Proof.
  intros Hsub (Hsub2&Hinj).
  unfold pub_locs_in_lstore.
  apply map_filter_strong_ext_1.
  intros γ' ℓ; split; intros [H1 H2]; split; try done.
  - apply lloc_map_pubs_lookup_Some. apply lloc_map_pubs_lookup_Some in H2.
    eapply lookup_weaken; done.
  - apply lloc_map_pubs_lookup_Some. apply lloc_map_pubs_lookup_Some in H2.
    eapply elem_of_weaken in H1; last apply Hsub.
    eapply elem_of_dom in H1; destruct H1 as [v Hv].
    eapply lookup_weaken_inv in H2; last apply Hsub2; last done. congruence.
Qed.

Lemma pub_locs_in_lstore_delete_lstore χ ζ γ :
  pub_locs_in_lstore χ (delete γ ζ) = delete γ (pub_locs_in_lstore χ ζ).
Proof.
  rewrite /pub_locs_in_lstore dom_delete_L. eapply map_eq.
  intros γ'. destruct (decide (γ = γ')) as [<-|].
  { rewrite lookup_delete. apply map_filter_lookup_None. set_solver. }
  rewrite lookup_delete_ne//. rewrite !map_filter_lookup.
  destruct (lloc_map_pubs χ !! γ'); eauto; cbn.
  apply option_guard_iff. set_solver.
Qed.

Lemma lstore_immut_blocks_lookup_Some ζ γ b :
  lstore_immut_blocks ζ !! γ = Some b ↔ ζ !! γ = Some b ∧ mutability b = Immut.
Proof.
  rewrite /lstore_immut_blocks map_filter_lookup /=.
  set X := (ζ !! γ). destruct (ζ !! γ) as [[[i' ?]| |[i' ?]]|] eqn:HH; subst X; cbn;
      try naive_solver.
  2: rewrite option_guard_True //; naive_solver.
  all: destruct (decide (i' = Immut)); subst.
  1, 3: rewrite option_guard_True //; naive_solver.
  all: rewrite option_guard_False //; naive_solver.
Qed.

Lemma lstore_immut_blocks_lookup_notin ζ γ :
  ζ !! γ = None →
  lstore_immut_blocks ζ !! γ = None.
Proof.
  intros Hnotin. rewrite /lstore_immut_blocks map_filter_lookup Hnotin //.
Qed.
Global Hint Resolve lstore_immut_blocks_lookup_notin : core.

Lemma lstore_immut_blocks_lookup_mut ζ γ b :
  ζ !! γ = Some b →
  mutability b = Mut →
  lstore_immut_blocks ζ !! γ = None.
Proof.
  intros Hb Hmut. rewrite /lstore_immut_blocks map_filter_lookup Hb /=.
  rewrite option_guard_False//. congruence.
Qed.
Global Hint Resolve lstore_immut_blocks_lookup_mut : core.

Lemma lstore_immut_blocks_lookup_immut ζ γ b :
  ζ !! γ = Some b →
  mutability b = Immut →
  lstore_immut_blocks ζ !! γ = Some b.
Proof.
  intros ? ?. rewrite lstore_immut_blocks_lookup_Some. naive_solver.
Qed.

Lemma lstore_immut_blocks_insert_mut ζ γ bb :
  mutability bb = Mut →
  lstore_immut_blocks (<[γ:=bb]> ζ) = delete γ (lstore_immut_blocks ζ).
Proof.
  intros Hmut. rewrite /lstore_immut_blocks map_filter_insert_False; [|congruence].
  apply map_filter_delete.
Qed.

Lemma lstore_immut_blocks_insert_immut ζ γ bb :
  mutability bb = Immut →
  lstore_immut_blocks (<[γ:=bb]> ζ) = <[γ:=bb]> (lstore_immut_blocks ζ).
Proof.
  intros HH. rewrite /lstore_immut_blocks map_filter_insert_True; done.
Qed.

Lemma lstore_immut_blocks_delete ζ γ :
  lstore_immut_blocks (delete γ ζ) = delete γ (lstore_immut_blocks ζ).
Proof. rewrite /lstore_immut_blocks. apply map_filter_delete. Qed.

Lemma lloc_map_mono_inj χ1 χ2 :
  lloc_map_mono χ1 χ2 →
  lloc_map_inj χ2.
Proof. intro H. apply H. Qed.
Global Hint Resolve lloc_map_mono_inj : core.


Lemma lloc_map_mono_trans χ1 χ2 χ3 : lloc_map_mono χ1 χ2 → lloc_map_mono χ2 χ3 → lloc_map_mono χ1 χ3.
Proof.
  intros [H1 _] [H2 H3]. split.
  1: by etransitivity. done.
Qed.

Lemma lloc_map_inj_insert χ vis γ :
  lloc_map_inj χ →
  (∀ γ' vis', vis ≠ LlocPrivate → χ !! γ' = Some vis' → vis' ≠ vis) →
  lloc_map_inj (<[γ := vis]> χ).
Proof.
  intros Hinj Hid γ1 γ2 vis' H1 H2 Hvis'.
  destruct (decide (γ1 = γ2)); auto. exfalso.
  destruct (decide (γ = γ1)) as [<-|]; simplify_map_eq; first naive_solver.
  destruct (decide (γ = γ2)) as [<-|]; simplify_map_eq; naive_solver.
Qed.

Lemma lloc_map_inj_insert_pub χ ℓ γ :
  lloc_map_inj χ →
  ℓ ∉ lloc_map_pub_locs χ →
  lloc_map_inj (<[γ := LlocPublic ℓ]> χ).
Proof.
  intros ? Hℓ. apply lloc_map_inj_insert; eauto.
  intros ? ? _ ? ->. apply Hℓ. apply elem_of_lloc_map_pub_locs; eauto.
Qed.

Lemma lloc_map_inj_insert_priv χ γ :
  lloc_map_inj χ →
  lloc_map_inj (<[γ := LlocPrivate]> χ).
Proof. intros. apply lloc_map_inj_insert; eauto. Qed.

Lemma expose_llocs_refl χ :
  lloc_map_inj χ →
  expose_llocs χ χ.
Proof using.
  intros. split_and!; auto. intros; simplify_map_eq.
  apply expose_lloc_refl.
Qed.

Lemma expose_llocs_inj χ1 χ2 :
  expose_llocs χ1 χ2 →
  lloc_map_inj χ2.
Proof. intro H. apply H. Qed.
Global Hint Resolve expose_llocs_inj : core.

Lemma expose_llocs_trans χ1 χ2 χ3 :
  expose_llocs χ1 χ2 →
  expose_llocs χ2 χ3 →
  expose_llocs χ1 χ3.
Proof.
  intros (Hdom1 & Hinj1 & He1) (Hdom2 & Hinj2 & He2).
  repeat split.
  - by rewrite Hdom1.
  - done.
  - intros γ vis1 vis2 H1 H3. destruct (χ2 !! γ) eqn:H2.
    2: { apply not_elem_of_dom in H2. apply elem_of_dom_2 in H1. set_solver. }
    specialize (He1 _ _ _ H1 H2). specialize (He2 _ _ _ H2 H3).
    inversion He1; inversion He2; simplify_eq; econstructor; eauto.
Qed.

Lemma expose_llocs_insert χ γ ℓ :
  χ !! γ = Some LlocPrivate →
  ℓ ∉ lloc_map_pub_locs χ →
  lloc_map_inj χ →
  expose_llocs χ (<[γ := LlocPublic ℓ]> χ).
Proof.
  intros Hγ Hℓ Hinj. repeat split.
  - rewrite dom_insert_L. apply elem_of_dom_2 in Hγ. set_solver.
  - eapply lloc_map_inj_insert_pub; eauto.
  - intros γ' vis1 vis2 H1 H2.
    destruct (decide (γ = γ')) as [<-|]; simplify_map_eq; econstructor; eauto.
Qed.

Lemma expose_llocs_insert_both χ χ' γ vis vis' :
  expose_llocs χ χ' →
  χ !! γ = None →
  (∀ γ' vis'', vis' ≠ LlocPrivate → χ' !! γ' = Some vis'' → vis'' ≠ vis') →
  expose_lloc vis vis' →
  expose_llocs (<[γ:=vis]> χ) (<[γ:=vis']> χ').
Proof.
  intros (Hdom & Hinj & Hexp) Hγ Hvis. repeat split.
  { rewrite !dom_insert_L Hdom //. }
  { by apply lloc_map_inj_insert. }
  { intros γ0 vis1 vis2 ?%lookup_insert_Some ?%lookup_insert_Some.
    destruct_or!; destruct_and!; simplify_eq; eauto. }
Qed.

Global Instance freeze_lstore_refl : Reflexive (freeze_lstore).
Proof.
  intros ζ; split; first done.
  intros γ b1 b2 H1 H2. rewrite H1 in H2; injection H2; intros ->.
  apply freeze_block_refl.
Qed.

Lemma freeze_lstore_freeze_lloc ζ ζ' γ b1 b2 :
  freeze_block b1 b2 →
  freeze_lstore ζ ζ' →
  ζ' !! γ = Some b1 →
  freeze_lstore ζ (<[γ:=b2]> ζ').
Proof.
  intros HB [HL HR] Hζ'γ. split.
  - rewrite HL. rewrite dom_insert_L. rewrite subseteq_union_1_L. 1:done.
    intros ? ->%elem_of_singleton. by eapply elem_of_dom.
  - intros γ1 b1' b2' H1 H2. destruct (decide (γ = γ1)) as [<- |H3].
    * rewrite lookup_insert in H2. injection H2; intros <-.
      specialize (HR γ b1' b1 H1 Hζ'γ).
      inversion HR; subst; destruct HB; try econstructor; try inversion HR; try econstructor.
    * rewrite lookup_insert_ne in H2; last done. by eapply HR.
Qed.

Lemma freeze_lstore_lookup ζ ζ' γ blk :
  freeze_lstore ζ ζ' →
  ζ !! γ = Some blk →
  ∃ blk', freeze_block blk blk' ∧ ζ' !! γ = Some blk'.
Proof.
  intros [HL HR] Hγ.
  destruct (ζ' !! γ) eqn:Hγ'; eauto.
  apply elem_of_dom_2 in Hγ. apply not_elem_of_dom in Hγ'. congruence.
Qed.

Lemma freeze_lstore_lookup_backwards ζ ζ' γ blk' :
  freeze_lstore ζ ζ' →
  ζ' !! γ = Some blk' →
  ∃ blk, freeze_block blk blk' ∧ ζ !! γ = Some blk.
Proof.
  intros [HL HR] Hγ.
  destruct (ζ !! γ) eqn:Hγ'; eauto.
  apply elem_of_dom_2 in Hγ. apply not_elem_of_dom in Hγ'. congruence.
Qed.

Lemma freeze_lstore_lookup_bclosure ζ ζ' γ f x e :
  freeze_lstore ζ ζ' →
  ζ' !! γ = Some (Bclosure f x e) →
  ζ !! γ = Some (Bclosure f x e).
Proof.
  intros Hfreeze Hζ'.
  eapply freeze_lstore_lookup_backwards in Hfreeze as (? & Hfrz & ?);
    eauto.
  by inversion Hfrz; simplify_eq.
Qed.

Lemma freeze_lstore_insert ζ ζ' γ blk :
  freeze_lstore ζ ζ' →
  freeze_lstore (<[γ := blk]> ζ) (<[γ := blk]> ζ').
Proof using.
  intros (Hdom & HH). split.
  { rewrite !dom_insert_L. set_solver. }
  { intros γ' b1 b2 HH1 HH2.
    destruct (decide (γ = γ')) as [<-|]; simplify_map_eq; naive_solver. }
Qed.

Lemma is_val_mono χ χL ζ ζL x y :
  χ ⊆ χL → ζ ⊆ ζL →
  is_val χ ζ x y →
  is_val χL ζL x y.
Proof.
  intros H1 H2; induction 1 in χL,ζL,H1,H2|-*; econstructor; eauto.
  all: eapply lookup_weaken; done.
Qed.

Lemma is_val_out_mono χ χL ζ ζL x y :
  χ ⊆ χL → ζ ⊆ ζL →
  is_val_out χ ζ x y →
  is_val_out χL ζL x y.
Proof.
  intros H1 H2; inversion 1; econstructor; eauto.
  eapply is_val_mono; eauto.
Qed.

Lemma is_val_expose_llocs χ χ' ζ v lv :
  expose_llocs χ χ' →
  is_val χ ζ v lv →
  is_val χ' ζ v lv.
Proof.
  intros He. induction 1 in χ',He; econstructor; eauto.
  destruct He as (Hdom & Hinj & He).
  destruct (χ' !! γ) eqn:HH.
  2: { exfalso. apply not_elem_of_dom_2 in HH. rewrite -Hdom in HH.
       apply not_elem_of_dom_1 in HH. naive_solver. }
  specialize (He _ _ _ ltac:(eassumption) HH). inversion He; auto.
Qed.

Lemma is_val_insert_immut χ ζ γ bb bb2 x y :
  ζ !! γ = Some bb2 →
  mutability bb2 = Mut →
  is_val χ ζ x y →
  is_val χ (<[γ := bb]> ζ) x y.
Proof.
  intros H1 H2; induction 1; econstructor; eauto.
  all: rewrite lookup_insert_ne; first done.
  all: intros ->; destruct bb2 as [[mut ?]| |[mut ?]]; cbn in *.
  all: congruence.
Qed.

Lemma is_val_freeze χ ζ ζfreeze v lv :
  freeze_lstore ζ ζfreeze →
  is_val χ ζ v lv →
  is_val χ ζfreeze v lv.
Proof using.
  intros Hfreeze. induction 1; try by constructor.
  all: econstructor; eauto.
  all: eapply freeze_lstore_lookup in Hfreeze as (?&Hblk&?); eauto.
  all: by inversion Hblk; subst.
Qed.

Lemma is_store_blocks_is_private_blocks_disjoint χ σ ζs ζp :
  is_store_blocks χ σ ζs →
  is_private_blocks χ ζp →
  ζs ##ₘ ζp.
Proof.
  intros [Hs1 Hs2] Hp. apply map_disjoint_spec. intros ℓ b1 b2 Hsℓ Hpℓ.
  apply elem_of_dom_2, Hs2 in Hsℓ as (?&?&?&?).
  apply elem_of_dom_2, Hp in Hpℓ. congruence.
Qed.

Lemma is_store_blocks_has_loc χ σ ζ ℓ Vs :
  is_store_blocks χ σ ζ →
  σ !! ℓ = Some (Some Vs) →
  ∃ γ, χ !! γ = Some (LlocPublic ℓ) ∧ γ ∈ dom ζ.
Proof.
  intros [H1 H2] Hℓ.
  destruct (H1 ℓ) as (γ & Hγ); [by eapply elem_of_dom_2|].
  eexists; split; eauto. apply H2. eauto.
Qed.

Lemma is_store_blocks_discarded_loc χ σ ζ ℓ γ :
  is_store_blocks χ σ ζ →
  σ !! ℓ = Some None →
  χ !! γ = Some (LlocPublic ℓ) →
  γ ∉ dom ζ.
Proof.
  intros [Hdom Hstore] Hσ Hχ [ℓ' (Hℓ' & Hχ' & ?)]%Hstore.
  simplify_map_eq.
Qed.

Lemma is_store_blocks_discard_loc χ σ ζ ℓ γ Vs :
  is_store_blocks χ σ ζ →
  lloc_map_inj χ →
  χ !! γ = Some (LlocPublic ℓ) →
  σ !! ℓ = Some (Some Vs) →
  is_store_blocks χ (<[ℓ:=None]> σ) (delete γ ζ).
Proof.
  intros [Hs1 Hs2] χinj Hχℓ Hσℓ. split.
  { intros ℓ'. rewrite dom_insert_lookup_L//. eauto. }
  intros γ'. destruct (decide (γ = γ')) as [<-|].
  { split. { rewrite dom_delete_L. set_solver. }
    intros (ℓ' & Vs' & Hχℓ' & Hσℓ'). simplify_map_eq. }
  { rewrite dom_delete_L elem_of_difference. split.
    { intros [Hγ' _]. apply Hs2 in Hγ' as (ℓ'' & ? & Hχℓ'' & ?).
      do 2 eexists. split; eauto. rewrite lookup_insert_ne //.
      intros ->. by specialize (χinj _ _ _ Hχℓ Hχℓ'' ltac:(done)). }
    { intros (ℓ' & Vs' & Hχℓ' & Hσℓ').
      rewrite lookup_insert_ne in Hσℓ'.
      2: { intros ->. by specialize (χinj _ _ _ Hχℓ Hχℓ' ltac:(done)). }
      split; [| set_solver]. apply Hs2. do 2 eexists. split; eauto. } }
Qed.

Lemma is_store_blocks_lstore_dom_sub χ σ ζ : is_store_blocks χ σ ζ → dom ζ ⊆ dom χ.
Proof using.
  intros [_ HH]. apply elem_of_subseteq. intros γ Hγ.
  by apply HH in Hγ as (?&?&?%elem_of_dom_2&?).
Qed.

Lemma is_private_blocks_dom_sub χ ζ : is_private_blocks χ ζ → dom ζ ⊆ dom χ.
Proof using.
  intros Hpriv. apply elem_of_subseteq. intros γ Hγ.
  by apply Hpriv, elem_of_dom_2 in Hγ.
Qed.

Lemma is_store_blocks_restore_loc χ σ ζ ℓ γ Vs blk:
  is_store_blocks χ σ ζ →
  lloc_map_inj χ →
  χ !! γ = Some (LlocPublic ℓ) →
  (σ !! ℓ = Some None ∨ σ !! ℓ = None) →
  is_store_blocks χ (<[ℓ:=Some Vs]> σ) (<[γ:=blk]> ζ).
Proof.
  intros [Hsl Hsr] Hχinj Hχℓ Hσℓ. split.
  { intros ℓ'. rewrite dom_insert_L //. intros [->%elem_of_singleton|H]%elem_of_union.
    1: by eexists. eauto. }
  intros γ'. destruct (Hsr γ') as [Hsrl Hsrr]; split.
  * intros Hin. rewrite dom_insert_L in Hin. apply elem_of_union in Hin.
    destruct Hin as [->%elem_of_singleton|Hin2].
    - exists ℓ, Vs. split; try done. by rewrite lookup_insert.
    - destruct (Hsrl Hin2) as (ℓ2 & Vs2 & H1 & H2); exists ℓ2, Vs2; split; try done.
      rewrite lookup_insert_ne; first done; destruct Hσℓ; congruence.
  * intros (ℓ2 & Vs2 & H1 & H2). destruct (decide (ℓ2 = ℓ)) as [->|Hne].
    - specialize (Hχinj _ _ _ Hχℓ H1). simplify_map_eq. set_solver.
    - rewrite dom_insert_L. apply elem_of_union; right. apply Hsrr.
      eexists _, _; split; try done. rewrite lookup_insert_ne in H2; done.
Qed.

Lemma is_store_blocks_expose_lloc χ ζ σ ℓ γ :
  is_store_blocks χ σ ζ →
  χ !! γ = Some LlocPrivate →
  ℓ ∉ dom σ →
  is_store_blocks (<[γ:=LlocPublic ℓ]> χ) (<[ℓ:=None]> σ) ζ.
Proof.
  intros [Hsl Hsr] Hγ Hℓdom. split.
  - intros ℓ'. rewrite !dom_insert_L elem_of_union elem_of_singleton.
    intros [<-|Hℓ']. by exists γ; simplify_map_eq.
    specialize (Hsl _ Hℓ') as (γ'&?). exists γ'.
    rewrite lookup_insert_ne //. set_solver.
  - intros γ'; destruct (Hsr γ') as [Hsrl Hsrr]. split.
    * intros Hin. specialize (Hsrl Hin) as (ℓ' & Vs' & H1 & H2).
      eexists ℓ', Vs'. rewrite lookup_insert_ne. 2: congruence.
      split; eauto. rewrite lookup_insert_ne//.
      eapply not_elem_of_dom in Hℓdom. naive_solver.
    * intros (ℓ2 & Vs & H1 & H2). destruct (decide (ℓ = ℓ2)) as [<- | Hn].
      1: rewrite lookup_insert in H2; congruence.
      apply Hsrr. destruct (decide (γ = γ')) as [<-|]; [by simplify_map_eq|].
      rewrite !lookup_insert_ne // in H1, H2. exists ℓ2, Vs. eauto.
Qed.

Lemma is_store_blocks_alloc_block χ σ ζσ γ :
  χ !! γ = None →
  is_store_blocks χ σ ζσ →
  is_store_blocks (<[γ:=LlocPrivate]> χ) σ ζσ.
Proof using.
  intros ? [HH1 HH2]. split.
  { intros ℓ1 Hℓ1. destruct (HH1 ℓ1 Hℓ1) as (γ'&?). exists γ'.
    rewrite lookup_insert_ne//. congruence. }
  { intros γ'. rewrite HH2. split; intros (ℓ' & VS & HH0 & ?).
    { do 2 eexists. split; eauto. rewrite lookup_insert_ne//. congruence. }
    { do 2 eexists. split; eauto.
      destruct (decide (γ = γ')) as [<-|]; by simplify_map_eq. } }
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

Lemma is_store_restore_loc χ ζ σ ℓ γ Vs blk :
  is_store χ ζ σ →
  lloc_map_inj χ →
  χ !! γ = Some (LlocPublic ℓ) →
  ζ !! γ = Some blk →
  is_heap_elt χ ζ Vs blk →
  is_store χ ζ (<[ℓ:=Some Vs]> σ).
Proof.
  intros Hstore Hχinj Hχℓ Hζγ Hblk ℓ1 vs1 γ1 bl1 Hs1 Hs2 Hs3.
  destruct (decide (ℓ = ℓ1)) as [<- | Hne].
  * specialize (Hχinj _ _ _ Hχℓ Hs2 ltac:(done)). by simplify_map_eq.
  * rewrite lookup_insert_ne in Hs1; last done. eapply Hstore; done.
Qed.

Lemma is_store_expose_lloc χ ζ σ ℓ γ :
  is_store χ ζ σ →
  χ !! γ = Some LlocPrivate →
  ℓ ∉ dom σ →
  ℓ ∉ lloc_map_pub_locs χ →
  lloc_map_inj χ →
  is_store (<[γ:=LlocPublic ℓ]> χ) ζ (<[ℓ:=None]> σ).
Proof.
  intros Hstore Hγ Hℓdom Hℓpubs Hinj ℓ1 vs γ1 blk H1 H2 H3.
  destruct (decide (ℓ = ℓ1)) as [<- | Hn]; [by simplify_map_eq|].
  destruct (decide (γ = γ1)) as [<- |]; [by simplify_map_eq|].
  rewrite !lookup_insert_ne // in H1, H2.
  specialize (Hstore _ _ _ _ H1 H2 H3).
  inversion Hstore; subst.
  econstructor. eapply Forall2_impl; first eauto.
  intros x y Hval. eapply is_val_expose_llocs; last done; eauto.
  eapply expose_llocs_insert; eauto.
Qed.

Lemma is_store_freeze_lloc χ ζ σ γ b1 b2:
  is_store χ ζ σ →
  freeze_block b1 b2 →
  χ !! γ = Some LlocPrivate →
  ζ !! γ = Some b1 →
  is_store χ (<[γ:=b2]> ζ) σ.
Proof.
  intros Hstore Hfreeze Hpriv Hζγ l vs' γ1 bb H1 H2 H3.
  destruct (decide (γ = γ1)) as [<- | H4].
  * simplify_map_eq.
  * rewrite lookup_insert_ne in H3; last done.
    specialize (Hstore _ _ _ _ H1 H2 H3).
    inversion Hstore. subst vs bb.
    econstructor. eapply Forall2_impl; first done.
    intros x y H5. destruct Hfreeze.
    1, 2: eapply is_val_insert_immut; eauto.
    assert ((<[γ:=b]> ζ) = ζ) as Hζ. { by apply insert_id. }
    by rewrite Hζ.
Qed.

Lemma is_store_alloc_block χ σ ζσ ζ γ blk :
  χ !! γ = None →
  ζσ !! γ = None →
  ζ !! γ = None →
  is_store χ (ζσ ∪ ζ) σ →
  is_store (<[γ:=LlocPrivate]> χ) (<[γ:=blk]> (ζσ ∪ ζ)) σ.
Proof using.
  intros Hχγ ? ? Hstore. unfold is_store.
  intros ℓ vs γ1 blk1 HH1 [[??]|[? HH2]]%lookup_insert_Some HH3; try congruence.
  rewrite lookup_insert_ne in HH3; last done.
  specialize (Hstore ℓ vs γ1 blk1 HH1 HH2 HH3).
  inversion Hstore; subst. econstructor.
  eapply Forall2_impl; first eassumption.
  intros vml vl HH4. eapply is_val_mono. 3: apply HH4.
  + by eapply insert_subseteq.
  + eapply insert_subseteq. by eapply lookup_union_None.
Qed.

Lemma is_store_modify_priv_block χ ζ σ γ blk blk':
  is_store χ ζ σ →
  ζ !! γ = Some blk →
  (∀ ℓ Vs, χ !! γ = Some (LlocPublic ℓ) → σ !! ℓ = Some (Some Vs) → False) →
  mutability blk = Mut →
  is_store χ (<[γ:=blk']> ζ) σ.
Proof.
  intros Hstore Hγ Hpriv Hmut ℓ Vs γ' bb H1 H2 [[<- <-]|[Hne H3']]%lookup_insert_Some.
  { exfalso. eapply Hpriv; eauto. }
  { specialize (Hstore ℓ Vs γ' bb H1 H2 H3'). inversion Hstore; subst.
    constructor. eapply Forall2_impl; first done. intros.
    eapply is_val_insert_immut; eauto. }
Qed.

Lemma GC_correct_freeze_lloc ζ θ γ b :
  GC_correct ζ θ →
  ζ !! γ = Some (Bvblock (Mut, b)) →
  GC_correct (<[γ := Bvblock (Immut, b)]> ζ) θ.
Proof.
  intros [H1 H2] Hζγ; split; first done. intros γ1 * ? ?.
  inversion 1; subst.
  destruct (decide (γ1 = γ)) as [-> |];
    simplify_map_eq; eauto.
  eapply H2; eauto. by constructor.
Qed.

Lemma repr_roots_dom θ roots mem : repr_roots θ roots mem → dom roots = dom mem.
Proof.
  induction 1.
  + by do 2 rewrite dom_empty_L.
  + by do 2 rewrite dom_insert_L; rewrite IHrepr_roots.
Qed.

Lemma code_int_inj z1 z2 : code_int z1 = code_int z2 → z1 = z2.
Proof.
  intros H; simplify_eq; lia.
Qed.

Lemma repr_lval_inj θ v w w' : repr_lval θ v w → repr_lval θ v w' → w = w'.
Proof.
  induction 1; inversion 1.
  + done.
  + rewrite H in H3. injection H3; intros ->; done.
Qed.

Lemma repr_lval_inj_1 θ v v' w : gmap_inj θ → repr_lval θ v w → repr_lval θ v' w -> v = v'.
Proof.
  unfold code_int.
  intros H; induction 1; inversion 1.
  + f_equal; lia.
  + subst. f_equal. by eapply H.
Qed.

Lemma repr_lval_lint θ1 θ2 z w : repr_lval θ1 (Lint z) w → repr_lval θ2 (Lint z) w.
Proof.
  inversion 1; simplify_eq; by econstructor.
Qed.

Lemma repr_lval_mono θ θ' v w: θ ⊆ θ' → repr_lval θ v w → repr_lval θ' v w.
Proof.
  intros H; induction 1; econstructor.
  eapply lookup_weaken; done.
Qed.

(* The development is generic over the precise encoding of ints *)
Opaque code_int.

Lemma repr_roots_mono θ θ' roots_m mem :
  θ ⊆ θ' →
  repr_roots θ roots_m mem →
  repr_roots θ' roots_m mem.
Proof.
  intros Helem HH. induction HH.
  - econstructor.
  - econstructor. 1: by eapply IHHH. 2-3: done.
    by eapply repr_lval_mono.
Qed.

Lemma repr_mem_mono θ θ' roots_m privmem mem :
  θ ⊆ θ' →
  repr_mem θ roots_m privmem mem →
  repr_mem θ' roots_m privmem mem.
Proof.
  intros Helem (memr&(H1&?&->)). exists memr.
  split; eauto using repr_roots_mono.
Qed.

Lemma repr_mem_disj θ roots_m privmem mem :
  repr_mem θ roots_m privmem mem →
  dom privmem ## dom roots_m.
Proof.
  intros (? & ? & ?%map_disjoint_dom & ->).
  erewrite repr_roots_dom; eauto.
Qed.

Lemma repr_mem_empty_roots θ mem :
  repr_mem θ ∅ mem mem.
Proof.
  exists ∅. split_and!.
  - apply repr_roots_empty.
  - apply map_disjoint_dom; set_solver.
  - rewrite left_id_L//.
Qed.

Lemma repr_roots_empty_inv_1 θ mem :
  repr_roots θ ∅ mem →
  mem = ∅.
Proof.
  inversion 1; simplify_eq; eauto.
  by eapply insert_non_empty in H0.
Qed.

Lemma repr_roots_lookup θ a lv roots mem :
  roots !! a = Some lv →
  repr_roots θ roots mem →
  ∃ w, mem !! a = Some (Storing w) ∧ repr_lval θ lv w.
Proof.
  intros Ha Hrepr. revert a lv Ha. induction Hrepr; first by set_solver.
  intros a' lv' Ha'.
  destruct (decide (a = a')) as [<-|]; simplify_map_eq; eauto.
Qed.

Lemma repr_roots_insert θ a lv w roots mem :
  a ∉ dom roots →
  repr_lval θ lv w →
  repr_roots θ roots mem →
  repr_roots θ (<[a:=lv]> roots) (<[a:=Some (Some w)]> mem).
Proof.
  intros Ha Hrepr Hr. constructor; eauto. erewrite <- repr_roots_dom; eauto.
Qed.

Lemma repr_roots_delete θ a lv roots mem :
  roots !! a = Some lv →
  repr_roots θ roots mem →
  repr_roots θ (delete a roots) (delete a mem).
Proof.
  intros Ha Hrepr. revert a lv Ha. induction Hrepr; first by set_solver.
  intros a' lv' Ha'.
  destruct (decide (a = a')) as [<-|]; simplify_map_eq.
  { rewrite !delete_insert_delete//.
    rewrite !delete_notin//; by apply not_elem_of_dom. }
  { rewrite !delete_insert_ne //. constructor; eauto.
    all: rewrite dom_delete_L; set_solver. }
Qed.

Lemma repr_roots_inj_2 θ roots mem mem' :
  repr_roots θ roots mem →
  repr_roots θ roots mem' →
  mem = mem'.
Proof.
  intros Hrepr1. revert mem'. induction Hrepr1.
  { by intros ? ->%repr_roots_empty_inv_1. }
  intros mem' Hrepr.
  edestruct repr_roots_lookup as (w'&Hw'&Hvw');
    [eapply lookup_insert|eassumption|].
  apply map_eq_iff. intros i.
  destruct (decide (i = a)) as [->|]; simplify_map_eq.
  { by pose proof (repr_lval_inj _ _ _ _ Hvw' H) as ->. }
  eapply (repr_roots_delete _ a) in Hrepr.
  2: by eapply lookup_insert.
  rewrite delete_insert_delete delete_notin in Hrepr.
  2: by eapply not_elem_of_dom.
  apply IHHrepr1 in Hrepr; subst mem.
  rewrite lookup_delete_ne//.
Qed.

Lemma lval_in_vblock v m tg vs :
  lval_in_block (Bvblock (m, (tg, vs))) v ↔ v ∈ vs.
Proof. split. by inversion 1. intros; by constructor. Qed.

Lemma GC_correct_transport ζ1 ζ2 θ : freeze_lstore ζ1 ζ2 → GC_correct ζ1 θ → GC_correct ζ2 θ.
Proof.
  intros (H1L&H1R) (H2&H3). split; first done.
  intros γ blk γ' HH1 HH2 HH3.
  destruct (ζ1 !! γ) as [b|] eqn:Heq.
  2: { eapply elem_of_dom_2 in HH2. eapply not_elem_of_dom in Heq. rewrite H1L in Heq; tauto. }
  specialize (H1R _ _ _ Heq HH2). inversion H1R; subst.
  3: { eapply H3; done. }
  destruct tgvs. eapply lval_in_vblock in HH3.
  eapply H3. 1: exact HH1. 1: done. eapply lval_in_vblock. done.
  inversion HH3.
Qed.

Lemma GC_correct_transport_rev ζ1 ζ2 θ : freeze_lstore ζ2 ζ1 → GC_correct ζ1 θ → GC_correct ζ2 θ.
Proof.
  intros (H1L&H1R) (H2&H3). split; first done.
  intros γ blk γ' HH1 HH2 HH3.
  destruct (ζ1 !! γ) as [b|] eqn:Heq.
  2: { eapply elem_of_dom_2 in HH2. eapply not_elem_of_dom in Heq. rewrite -H1L in Heq; tauto. }
  specialize (H1R _ _ _ HH2 Heq). inversion H1R; subst.
  3: { eapply H3; done. }
  destruct tgvs. eapply lval_in_vblock in HH3.
  eapply H3. 1: exact HH1. 1: done. eapply lval_in_vblock. done.
  inversion HH3.
Qed.

Lemma GC_correct_modify_block ζ θ γ blk blk' i v w :
  ζ !! γ = Some blk →
  modify_block blk i v blk' →
  repr_lval θ v w →
  GC_correct ζ θ →
  GC_correct (<[γ := blk']> ζ) θ.
Proof using.
  intros Hγ Hblk Hrepr [GC1 GC2]. split; first done.
  intros γ0 blk1 γ1 Hγ0 [[??]|[Hne1 Hlu]]%lookup_insert_Some Hlloc.
  2: { by eapply GC2. }
  simplify_eq. inversion Hblk; subst.
  apply lval_in_vblock, list_insert_lookup_inv in Hlloc as [HLL|HRR];
    simplify_map_eq.
  { inversion Hrepr; subst. by eapply elem_of_dom_2. }
  { eapply GC2; eauto. by constructor. }
Qed.

Lemma GC_correct_modify_foreign ζ θ γ blk blk' :
  ζ !! γ = Some (Bforeign blk) →
  GC_correct ζ θ →
  GC_correct (<[γ := Bforeign blk']> ζ) θ.
Proof using.
  intros Hγ [GC1 GC2]. split; first done.
  intros γ0 blk1 γ1 Hγ0 [[??]|[Hne1 Hlu]]%lookup_insert_Some Hlloc; subst; eauto.
  by inversion Hlloc.
Qed.

Lemma GC_correct_gmap_inj ζ θ :
  GC_correct ζ θ →
  gmap_inj θ.
Proof. intros H; apply H. Qed.
Global Hint Resolve GC_correct_gmap_inj : core.

Lemma roots_are_live_empty θ : roots_are_live θ ∅.
Proof. intros ? ?. rewrite lookup_empty//. Qed.

Lemma roots_are_live_insert a lv w θ roots_m :
  repr_lval θ lv w →
  roots_are_live θ roots_m →
  roots_are_live θ (<[a:=lv]> roots_m).
Proof.
  intros Hrepr Hlive a' γ Ha'. destruct (decide (a = a')) as [<-|].
  { simplify_map_eq. inversion Hrepr; simplify_eq. by apply elem_of_dom. }
  { simplify_map_eq. eapply Hlive; eauto. }
Qed.

Lemma roots_are_live_delete a θ roots_m :
  roots_are_live θ roots_m →
  roots_are_live θ (delete a roots_m).
Proof.
  intros Hlive ℓ γ [HH1 HH2]%lookup_delete_Some; by eapply Hlive.
Qed.

(******************************************************************************)
(* auxiliary hints & tactics *)

Global Hint Constructors repr_lval : core.

Ltac inv_repr_lval :=
  progress repeat match goal with
  | H : repr_lval _ (Lloc _) _ |- _ =>
      inversion H; subst; clear H
  | H : repr_lval _ (Lint _) _ |- _ =>
      inversion H; subst; clear H
  end.

Ltac inv_modify_block :=
  match goal with
  | H : modify_block _ _ _ _ |- _ =>
      inversion H; simplify_eq; clear H
  end.

Ltac repr_lval_inj :=
  progress repeat match goal with
  | Hinj : gmap_inj ?θ,
    Hr1 : repr_lval ?θ ?v ?w,
    Hr2 : repr_lval ?θ ?v' ?w |- _ =>
      pose proof (repr_lval_inj_1 _ _ _ _ Hinj Hr1 Hr2); subst v'; clear Hr2
  | Hr1 : repr_lval _ ?v ?w,
    Hr2 : repr_lval _ ?v ?w' |- _ =>
      pose proof (repr_lval_inj _ _ _ _ Hr1 Hr2); subst w'; clear Hr2
  end.
