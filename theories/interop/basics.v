From Coq Require Import ZArith.
From stdpp Require Import base gmap list.
From melocoton Require Import commons.
From melocoton.c_toy_lang Require Import lang.
From melocoton.ml_toy_lang Require Import lang.

(* the type of memory addresses used by the C semantics *)
Notation addr := iris.heap_lang.locations.loc (only parsing).
(* We call "mem" a C memory and "word" a C value. *)
Notation memory := C_lang.state.
Notation word := C_lang.val.
(* We call "store" an ML memory and "val" an ML value. *)
(* Notation store := ML_lang.state. *)
(* FIXME temporary: need to update ML_lang.state *)
Notation store := (gmap loc (option (list val))).
Notation val := ML_lang.val.

Section basics.

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
Definition lloc : Type := nat.
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

Instance tag_as_int_inj : Inj (=) (=) tag_as_int.
Proof using. intros t t'. destruct t; destruct t'; by inversion 1. Qed.

(* a block in the block-level store *)
Definition block :=
  (ismut * tag * list lval)%type.

(* a block-level store *)
Definition lstore : Type := gmap lloc block.
Implicit Type ζ : lstore.


(************
   In order to tie the logical block-level store to the ML and C stores, the
   wrapper also maintains a number of mappings, that e.g. relate ML locations to
   block-level locations. *)

(* maps an ML location to its corresponding logical location *)
Definition lloc_map : Type := gmap loc lloc.
Implicit Type χ : lloc_map.

(* maps a logical location to its address in C memory.
   Note: since blocks do not move around in the logical store, even though they
   *are* moved around by the GC in the actual memory, this means that "the
   current θ" will often arbitrarily change during the execution, each time a GC
   might occur. *)
Definition addr_map : Type := gmap lloc addr.
Implicit Type θ : addr_map.

(* maps each root (a heap cell in C memory) to the logical value it is tracking
   and keeping alive *)
Definition roots_map : Type := gmap addr lval.


(************
   Block-level state changes.

   These relations define various transitions that might need to happen on the
   logical store; these are used to define the wrapper semantics.
*)

(* freezing: turning a mutable block into an immutable block. (This is typically
   only legal as long as the mutable block has not been "observable" by other
   code than the wrapper..) *)
Inductive freeze_block : block → block → Prop :=
  | freeze_block_mut vs tg m' :
    freeze_block (Mut, tg, vs) (m', tg, vs)
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

(* This is a sanity condition for a new χ2 that will be used to extend the store
   with new blocks, with respect to a previous χ1 and lstore ζ: it must not
   "capture" logical locations that were already present in the store. *)
Definition lloc_map_mono_fresh_in (ζ : lstore) (χ1 χ2 : lloc_map) : Prop :=
  ∀ ℓ γ, χ1 !! ℓ = None → χ2 !! ℓ = Some γ → ζ !! γ = None.

(* Helper relation to modify the contents of a block at a given index (which has
   to be in the bounds). Used to define the semantics of the "modify" primitive.
*)
Inductive modify_block : block → nat → lval → block → Prop :=
  | mk_modify_block tg vs i v :
    i < length vs →
    modify_block (Mut, tg, vs) i v (Mut, tg, (<[ i := v ]> vs)).

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
      ζ !! γ = Some (m, tg, vs) ∧
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
    ζ !! γ = Some (Immut, TagDefault, [lv1; lv2]) →
    is_val χ ζ v1 lv1 →
    is_val χ ζ v2 lv2 →
    is_val χ ζ (ML_lang.PairV v1 v2) (Lloc γ)
  (* sum-type constructors *)
  | is_val_injl χ ζ v lv γ :
    ζ !! γ = Some (Immut, TagDefault, [lv]) →
    is_val χ ζ v lv →
    is_val χ ζ (ML_lang.InjLV v) (Lloc γ)
  | is_val_injr χ ζ v lv γ :
    ζ !! γ = Some (Immut, TagInjRV, [lv]) →
    is_val χ ζ v lv →
    is_val χ ζ (ML_lang.InjRV v) (Lloc γ).

(* Elements of the ML store are lists of values representing refs and arrays;
   they correspond to a mutable block with the default tag. *)
Inductive is_heap_elt (χ : lloc_map) (ζ : lstore) : list val → block → Prop :=
| is_heap_elt_block vs lvs :
  Forall2 (is_val χ ζ) vs lvs →
  is_heap_elt χ ζ vs (Mut, TagDefault, lvs).

Definition is_store (χ : lloc_map) (ζ : lstore) (σ : store) : Prop :=
  ∀ ℓ vs γ blk,
    σ !! ℓ = Some (Some vs) → χ !! ℓ = Some γ → ζ !! γ = Some blk →
    is_heap_elt χ ζ vs blk.

End basics.
