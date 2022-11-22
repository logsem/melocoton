From Coq Require Import ZArith.
From stdpp Require Import base gmap list.
From melocoton.c_toy_lang Require Import lang.
From melocoton.ml_toy_lang Require Import lang.

(* the type of memory addresses used by the C semantics *)
Notation addr := iris.heap_lang.locations.loc (only parsing).
(* We call "mem" a C memory and "word" a C value. *)
Notation memory := C_lang.state.
Notation word := C_lang.val.
(* We call "store" an ML memory and "val" an ML value. *)
Notation store := ML_lang.state.
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
  ∀ γ b1 b2, ζ1 !! γ = Some b1 → ζ2 !! γ = Some b2 →
    freeze_block b1 b2.

(* which block-level changes can happen as the result of execution in the
   "outside world"? answer: only changes to the contents of mutable blocks.

   There is nothing deep here, this is mostly an administrative constraint:
   external code does not have access to the extra information (immutable
   blocks, blocks tags, etc) which are part of the wrapper private state ; so
   indeed, it cannot change it.
*)
Inductive ML_change_block : block → block → Prop :=
  | mk_ML_change_block tg vs vs' :
    length vs = length vs' →
    ML_change_block (Mut, tg, vs) (Mut, tg, vs').

Definition ML_change_lstore (χ : lloc_map) (ζ1 ζ2 : lstore) : Prop :=
  dom ζ1 ⊆ dom ζ2 ∧
  ∀ γ b1 b2, ζ1 !! γ = Some b1 → ζ2 !! γ = Some b2 →
    (b1 = b2 ∨ (∃ ℓ, χ !! ℓ = Some γ ∧ ML_change_block b1 b2)).

(* Running external code can allocate new memory, which then needs to be
   registered in χ. This is a sanity condition for the corresponding new χ: it
   must not "capture" logical locations that were already used in the store for
   immutable blocks. *)
Definition ML_extends_lloc_map (ζ : lstore) (χ1 χ2 : lloc_map) : Prop :=
  χ1 ⊆ χ2 ∧
  ∀ ℓ γ, χ1 !! ℓ = None → χ2 !! ℓ = Some γ → ζ !! γ = None.

(* Helper relation to modify the contents of a block at a given index (which has
   to be in the bounds). *)
Inductive modify_block : block → nat → lval → block → Prop :=
  | mk_modify_block tg vs i v :
    i < length vs →
    modify_block (Mut, tg, vs) i v (Mut, tg, (<[ i := v ]> vs)).

(* Reachability. Needed to describe the effect of the GC on the map θ: after a
   GC, everything that is reachable from the roots (in the logical store) is
   still in the domain of θ (i.e. has not been deallocated). *)

(* TODO: unclear whether it is simpler to define reachability wrt a list of
   values (as is done below) or a single value. *)
Inductive reachable : lstore → list lval → lloc → Prop :=
  | reachable_invals ζ γ vs :
    Lloc γ ∈ vs →
    reachable ζ vs γ
  | reachable_instore ζ vs γ γ' bvs m :
    reachable ζ vs γ' →
    ζ !! γ' = Some (m, bvs) →
    Lloc γ ∈ bvs →
    reachable ζ vs γ.

(* NB: the induction case for this definition of reachability where one takes a step last:

   reachable = -->* -->

   TODO: prove an alternative induction principle that corresponds to the
   induction where one does a step first:

   reachable = --> -->*
*)

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

Definition is_block_store (χ : lloc_map) (ζ : lstore) (σ : store) : Prop :=
  dom σ = dom χ ∧
  ∀ ℓ vs, σ !! ℓ = Some vs →
    ∃ γ blk, χ !! ℓ = Some γ ∧
             ζ !! γ = Some blk ∧
             is_heap_elt χ ζ vs blk.

Definition is_store (χ : lloc_map) (ζ : lstore) (privσ σ : store) : Prop :=
  ∃ σbks, is_block_store χ ζ σbks ∧
  privσ ##ₘ σbks ∧
  σ = σbks ∪ privσ.

End basics.
