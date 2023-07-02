From Coq Require Export ssreflect.
From stdpp Require Export prelude gmap numbers.
From iris.heap_lang Require Export locations.
Set Default Proof Using "Type".

(* A location + offset type, used to look up in the store type where each
   location is associated to a list of values *)

(* Code adapted from Cosmo https://gitlab.inria.fr/cambium/cosmo
   (theories/lang/model.v) *)

Notation offset := Z (only parsing).
Record locoff : Type := Locoff {
  locoff_loc : loc;
  locoff_off : offset;
}.

(* TODO remove *)
Declare Scope loc_scope.
Delimit Scope loc_scope with L.

Definition locoff_to_pair '(Locoff ℓ i) := (ℓ, i).
Definition pair_to_locoff '(ℓ, i) := Locoff ℓ i.
Global Instance pair_to_locoff_inj : Inj eq eq pair_to_locoff.
Proof. by intros [] [] [= -> ->]. Qed.
Global Instance locoff_to_pair_inj : Inj eq eq locoff_to_pair.
Proof. by intros [] [] [= -> ->]. Qed.
Global Instance locoff_eq_dec : EqDecision locoff.
Proof. eapply (inj_eq_dec locoff_to_pair). Defined.
Global Instance locoff_countable : Countable locoff.
Proof. apply (inj_countable' locoff_to_pair pair_to_locoff). by intros []. Qed.
Definition loc_to_locoff ℓ := Locoff ℓ 0.

Coercion loc_to_locoff : loc >-> locoff.
Notation "ℓ .[ i ]" := (Locoff ℓ i) (at level 2, i at level 200, left associativity, format "ℓ .[ i ]").


Bind Scope loc_scope with locoff.

Section store.
Context {val : Type}.

Local Notation store := (gmap loc ((list val))).

Global Instance store_lookup : Lookup locoff val store :=
  λ '(Locoff ℓ i) σ,
    if bool_decide (0 ≤ i)%Z then
      σ !! ℓ ≫=  λ (blk : list _), blk !! Z.to_nat i
    else None.

Global Instance store_insert : Insert locoff val store :=
  λ '(Locoff ℓ i) s σ,
    if bool_decide (0 ≤ i)%Z then
      match σ !! ℓ with
      | None     => σ
      | Some blk => <[ℓ := (<[Z.to_nat i := s]> blk)]> σ
      end
    else σ.

Lemma store_lookup_eq (σ : store) (ℓ : loc) (i : offset) :
  σ !! (ℓ.[i])%L =
    if bool_decide (0 ≤ i)%Z then
      σ !! ℓ ≫= λ (blk : list _), blk !! Z.to_nat i
    else None.
Proof. reflexivity. Qed.

Lemma store_lookup_insert (σ : store) (ℓi : locoff) (v0 v : val) :
  σ !! ℓi = Some v0 →
  <[ℓi := v]> σ !! ℓi = Some v.
Proof.
  destruct ℓi as [ℓ i]. rewrite /lookup /insert /=.
  case_bool_decide ; last done.
  case_match ; last done. cbn=>?.
  rewrite lookup_insert /= list_lookup_insert//. by eapply lookup_lt_Some.
Qed.

Lemma store_lookup_insert_ne (σ : store) (ℓi ℓi' : locoff) (v : val) :
  ℓi ≠ ℓi' →
  <[ℓi := v]> σ !! ℓi' = σ !! ℓi'.
Proof.
  destruct ℓi as [ℓ i], ℓi' as [ℓ' i']. rewrite /lookup /insert /=.
  intros ?. case_bool_decide ; last done.
  case_bool_decide ; last done.
  destruct (σ !! ℓ) as [blk|] eqn:Hσℓ ; last done.
  destruct (decide (ℓ = ℓ')) as [<-|].
  - destruct (decide (i = i')) as [<-|] ; first done.
    assert (Z.to_nat i ≠ Z.to_nat i') by lia.
    by rewrite Hσℓ lookup_insert /= list_lookup_insert_ne.
  - by rewrite lookup_insert_ne.
Qed.

Lemma store_insert_offset (σ : store) (ℓ : loc) (i : offset) (vs : list val) (w : val):
  σ !! ℓ = (Some vs) →
  (0 ≤ i < length vs)%Z →
  <[(ℓ.[i])%L := w]> σ = <[ℓ := (<[Z.to_nat i := w]> vs)]> σ.
Proof.
  intros Hvs Hi. rewrite /insert /store_insert -/(insert _ _ _).
  case_bool_decide; [|lia]. by simplify_map_eq.
Qed.

End store.
