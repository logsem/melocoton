From Coq Require Import ssreflect.
From stdpp Require Import strings gmap list.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props.
From melocoton.ml_lang Require Import lang_instantiation primitive_laws.
From melocoton.interop Require Import basics_resources gctoken prims.

Section PrimsProto.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperGCtokG Σ}.

(* XXX? *)
Notation mkPeML p T := ({| penv_prog := p; penv_proto := T |} : prog_environ ML_lang (_ : gFunctors)).

Notation prim_proto := (prim -d> list C_intf.val -d> (C_intf.val -d> iPropO Σ) -d> iPropO Σ).
Notation C_proto := (string -d> list C_intf.val -d> (C_intf.val -d> iPropO Σ) -d> iPropO Σ).
Notation ML_proto := (string -d> list ML_lang.val -d> (ML_lang.val -d> iPropO Σ) -d> iPropO Σ).

Definition proto_int2val : prim_proto := (λ p vl Φ,
   ∃ θ z,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜p = Pint2val⌝ ∗
     "->" ∷ ⌜vl = [C_intf.LitV $ C_intf.LitInt $ z]⌝ ∗
     "Cont" ∷ (∀ w, GC θ -∗ ⌜repr_lval θ (Lint z) w⌝ -∗ Φ w))%I.

Definition proto_val2int : prim_proto := (λ p vl Φ,
   ∃ θ w z,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜p = Pval2int⌝ ∗
     "->" ∷ ⌜vl = [ w ]⌝ ∗
     "%Hrepr" ∷ ⌜repr_lval θ (Lint z) w⌝ ∗
     "Cont" ∷ (GC θ -∗ Φ (C_intf.LitV $ C_intf.LitInt $ z)))%I.

Definition proto_registerroot : prim_proto := (λ p vl Φ,
   ∃ θ l v w,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜p = Pregisterroot⌝ ∗
     "->" ∷ ⌜vl = [ C_intf.LitV $ C_intf.LitLoc $ l ]⌝ ∗
     "Hpto" ∷ l ↦C w ∗
     "%Hrepr" ∷ ⌜repr_lval θ v w⌝ ∗
     "Cont" ∷ (GC θ -∗ l ↦roots v -∗ Φ (C_intf.LitV $ C_intf.LitInt $ 0)))%I.

Definition proto_unregisterroot : prim_proto := (λ p vl Φ,
   ∃ θ l v,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜p = Punregisterroot⌝ ∗
     "->" ∷ ⌜vl = [ C_intf.LitV $ C_intf.LitLoc $ l ]⌝ ∗
     "Hpto" ∷ l ↦roots v ∗
     "Cont" ∷ (∀w, GC θ -∗ l ↦C w -∗ ⌜repr_lval θ v w⌝ -∗ Φ (C_intf.LitV $ C_intf.LitInt $ 0)))%I.

Definition proto_modify : prim_proto := (λ p vl Φ,
  ∃ θ w i v' w' γ mut tg vs,
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜p = Pmodify⌝ ∗
    "->" ∷ ⌜vl = [ w; C_intf.LitV $ C_intf.LitInt $ i; w' ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "%Hptomut" ∷ ⌜vblock_access_le M mut⌝ ∗
    "Hpto" ∷ γ ↦vblk[mut] (tg, vs) ∗
    "%Hreprw'" ∷ ⌜repr_lval θ v' w'⌝ ∗
    "%Hi1" ∷ ⌜0 ≤ i⌝%Z ∗
    "%Hi2" ∷ ⌜i < length vs⌝%Z ∗
    "Cont" ∷ (GC θ -∗
              γ ↦vblk[mut] (tg, <[Z.to_nat i:=v']> vs) -∗
              Φ (C_intf.LitV $ C_intf.LitInt $ 0)))%I.

Definition proto_readfield : prim_proto := (λ p vl Φ,
   ∃ θ w i γ dq m tg vs,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜p = Preadfield⌝ ∗
     "->" ∷ ⌜vl = [ w; C_intf.LitV $ C_intf.LitInt $ i ]⌝ ∗
     "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
     "Hpto" ∷ γ ↦vblk[m]{dq} (tg, vs) ∗
     "%Hi1" ∷ ⌜0 ≤ i⌝%Z ∗
     "%Hi2" ∷ ⌜i < length vs⌝%Z ∗
     "Cont" ∷ (∀ v' w', GC θ -∗
                        γ ↦vblk[m]{dq} (tg, vs) -∗
                        ⌜vs !! (Z.to_nat i) = Some v'⌝ -∗
                        ⌜repr_lval θ v' w'⌝ -∗
                        Φ w'))%I.

Definition proto_alloc : prim_proto := (λ p vl Φ,
   ∃ θ tg sz,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜p = Palloc⌝ ∗
     "->" ∷ ⌜vl = [ C_intf.LitV $ C_intf.LitInt $ vblock_tag_as_int $ tg; C_intf.LitV $ C_intf.LitInt $ sz ]⌝ ∗
     "%Hsz" ∷ ⌜0 ≤ sz⌝%Z ∗
     "Cont" ∷ (∀ θ' γ w, GC θ' -∗
                         γ ↦fresh (tg, List.repeat (Lint 0) (Z.to_nat sz)) -∗
                         ⌜repr_lval θ' (Lloc γ) w⌝ -∗
                         Φ w))%I.

Definition proto_callback (E : coPset) (T : ML_proto) : prim_proto := (λ p vl Φ,
  ∃ θ w γ w' lv' v' f x e ψ,
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜p = Pcallback⌝ ∗
    "->" ∷ ⌜vl = [ w; w' ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hclos" ∷ γ ↦clos (f, x, e) ∗
    "%Hreprw'" ∷ ⌜repr_lval θ lv' w'⌝ ∗
    "Hsim'" ∷ lv' ~~ v' ∗
    "WPcallback" ∷ ▷ WP (App (Val (RecV f x e)) (Val v')) @ mkPeML ∅ T ; E {{ ψ }} ∗
    "Cont" ∷ (∀ θ' vret lvret wret,
                GC θ' -∗
                ψ vret -∗
                lvret ~~ vret -∗
                ⌜repr_lval θ' lvret wret⌝ -∗
                Φ wret))%I.

(* non-callbacks primitives *)
Definition proto_base_prims : prim_proto := (λ p vl Φ,
    proto_int2val p vl Φ ∨ proto_val2int p vl Φ ∨ proto_registerroot p vl Φ ∨ proto_unregisterroot p vl Φ
  ∨ proto_modify p vl Φ ∨ proto_readfield p vl Φ ∨ proto_alloc p vl Φ)%I.

Definition proto_prims E T : prim_proto := (λ p vl Φ,
  proto_base_prims p vl Φ ∨ proto_callback E T p vl Φ)%I.

Lemma proto_prims_mask_mono E1 E2 T : E1 ⊆ E2 →
  ∀ p vl Φ, proto_prims E1 T p vl Φ -∗ proto_prims E2 T p vl Φ.
Proof.
  iIntros (H p vl Φ) "[HL|HR]".
  1: by iLeft.
  iNamed "HR". iRight.
  do 10 iExists _; unfold named.
  iFrame. do 4 (iSplit; first done).
  iNext. iApply @wp_mask_mono. 1: done.
  iFrame.
Qed.

Definition proto_prims_in_C E (T : ML_proto) : C_proto := (λ f vs Φ,
  ∃ p, ⌜is_prim f p⌝ ∗ proto_prims E T p vs Φ
)%I.

End PrimsProto.
