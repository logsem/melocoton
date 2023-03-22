From Coq Require Import ssreflect.
From stdpp Require Import strings gmap list.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props.
From melocoton.ml_lang Require Import lang_instantiation primitive_laws.
From melocoton.interop Require Export prims.
From melocoton.interop Require Import basics_resources gctoken prims.

Section PrimsProto.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGCtokGS Σ}.

Notation C_proto := (string -d> list C_intf.val -d> (C_intf.val -d> iPropO Σ) -d> iPropO Σ).
Notation ML_proto := (string -d> list ML_lang.val -d> (ML_lang.val -d> iPropO Σ) -d> iPropO Σ).

Local Notation prim_proto := (list C_intf.val -d> (C_intf.val -d> iPropO Σ) -d> iPropO Σ).

Definition proto_int2val : prim_proto := (λ vl Φ,
   ∃ θ z,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜vl = [C_intf.LitV $ C_intf.LitInt $ z]⌝ ∗
     "Cont" ∷ ▷ (∀ w, GC θ -∗ ⌜repr_lval θ (Lint z) w⌝ -∗ Φ w))%I.

Definition proto_val2int : prim_proto := (λ vl Φ,
   ∃ θ w z,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜vl = [ w ]⌝ ∗
     "%Hrepr" ∷ ⌜repr_lval θ (Lint z) w⌝ ∗
     "Cont" ∷ ▷ (GC θ -∗ Φ (C_intf.LitV $ C_intf.LitInt $ z)))%I.

Definition proto_registerroot : prim_proto := (λ vl Φ,
   ∃ θ l v w,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜vl = [ C_intf.LitV $ C_intf.LitLoc $ l ]⌝ ∗
     "Hpto" ∷ l ↦C w ∗
     "%Hrepr" ∷ ⌜repr_lval θ v w⌝ ∗
     "Cont" ∷ ▷ (GC θ -∗ l ↦roots v -∗ Φ (C_intf.LitV $ C_intf.LitInt $ 0)))%I.

Definition proto_unregisterroot : prim_proto := (λ vl Φ,
   ∃ θ l v,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜vl = [ C_intf.LitV $ C_intf.LitLoc $ l ]⌝ ∗
     "Hpto" ∷ l ↦roots v ∗
     "Cont" ∷ ▷ (∀ w, GC θ -∗ l ↦C w -∗ ⌜repr_lval θ v w⌝ -∗ Φ (C_intf.LitV $ C_intf.LitInt $ 0)))%I.

Definition proto_modify : prim_proto := (λ vl Φ,
  ∃ θ w i v' w' γ mut tg vs,
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜vl = [ w; C_intf.LitV $ C_intf.LitInt $ i; w' ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "%Hptomut" ∷ ⌜vblock_access_le M mut⌝ ∗
    "Hpto" ∷ γ ↦vblk[mut] (tg, vs) ∗
    "%Hreprw'" ∷ ⌜repr_lval θ v' w'⌝ ∗
    "%Hi1" ∷ ⌜0 ≤ i⌝%Z ∗
    "%Hi2" ∷ ⌜i < length vs⌝%Z ∗
    "Cont" ∷ ▷ (GC θ -∗
                 γ ↦vblk[mut] (tg, <[Z.to_nat i:=v']> vs) -∗
                 Φ (C_intf.LitV $ C_intf.LitInt $ 0)))%I.

Definition proto_readfield : prim_proto := (λ vl Φ,
   ∃ θ w i γ dq m tg vs,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜vl = [ w; C_intf.LitV $ C_intf.LitInt $ i ]⌝ ∗
     "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
     "Hpto" ∷ γ ↦vblk[m]{dq} (tg, vs) ∗
     "%Hi1" ∷ ⌜0 ≤ i⌝%Z ∗
     "%Hi2" ∷ ⌜i < length vs⌝%Z ∗
     "Cont" ∷ ▷ (∀ v' w', GC θ -∗
                           γ ↦vblk[m]{dq} (tg, vs) -∗
                           ⌜vs !! (Z.to_nat i) = Some v'⌝ -∗
                           ⌜repr_lval θ v' w'⌝ -∗
                           Φ w'))%I.

Definition proto_alloc : prim_proto := (λ vl Φ,
   ∃ θ tg sz,
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜vl = [ C_intf.LitV $ C_intf.LitInt $ vblock_tag_as_int $ tg; C_intf.LitV $ C_intf.LitInt $ sz ]⌝ ∗
     "%Hsz" ∷ ⌜0 ≤ sz⌝%Z ∗
     "Cont" ∷ ▷ (∀ θ' γ w, GC θ' -∗
                            γ ↦fresh (tg, List.repeat (Lint 0) (Z.to_nat sz)) -∗
                            ⌜repr_lval θ' (Lloc γ) w⌝ -∗
                            Φ w))%I.

Definition proto_alloc_foreign : prim_proto := (λ vl Φ,
  ∃ θ a,
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜vl = [ C_intf.LitV (C_intf.LitLoc a) ]⌝ ∗
    "Cont" ∷ ▷ (∀ θ' γ w, GC θ' -∗
                           γ ↦foreign a -∗
                           ⌜repr_lval θ' (Lloc γ) w⌝ -∗
                           Φ w))%I.

Definition proto_write_foreign : prim_proto := (λ vl Φ,
  ∃ θ γ w a a',
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜vl = [ w; C_intf.LitV (C_intf.LitLoc a') ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hpto" ∷ γ ↦foreign a ∗
    "Cont" ∷ ▷ (GC θ -∗
                 γ ↦foreign a' -∗
                 Φ (C_intf.LitV (C_intf.LitInt 0))))%I.

Definition proto_read_foreign : prim_proto := (λ vl Φ,
  ∃ θ γ w a,
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜vl = [ w ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hpto" ∷ γ ↦foreign a ∗
    "Cont" ∷ ▷ (GC θ -∗
                 γ ↦foreign a -∗
                 Φ (C_intf.LitV (C_intf.LitLoc a))))%I.

Definition proto_callback E (T : ML_proto) : prim_proto := (λ vl Φ,
  ∃ θ w γ w' lv' v' f x e ψ,
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜vl = [ w; w' ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hclos" ∷ γ ↦clos (f, x, e) ∗
    "%Hreprw'" ∷ ⌜repr_lval θ lv' w'⌝ ∗
    "Hsim'" ∷ lv' ~~ v' ∗
    "WPcallback" ∷ ▷ WP (App (Val (RecV f x e)) (Val v')) @ ⟨∅, T⟩ ; E {{ ψ }} ∗
    "Cont" ∷ ▷ (∀ θ' vret lvret wret,
                   GC θ' -∗
                   ψ vret -∗
                   lvret ~~ vret -∗
                   ⌜repr_lval θ' lvret wret⌝ -∗
                   Φ wret))%I.

Definition proto_prim (p : prim) E (T : ML_proto) : prim_proto :=
  match p with
  | Pint2val => proto_int2val
  | Pval2int => proto_val2int
  | Pregisterroot => proto_registerroot
  | Punregisterroot => proto_unregisterroot
  | Pmodify => proto_modify
  | Preadfield => proto_readfield
  | Palloc => proto_alloc
  | Pallocforeign => proto_alloc_foreign
  | Pwriteforeign => proto_write_foreign
  | Preadforeign => proto_read_foreign
  | Pcallback => proto_callback E T
  end.

Definition proto_prims_in_C E (T : ML_proto) : C_proto := (λ f vs Φ,
  ∃ p, ⌜is_prim f p⌝ ∗ proto_prim p E T vs Φ
)%I.

Lemma proto_prim_mask_mono E1 E2 T : E1 ⊆ E2 →
  ∀ p vl Φ, proto_prim p E1 T vl Φ -∗ proto_prim p E2 T vl Φ.
Proof using.
  iIntros (H p vl Φ) "H". destruct p; try done.
  iNamed "H". do 10 iExists _; unfold named.
  iFrame. do 3 (iSplit; first done).
  iNext. iApply @wp_mask_mono. 1: done.
  iFrame.
Qed.

End PrimsProto.

(* TODO: move? *)
Notation C_proto Σ := (string -d> list C_intf.val -d> (C_intf.val -d> iPropO Σ) -d> iPropO Σ).
Notation ML_proto Σ := (string -d> list ML_lang.val -d> (ML_lang.val -d> iPropO Σ) -d> iPropO Σ).
