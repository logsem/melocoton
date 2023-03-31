From Coq Require Import ssreflect.
From stdpp Require Import strings gmap list.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props.
From melocoton.ml_lang Require Import lang_instantiation primitive_laws.
From melocoton.interop Require Export prims.
From melocoton.interop Require Import basics_resources gctoken prims.

Section PrimsProto.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperGCtokG Σ}.

Notation C_proto := (protocol C_intf.val Σ).
Notation ML_proto := (protocol ML_lang.val Σ).

(* TODO: move *)
Definition wrap_proto (Ψ : ML_proto) : C_proto := (λ f ws Φ,
  ∃ θ vs lvs Φ',
    "HGC" ∷ GC θ ∗
    "%Hrepr" ∷ ⌜Forall2 (repr_lval θ) lvs ws⌝ ∗
    "Hsim" ∷ lvs ~~∗ vs ∗
    "Hproto" ∷ Ψ f vs Φ' ∗
    "Cont" ∷ ▷ (∀ θ' vret lvret wret,
      GC θ' -∗
      Φ' vret -∗
      lvret ~~ vret -∗
      ⌜repr_lval θ' lvret wret⌝ -∗
      Φ wret)
)%I.

Lemma wrap_proto_mono Ψ Ψ' : Ψ ⊑ Ψ' → wrap_proto Ψ ⊑ wrap_proto Ψ'.
Proof using.
  iIntros (Hre ? ? ?) "H". unfold wrap_proto. iNamed "H".
  rewrite /named. iExists _, _, _, _. iFrame. iSplit; first done.
  by iApply Hre.
Qed.

Definition int2val_proto : C_proto := (λ fn vl Φ,
   ∃ θ z,
     "->" ∷ ⌜fn = "int2val"⌝ ∗
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜vl = [C_intf.LitV $ C_intf.LitInt $ z]⌝ ∗
     "Cont" ∷ ▷ (∀ w, GC θ -∗ ⌜repr_lval θ (Lint z) w⌝ -∗ Φ w))%I.

Definition val2int_proto : C_proto := (λ fn vl Φ,
   ∃ θ w z,
     "->" ∷ ⌜fn = "val2int"⌝ ∗
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜vl = [ w ]⌝ ∗
     "%Hrepr" ∷ ⌜repr_lval θ (Lint z) w⌝ ∗
     "Cont" ∷ ▷ (GC θ -∗ Φ (C_intf.LitV $ C_intf.LitInt $ z)))%I.

Definition registerroot_proto : C_proto := (λ fn vl Φ,
   ∃ θ l v w,
     "->" ∷ ⌜fn = "registerroot"⌝ ∗
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜vl = [ C_intf.LitV $ C_intf.LitLoc $ l ]⌝ ∗
     "Hpto" ∷ l ↦C w ∗
     "%Hrepr" ∷ ⌜repr_lval θ v w⌝ ∗
     "Cont" ∷ ▷ (GC θ -∗ l ↦roots v -∗ Φ (C_intf.LitV $ C_intf.LitInt $ 0)))%I.

Definition unregisterroot_proto : C_proto := (λ fn vl Φ,
   ∃ θ l v,
     "->" ∷ ⌜fn = "unregisterroot"⌝ ∗
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜vl = [ C_intf.LitV $ C_intf.LitLoc $ l ]⌝ ∗
     "Hpto" ∷ l ↦roots v ∗
     "Cont" ∷ ▷ (∀ w, GC θ -∗ l ↦C w -∗ ⌜repr_lval θ v w⌝ -∗ Φ (C_intf.LitV $ C_intf.LitInt $ 0)))%I.

Definition modify_proto : C_proto := (λ fn vl Φ,
  ∃ θ w i v' w' γ mut tg vs,
    "->" ∷ ⌜fn = "modify"⌝ ∗
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

Definition readfield_proto : C_proto := (λ fn vl Φ,
   ∃ θ w i γ dq m tg vs,
     "->" ∷ ⌜fn = "readfield"⌝ ∗
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

Definition alloc_proto : C_proto := (λ fn vl Φ,
   ∃ θ tg sz,
     "->" ∷ ⌜fn = "alloc"⌝ ∗
     "HGC" ∷ GC θ ∗
     "->" ∷ ⌜vl = [ C_intf.LitV $ C_intf.LitInt $ vblock_tag_as_int $ tg; C_intf.LitV $ C_intf.LitInt $ sz ]⌝ ∗
     "%Hsz" ∷ ⌜0 ≤ sz⌝%Z ∗
     "Cont" ∷ ▷ (∀ θ' γ w, GC θ' -∗
                            γ ↦fresh (tg, List.repeat (Lint 0) (Z.to_nat sz)) -∗
                            ⌜repr_lval θ' (Lloc γ) w⌝ -∗
                            Φ w))%I.

Definition alloc_foreign_proto : C_proto := (λ fn vl Φ,
  ∃ θ,
    "->" ∷ ⌜fn = "alloc_foreign"⌝ ∗
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜vl = [ ]⌝ ∗
    "Cont" ∷ ▷ (∀ θ' γ w, GC θ' -∗
                          γ ↦foreignO None -∗
                          ⌜repr_lval θ' (Lloc γ) w⌝ -∗
                          Φ w))%I.

Definition write_foreign_proto : C_proto := (λ fn vl Φ,
  ∃ θ γ w wo w',
    "->" ∷ ⌜fn = "write_foreign"⌝ ∗
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜vl = [ w; w' ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hpto" ∷ γ ↦foreignO wo ∗
    "Cont" ∷ ▷ (GC θ -∗
                 γ ↦foreign w' -∗
                 Φ (C_intf.LitV (C_intf.LitInt 0))))%I.

Definition read_foreign_proto : C_proto := (λ fn vl Φ,
  ∃ θ γ w w',
    "->" ∷ ⌜fn = "read_foreign"⌝ ∗
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜vl = [ w ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hpto" ∷ γ ↦foreign w' ∗
    "Cont" ∷ ▷ (GC θ -∗
                 γ ↦foreign w' -∗
                 Φ w'))%I.

Definition callback_proto E (Ψ : ML_proto) : C_proto := (λ fn vl Φ,
  ∃ θ w γ w' lv' v' f x e Φ',
    "->" ∷ ⌜fn = "callback"⌝ ∗
    "HGC" ∷ GC θ ∗
    "->" ∷ ⌜vl = [ w; w' ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hclos" ∷ γ ↦clos (f, x, e) ∗
    "%Hreprw'" ∷ ⌜repr_lval θ lv' w'⌝ ∗
    "Hsim'" ∷ lv' ~~ v' ∗
    "WPcallback" ∷ ▷ WP (App (Val (RecV f x e)) (Val v')) @ ⟨∅, Ψ⟩ ; E {{ Φ' }} ∗
    "Cont" ∷ ▷ (∀ θ' vret lvret wret,
                   GC θ' -∗
                   Φ' vret -∗
                   lvret ~~ vret -∗
                   ⌜repr_lval θ' lvret wret⌝ -∗
                   Φ wret))%I.

Definition main_proto (E: coPset) (e : ML_lang.expr) (Ψ : ML_proto) : C_proto := (λ fn vl Φ,
  ∃ Φ',
  "->" ∷ ⌜fn = "main"⌝ ∗
  "->" ∷ ⌜vl = []⌝ ∗
  "Hat_init" ∷ at_init ∗
  "WPmain" ∷ ▷ WP e @ ⟨∅, Ψ⟩; E {{ Φ' }} ∗
  "Cont" ∷ ▷ (∀ θ' vret lvret wret,
                   GC θ' -∗
                   Φ' vret -∗
                   lvret ~~ vret -∗
                   ⌜repr_lval θ' lvret wret⌝ -∗
                   Φ wret)
  )%I.

Definition prim_proto (p : prim) E (Ψ : ML_proto) : C_proto :=
  match p with
  | Pint2val => int2val_proto
  | Pval2int => val2int_proto
  | Pregisterroot => registerroot_proto
  | Punregisterroot => unregisterroot_proto
  | Pmodify => modify_proto
  | Preadfield => readfield_proto
  | Palloc => alloc_proto
  | Pallocforeign => alloc_foreign_proto
  | Pwriteforeign => write_foreign_proto
  | Preadforeign => read_foreign_proto
  | Pcallback => callback_proto E Ψ
  | Pmain e => main_proto E e Ψ
  end.

Definition prims_proto E e (Ψ : ML_proto) : C_proto :=
  (λ fn vs Φ, ∃ p, ⌜prims_prog e !! fn = Some p⌝ ∗
    prim_proto p E Ψ fn vs Φ)%I.

Lemma proto_prim_mask_mono E1 E2 e Ψ : E1 ⊆ E2 →
  ∀ fn vl Φ, prims_proto E1 e Ψ fn vl Φ -∗ prims_proto E2 e Ψ fn vl Φ.
Proof using.
  iIntros (H fn vl Φ) "H". iDestruct "H" as (p Hp) "H". iExists p.
  iSplit; first done.
  destruct p; try done. all: cbn; iNamed "H".
  { do 10 iExists _; unfold named.
    iFrame. do 4 (iSplit; first done).
    iNext. iApply wp_mask_mono. 1: done.
    iFrame. }
  { unfold main_proto, named. iExists Φ'. iFrame. do 2 (iSplit; first done).
    iNext. iApply wp_mask_mono; first done. iFrame. }
Qed.

Lemma prims_proto_except_dom E e Ψ :
  (prims_proto E e Ψ) except (dom (prims_prog e)) ⊑ ⊥.
Proof using.
  iIntros (? ? ?) "H". rewrite /proto_except.
  iDestruct "H" as (Hdom p ?) "H".
  apply not_elem_of_dom in Hdom.
  destruct p; unfold prim_proto; iNamed "H"; by exfalso.
Qed.

(* some boilerplate *)
Local Ltac tac p :=
  iIntros (? ? ?) "H"; iExists p; (iSplit; last iFrame); by iNamed "H".
Lemma int2val_refines_prims_proto E e Ψ : int2val_proto ⊑ prims_proto E e Ψ.
Proof using. tac Pint2val. Qed.
Lemma val2int_refines_prims_proto E e Ψ : val2int_proto ⊑ prims_proto E e Ψ.
Proof using. tac Pval2int. Qed.
Lemma registerroot_refines_prims_proto E e Ψ : registerroot_proto ⊑ prims_proto E e Ψ.
Proof using. tac Pregisterroot. Qed.
Lemma unregisterroot_refines_prims_proto E e Ψ : unregisterroot_proto ⊑ prims_proto E e Ψ.
Proof using. tac Punregisterroot. Qed.
Lemma modify_refines_prims_proto E e Ψ : modify_proto ⊑ prims_proto E e Ψ.
Proof using. tac Pmodify. Qed.
Lemma readfield_refines_prims_proto E e Ψ : readfield_proto ⊑ prims_proto E e Ψ.
Proof using. tac Preadfield. Qed.
Lemma alloc_refines_prims_proto E e Ψ : alloc_proto ⊑ prims_proto E e Ψ.
Proof using. tac Palloc. Qed.
Lemma alloc_foreign_refines_prims_proto E e Ψ : alloc_foreign_proto ⊑ prims_proto E e Ψ.
Proof using. tac Pallocforeign. Qed.
Lemma write_foreign_refines_prims_proto E e Ψ : write_foreign_proto ⊑ prims_proto E e Ψ.
Proof using. tac Pwriteforeign. Qed.
Lemma read_foreign_refines_prims_proto E e Ψ : read_foreign_proto ⊑ prims_proto E e Ψ.
Proof using. tac Preadforeign. Qed.
Lemma callback_refines_prims_proto E e Ψ : callback_proto E Ψ ⊑ prims_proto E e Ψ.
Proof using. tac Pcallback. Qed.
Lemma main_refines_prims_proto E e Ψ : main_proto E e Ψ ⊑ prims_proto E e Ψ.
Proof using. tac (Pmain e). Qed.

End PrimsProto.

Global Hint Resolve int2val_refines_prims_proto : core.
Global Hint Resolve val2int_refines_prims_proto : core.
Global Hint Resolve registerroot_refines_prims_proto : core.
Global Hint Resolve unregisterroot_refines_prims_proto : core.
Global Hint Resolve modify_refines_prims_proto : core.
Global Hint Resolve readfield_refines_prims_proto : core.
Global Hint Resolve alloc_refines_prims_proto : core.
Global Hint Resolve alloc_foreign_refines_prims_proto : core.
Global Hint Resolve write_foreign_refines_prims_proto : core.
Global Hint Resolve read_foreign_refines_prims_proto : core.
Global Hint Resolve callback_refines_prims_proto : core.
Global Hint Resolve main_refines_prims_proto : core.
