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

Definition wrap_proto (Ψ : ML_proto) : C_proto := (λ f ws Φ,
  ∃ θ vs lvs Φ',
    "HGC" ∷ GC θ ∅ ∗
    "%Hrepr" ∷ ⌜Forall2 (repr_lval θ) lvs ws⌝ ∗
    "#Hsim" ∷ lvs ~~∗ vs ∗
    "Hproto" ∷ Ψ f vs Φ' ∗
    "Cont" ∷ (∀ θ' vret lvret wret,
      GC θ' ∅ -∗
      Φ' vret -∗
      lvret ~~ vret -∗
      ⌜repr_lval θ' lvret wret⌝ -∗
      Φ wret)
)%I.

Lemma wrap_proto_mono Ψ Ψ' : Ψ ⊑ Ψ' → wrap_proto Ψ ⊑ wrap_proto Ψ'.
Proof using.
  iIntros (Hre ? ? ?) "H". unfold wrap_proto. iNamed "H".
  rewrite /named. iExists _, _, _, _. iFrame. iFrame "Hsim". iSplit; first done.
  by iApply Hre.
Qed.

Definition int2val_proto : C_proto := (λ fn vl Φ,
   ∃ θ dirty z, 
     "->" ∷ ⌜fn = "int2val"⌝ ∗
     "HGC" ∷ GC θ dirty ∗
     "->" ∷ ⌜vl = [C_intf.LitV $ C_intf.LitInt $ z]⌝ ∗
     "Cont" ∷ ▷ (∀ w, GC θ dirty -∗ ⌜repr_lval θ (Lint z) w⌝ -∗ Φ w))%I.

Definition val2int_proto : C_proto := (λ fn vl Φ,
   ∃ θ dirty w z,
     "->" ∷ ⌜fn = "val2int"⌝ ∗
     "HGC" ∷ GC θ dirty ∗
     "->" ∷ ⌜vl = [ w ]⌝ ∗
     "%Hrepr" ∷ ⌜repr_lval θ (Lint z) w⌝ ∗
     "Cont" ∷ ▷ (GC θ dirty -∗ Φ (C_intf.LitV $ C_intf.LitInt $ z)))%I.

Definition registerroot_proto : C_proto := (λ fn vl Φ,
   ∃ θ dirty l v w,
     "->" ∷ ⌜fn = "registerroot"⌝ ∗
     "HGC" ∷ GC θ dirty ∗
     "->" ∷ ⌜vl = [ C_intf.LitV $ C_intf.LitLoc $ l ]⌝ ∗
     "Hpto" ∷ l ↦C w ∗
     "%Hrepr" ∷ ⌜repr_lval θ v w⌝ ∗
     "Cont" ∷ ▷ (GC θ dirty -∗ l ↦roots v -∗ Φ (C_intf.LitV $ C_intf.LitInt $ 0)))%I.

Definition unregisterroot_proto : C_proto := (λ fn vl Φ,
   ∃ θ dirty l v,
     "->" ∷ ⌜fn = "unregisterroot"⌝ ∗
     "HGC" ∷ GC θ dirty ∗
     "->" ∷ ⌜vl = [ C_intf.LitV $ C_intf.LitLoc $ l ]⌝ ∗
     "Hpto" ∷ l ↦roots v ∗
     "Cont" ∷ ▷ (∀ w, GC θ dirty -∗ l ↦C w -∗ ⌜repr_lval θ v w⌝ -∗ Φ (C_intf.LitV $ C_intf.LitInt $ 0)))%I.

Definition modify_proto : C_proto := (λ fn vl Φ,
  ∃ θ dirty w i v' w' γ mut tg vs,
    "->" ∷ ⌜fn = "modify"⌝ ∗
    "HGC" ∷ GC θ dirty ∗
    "->" ∷ ⌜vl = [ w; C_intf.LitV $ C_intf.LitInt $ i; w' ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "%Hptomut" ∷ ⌜vblock_access_le M mut⌝ ∗
    "Hpto" ∷ γ ↦vblk[mut] (tg, vs) ∗
    "Hv'safe" ∷ (∀ γ', ⌜v' = Lloc γ'⌝ → ∃ fid, γ' ~@~ fid) ∗
    "%Hreprw'" ∷ ⌜repr_lval θ v' w'⌝ ∗
    "%Hi1" ∷ ⌜0 ≤ i⌝%Z ∗
    "%Hi2" ∷ ⌜i < length vs⌝%Z ∗
    "Cont" ∷ ▷ (GC θ dirty -∗
                 γ ↦vblk[mut] (tg, <[Z.to_nat i:=v']> vs) -∗
                 Φ (C_intf.LitV $ C_intf.LitInt $ 0)))%I.

Definition readfield_proto : C_proto := (λ fn vl Φ,
   ∃ θ dirty w i γ dq m tg vs,
     "->" ∷ ⌜fn = "readfield"⌝ ∗
     "HGC" ∷ GC θ dirty ∗
     "->" ∷ ⌜vl = [ w; C_intf.LitV $ C_intf.LitInt $ i ]⌝ ∗
     "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
     "Hpto" ∷ γ ↦vblk[m]{dq} (tg, vs) ∗
     "%Hi1" ∷ ⌜0 ≤ i⌝%Z ∗
     "%Hi2" ∷ ⌜i < length vs⌝%Z ∗
     "Cont" ∷ ▷ (∀ v' w', GC θ dirty -∗
                           γ ↦vblk[m]{dq} (tg, vs) -∗
                           ⌜vs !! (Z.to_nat i) = Some v'⌝ -∗
                           ⌜repr_lval θ v' w'⌝ -∗
                           Φ w'))%I.

Definition isblock_proto : C_proto := (λ fn vl Φ,
   ∃ θ dirty lv w,
     "->" ∷ ⌜fn = "isblock"⌝ ∗
     "HGC" ∷ GC θ dirty ∗
     "->" ∷ ⌜vl = [ w ]⌝ ∗
     "%Hreprw" ∷ ⌜repr_lval θ lv w⌝ ∗
     "Cont" ∷ ▷ (GC θ dirty -∗ Φ (C_intf.LitV $ C_intf.LitInt 
                  (match lv with Lloc _ => 1 | _ => 0 end))))%I.

Definition read_tag_proto : C_proto := (λ fn vl Φ,
  ∃ θ dirty γ w dq bl tg,
    "->" ∷ ⌜fn = "read_tag"⌝ ∗
    "HGC" ∷ GC θ dirty ∗
    "->" ∷ ⌜vl = [ w ]⌝ ∗
    "->" ∷ ⌜tg = block_tag bl⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hpto" ∷ lstore_own_elem γ dq bl ∗
    "Cont" ∷ ▷ (GC θ dirty -∗
                 lstore_own_elem γ dq bl -∗
                 Φ (C_intf.LitV $ C_intf.LitInt $ (tag_as_int tg))))%I.

Definition length_proto : C_proto := (λ fn vl Φ,
  ∃ θ dirty γ w a dq bl,
    "->" ∷ ⌜fn = "length"⌝ ∗
    "HGC" ∷ GC θ dirty ∗
    "->" ∷ ⌜vl = [ w ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hpto" ∷ γ ↦vblk[ a ]{ dq } bl ∗
    "Cont" ∷ ▷ (GC θ dirty -∗
                 γ ↦vblk[ a ]{ dq } bl -∗
                 Φ (C_intf.LitV $ C_intf.LitInt $ length $ snd $ bl)))%I.

Definition alloc_proto : C_proto := (λ fn vl Φ,
   ∃ θ dirty tg sz,
     "->" ∷ ⌜fn = "alloc"⌝ ∗
     "HGC" ∷ GC θ dirty ∗
     "->" ∷ ⌜vl = [ C_intf.LitV $ C_intf.LitInt $ vblock_tag_as_int $ tg; C_intf.LitV $ C_intf.LitInt $ sz ]⌝ ∗
     "%Hsz" ∷ ⌜0 ≤ sz⌝%Z ∗
     "Cont" ∷ ▷ (∀ θ' γ w, GC θ' dirty -∗
                            γ ↦fresh (tg, List.repeat (Lint 0) (Z.to_nat sz)) -∗
                            ⌜repr_lval θ' (Lloc γ) w⌝ -∗
                            Φ w))%I.

Definition alloc_foreign_proto : C_proto := (λ fn vl Φ,
  ∃ θ dirty,
    "->" ∷ ⌜fn = "alloc_foreign"⌝ ∗
    "HGC" ∷ GC θ dirty ∗
    "->" ∷ ⌜vl = [ ]⌝ ∗
    "Cont" ∷ ▷ (∀ θ' γ w, GC θ' dirty -∗
                          γ ↦foreignO None -∗
                          ⌜repr_lval θ' (Lloc γ) w⌝ -∗
                          Φ w))%I.

Definition write_foreign_proto : C_proto := (λ fn vl Φ,
  ∃ θ dirty γ w wo w',
    "->" ∷ ⌜fn = "write_foreign"⌝ ∗
    "HGC" ∷ GC θ dirty ∗
    "->" ∷ ⌜vl = [ w; w' ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hpto" ∷ γ ↦foreignO wo ∗
    "Cont" ∷ ▷ (GC θ dirty -∗
                 γ ↦foreign w' -∗
                 Φ (C_intf.LitV (C_intf.LitInt 0))))%I.

Definition read_foreign_proto : C_proto := (λ fn vl Φ,
  ∃ θ dirty γ w w' dq,
    "->" ∷ ⌜fn = "read_foreign"⌝ ∗
    "HGC" ∷ GC θ dirty ∗
    "->" ∷ ⌜vl = [ w ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hpto" ∷ γ ↦foreign{dq} w' ∗
    "Cont" ∷ ▷ (GC θ dirty -∗
                 γ ↦foreign{dq} w' -∗
                 Φ w'))%I.

Definition callback_proto (Ψ : ML_proto) : C_proto := (λ fn vl Φ,
  ∃ θ w γ w' lv' v' f x e Φ',
    "->" ∷ ⌜fn = "callback"⌝ ∗
    "HGC" ∷ GC θ ∅ ∗
    "->" ∷ ⌜vl = [ w; w' ]⌝ ∗
    "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
    "Hclos" ∷ γ ↦clos (f, x, e) ∗
    "%Hreprw'" ∷ ⌜repr_lval θ lv' w'⌝ ∗
    "Hsim'" ∷ lv' ~~ v' ∗
    "WPcallback" ∷ ▷ WP (App (Val (RecV f x e)) (Val v')) at ⟨∅, Ψ⟩ {{ Φ' }} ∗
    "Cont" ∷ ▷ (∀ θ' vret lvret wret,
                   GC θ' ∅ -∗
                   Φ' vret -∗
                   lvret ~~ vret -∗
                   ⌜repr_lval θ' lvret wret⌝ -∗
                   Φ wret))%I.

Definition main_proto (Φ' : Z → Prop) (Pinit : iProp Σ) : C_proto := (λ fn vl Φ,
  "->" ∷ ⌜fn = "main"⌝ ∗
  "->" ∷ ⌜vl = []⌝ ∗
  "Hat_init" ∷ at_init ∗
  "Hinitial_resources" ∷ Pinit ∗
  "Cont" ∷ ▷ (∀ x, ⌜Φ' x⌝ -∗ Φ (code_int x)))%I.

Definition prim_proto (p : prim) (Ψ : ML_proto) : C_proto :=
  match p with
  | Pint2val => int2val_proto
  | Pval2int => val2int_proto
  | Pregisterroot => registerroot_proto
  | Punregisterroot => unregisterroot_proto
  | Pmodify => modify_proto
  | Preadfield => readfield_proto
  | Pisblock => isblock_proto
  | Pread_tag => read_tag_proto
  | Plength => length_proto
  | Palloc => alloc_proto
  | Pallocforeign => alloc_foreign_proto
  | Pwriteforeign => write_foreign_proto
  | Preadforeign => read_foreign_proto
  | Pcallback => callback_proto Ψ
  | Pmain _ => ⊥
  end.

Definition prims_proto (Ψ : ML_proto) : C_proto :=
  (λ fn vs Φ, ∃ p, prim_proto p Ψ fn vs Φ)%I.

Lemma proto_prim_mono Ψ1 Ψ2 : Ψ1 ⊑ Ψ2 →
  prims_proto Ψ1 ⊑ prims_proto Ψ2.
Proof using.
  iIntros (HH s vv Φ) "H". iDestruct "H" as (p) "H". iExists p.
  destruct p; try done. all: cbn; iNamed "H".
  { do 10 iExists _; unfold named.
    iFrame. do 4 (iSplit; first done).
    iNext. iApply (wp_strong_mono with "[-] []"). 1-2: done.
    1: iFrame. by iIntros (v) "$". }
Qed.

Lemma prims_proto_except_prims Ψ :
  (prims_proto Ψ) except prim_names ⊑ ⊥.
Proof using.
  iIntros (? ? ?) "H". rewrite /proto_except.
  iDestruct "H" as (Hnin%not_elem_of_prim_names ?) "H".
  destruct p; unfold prim_proto; iNamed "H";
    try by (exfalso; apply Hnin; eexists; constructor).
  done.
Qed.

Lemma main_proto_mono (Φ Φ' : Z → Prop) (P P' : iProp Σ) :
  (∀ x, Φ x → Φ' x) → (P' -∗ P) →
  main_proto Φ' P' ⊑ main_proto Φ P.
Proof.
  iIntros (Himpl Hwand ? ? ?) "H". iNamed "H".
  rewrite /main_proto /named. do 2 (iSplit; first done).
  iFrame. iSplitL "Hinitial_resources".
  - iApply (Hwand with "[$]").
  - iIntros "!>" (? ?). iApply "Cont". iPureIntro. eauto.
Qed.

(* some boilerplate *)
Local Ltac tac p :=
  iIntros (? ? ?) "H"; by iExists p.
Lemma int2val_refines_prims_proto Ψ : int2val_proto ⊑ prims_proto Ψ.
Proof using. tac Pint2val. Qed.
Lemma val2int_refines_prims_proto Ψ : val2int_proto ⊑ prims_proto Ψ.
Proof using. tac Pval2int. Qed.
Lemma registerroot_refines_prims_proto Ψ : registerroot_proto ⊑ prims_proto Ψ.
Proof using. tac Pregisterroot. Qed.
Lemma unregisterroot_refines_prims_proto Ψ : unregisterroot_proto ⊑ prims_proto Ψ.
Proof using. tac Punregisterroot. Qed.
Lemma modify_refines_prims_proto Ψ : modify_proto ⊑ prims_proto Ψ.
Proof using. tac Pmodify. Qed.
Lemma readfield_refines_prims_proto Ψ : readfield_proto ⊑ prims_proto Ψ.
Proof using. tac Preadfield. Qed.
Lemma isblock_refines_prims_proto Ψ : isblock_proto ⊑ prims_proto Ψ.
Proof using. tac Pisblock. Qed.
Lemma read_tag_refines_prims_proto Ψ : read_tag_proto ⊑ prims_proto Ψ.
Proof using. tac Pread_tag. Qed.
Lemma length_refines_prims_proto Ψ : length_proto ⊑ prims_proto Ψ.
Proof using. tac Plength. Qed.
Lemma alloc_refines_prims_proto Ψ : alloc_proto ⊑ prims_proto Ψ.
Proof using. tac Palloc. Qed.
Lemma alloc_foreign_refines_prims_proto Ψ : alloc_foreign_proto ⊑ prims_proto Ψ.
Proof using. tac Pallocforeign. Qed.
Lemma write_foreign_refines_prims_proto Ψ : write_foreign_proto ⊑ prims_proto Ψ.
Proof using. tac Pwriteforeign. Qed.
Lemma read_foreign_refines_prims_proto Ψ : read_foreign_proto ⊑ prims_proto Ψ.
Proof using. tac Preadforeign. Qed.
Lemma callback_refines_prims_proto Ψ : callback_proto Ψ ⊑ prims_proto Ψ.
Proof using. tac Pcallback. Qed.

End PrimsProto.

Global Hint Resolve int2val_refines_prims_proto : core.
Global Hint Resolve val2int_refines_prims_proto : core.
Global Hint Resolve registerroot_refines_prims_proto : core.
Global Hint Resolve unregisterroot_refines_prims_proto : core.
Global Hint Resolve modify_refines_prims_proto : core.
Global Hint Resolve readfield_refines_prims_proto : core.
Global Hint Resolve isblock_refines_prims_proto : core.
Global Hint Resolve read_tag_refines_prims_proto : core.
Global Hint Resolve length_refines_prims_proto : core.
Global Hint Resolve alloc_refines_prims_proto : core.
Global Hint Resolve alloc_foreign_refines_prims_proto : core.
Global Hint Resolve write_foreign_refines_prims_proto : core.
Global Hint Resolve read_foreign_refines_prims_proto : core.
Global Hint Resolve callback_refines_prims_proto : core.
