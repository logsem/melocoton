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
    "HGC" ∷ GC θ ∗
    "%Hrepr" ∷ ⌜Forall2 (repr_lval θ) lvs ws⌝ ∗
    "#Hsim" ∷ lvs ~~∗ vs ∗
    "Hproto" ∷ Ψ f vs Φ' ∗
    "Return" ∷ (∀ θ' vret lvret wret,
      GC θ' -∗
      Φ' vret -∗
      lvret ~~ₒ vret -∗
      ⌜repr_lval_out θ' lvret wret⌝ -∗
      Φ wret)
)%I.

Lemma wrap_proto_mono Ψ Ψ' : Ψ ⊑ Ψ' → wrap_proto Ψ ⊑ wrap_proto Ψ'.
Proof using.
  iIntros (Hre ? ? ?) "H". unfold wrap_proto. iNamed "H".
  rewrite /named. iExists _, _, _, _. iFrame. iFrame "Hsim". iSplit; first done.
  by iApply Hre.
Qed.

Definition int2val_proto : C_proto :=
  !! θ z
  {{ "HGC" ∷ GC θ }}
    "int2val" with [C_intf.LitV $ C_intf.LitInt $ z]
  {{ w, RETV w; GC θ ∗ ⌜repr_lval θ (Lint z) w⌝ }}.

Definition val2int_proto : C_proto :=
  !! θ w z
  {{ "HGC" ∷ GC θ ∗ "%Hrepr" ∷ ⌜repr_lval θ (Lint z) w⌝ }}
    "val2int" with [w]
  {{ RETV C_intf.LitV $ C_intf.LitInt $ z; GC θ }}.

Definition registerroot_proto : C_proto :=
  !! θ l v w
  {{
     "HGC" ∷ GC θ ∗
     "Hpto" ∷ l ↦C w ∗
     "%Hrepr" ∷ ⌜repr_lval θ v w⌝
  }}
    "registerroot" with [ C_intf.LitV $ C_intf.LitLoc $ l ]
  {{ RETV C_intf.LitV $ C_intf.LitInt $ 0; GC θ ∗ l ↦roots v }}.

Definition unregisterroot_proto : C_proto :=
  !! θ l v
  {{ "HGC" ∷ GC θ ∗ "Hpto" ∷ l ↦roots v }}
    "unregisterroot" with [ C_intf.LitV $ C_intf.LitLoc $ l ]
  {{ w, RETV C_intf.LitV $ C_intf.LitInt $ 0; GC θ ∗ l ↦C w ∗ ⌜repr_lval θ v w⌝ }}.

Definition initlocalroot_proto : C_proto :=
  !! θ fc
  {{ "HGC" ∷ GC θ ∗ "Hfc" ∷ current_fc fc }}
    "initlocalroot" with [ ]
  {{ f, RETV C_intf.LitV $ C_intf.LitInt $ 0;
    GC θ ∗ current_fc (f :: fc) ∗ ⌜fresh_frame f fc⌝
  }}.

Check elements.

Definition registerlocalroot_proto : C_proto :=
  !! θ l v w f fc r
    {{
       "HGC"    ∷ GC θ
     ∗ "Hpto"   ∷ l ↦C w
     ∗ "Hfc"    ∷ current_fc (f :: fc)
     ∗ "Hlr"    ∷ local_roots f r
     ∗ "%Hrepr" ∷ ⌜repr_lval θ v w⌝
    }}
        "registerlocalroot" with [ C_intf.LitV $ C_intf.LitLoc $ l ]
    {{
      RETV C_intf.LitV $ C_intf.LitInt $ 0;
      GC θ ∗ l ↦roots[f] v ∗ current_fc (f :: fc) ∗ local_roots f ({[l]} ∪ r)
    }}.

Definition unregisterlocalroot_proto : C_proto :=
  !! θ f fc r ws
  {{
       "HGC"    ∷ GC θ
     ∗ "Hfc"    ∷ current_fc (f :: fc)
     ∗ "Hlr"    ∷ local_roots f r
     ∗ "Hpto"   ∷ ([∗ list] l; w ∈ (elements r); ws, l ↦roots[f] w)
  }}
    "unregisterlocalroot" with [ ]
  {{ RETV C_intf.LitV $ C_intf.LitInt $ 0; GC θ ∗ current_fc (f :: fc) }}.

Definition modify_proto : C_proto :=
  !! θ w i v' w' γ mut tg vs
  {{
     "HGC" ∷ GC θ ∗
     "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
     "%Hptomut" ∷ ⌜vblock_access_le M mut⌝ ∗
     "%Hreprw'" ∷ ⌜repr_lval θ v' w'⌝ ∗
     "%Hi1" ∷ ⌜0 ≤ i⌝%Z ∗
     "%Hi2" ∷ ⌜i < length vs⌝%Z ∗
     "Hpto" ∷ γ ↦vblk[mut] (tg, vs)
  }}
    "modify" with [ w; C_intf.LitV $ C_intf.LitInt $ i; w' ]
  {{ RETV C_intf.LitV $ C_intf.LitInt $ 0;
     GC θ ∗ γ ↦vblk[mut] (tg, <[Z.to_nat i:=v']> vs)
  }}.

Definition readfield_proto : C_proto :=
  !! θ w i γ dq m tg vs
  {{
     "HGC" ∷ GC θ ∗
     "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
     "%Hi1" ∷ ⌜0 ≤ i⌝%Z ∗
     "%Hi2" ∷ ⌜i < length vs⌝%Z ∗
     "Hpto" ∷ γ ↦vblk[m]{dq} (tg, vs)
  }}
    "readfield" with [ w; C_intf.LitV $ C_intf.LitInt $ i ]
  {{ w' v', RETV w';
     GC θ ∗
     γ ↦vblk[m]{dq} (tg, vs) ∗
     ⌜vs !! (Z.to_nat i) = Some v'⌝ ∗
     ⌜repr_lval θ v' w'⌝
  }}.

Definition isblock_proto : C_proto :=
  !! θ lv w
  {{ "HGC" ∷ GC θ ∗ "%Hreprw" ∷ ⌜repr_lval θ lv w⌝ }}
    "isblock" with [ w ]
  {{ RETV C_intf.LitV $ C_intf.LitInt
            (match lv with Lloc _ => 1 | _ => 0 end);
     GC θ
  }}.

Definition read_tag_proto : C_proto :=
  !! θ γ w dq bl tg
  {{
     "HGC" ∷ GC θ ∗
     "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
     "->" ∷ ⌜tg = block_tag bl⌝ ∗
     "Hpto" ∷ lstore_own_elem γ dq bl
  }}
    "read_tag" with [ w ]
  {{ RETV C_intf.LitV $ C_intf.LitInt $ (tag_as_int tg);
     GC θ ∗ lstore_own_elem γ dq bl
  }}.

Definition length_proto : C_proto :=
  !! θ γ w a dq bl
  {{
     "HGC" ∷ GC θ ∗
     "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
     "Hpto" ∷ γ ↦vblk[ a ]{ dq } bl
  }}
    "length" with [ w ]
  {{ RETV C_intf.LitV $ C_intf.LitInt $ length $ snd $ bl;
     GC θ ∗ γ ↦vblk[ a ]{ dq } bl
  }}.

Definition alloc_proto : C_proto :=
  !! θ tg sz
  {{ "HGC" ∷ GC θ ∗ "%Hsz" ∷ ⌜0 ≤ sz⌝%Z }}
    "alloc" with
      [ C_intf.LitV $ C_intf.LitInt $ vblock_tag_as_int $ tg; C_intf.LitV $ C_intf.LitInt $ sz ]
  {{ θ' γ w, RETV w;
     GC θ' ∗
     γ ↦fresh (tg, List.repeat (Lint 0) (Z.to_nat sz)) ∗
     ⌜repr_lval θ' (Lloc γ) w⌝
  }}.

Definition alloc_foreign_proto : C_proto :=
  !! θ
  {{ GC θ }}
    "alloc_foreign" with []
  {{ θ' γ w, RETV w; GC θ' ∗ γ ↦foreignO[Mut] None ∗ ⌜repr_lval θ' (Lloc γ) w⌝ }}.

Definition write_foreign_proto : C_proto :=
  !! θ γ w wo w'
  {{
     "HGC" ∷ GC θ ∗
     "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
     "Hpto" ∷ γ ↦foreignO[Mut] wo
  }}
    "write_foreign" with [ w; w' ]
  {{ RETV (C_intf.LitV (C_intf.LitInt 0));
     GC θ ∗ γ ↦foreign[Mut] w'
  }}.

Definition read_foreign_proto : C_proto :=
  !! θ γ w w' m dq
  {{
     "HGC" ∷ GC θ ∗
     "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
     "Hpto" ∷ γ ↦foreign[m]{dq} w'
  }}
    "read_foreign" with [ w ]
  {{ RETV w'; GC θ ∗ γ ↦foreign[m]{dq} w' }}.

Definition callback_proto (Ψ : ML_proto) : C_proto :=
  !! θ w γ w' lv' v' f x e Φ'
  {{
     "HGC" ∷ GC θ ∗
     "%Hreprw" ∷ ⌜repr_lval θ (Lloc γ) w⌝ ∗
     "Hclos" ∷ γ ↦clos (f, x, e) ∗
     "%Hreprw'" ∷ ⌜repr_lval θ lv' w'⌝ ∗
     "Hsim'" ∷ lv' ~~ v' ∗
     "WPcallback" ∷ ▷ WP (App (Val (RecV f x e)) (Val v')) at ⟨∅, Ψ⟩ {{ Φ' }}
  }}
    "callback" with [ w; w' ]
  {{ θ' ov olv ow, RET ow;
     GC θ' ∗ Φ' ov ∗ olv ~~ₒ ov ∗ ⌜repr_lval_out θ' olv ow⌝
  }}.

Definition main_proto (Φ' : Z → Prop) (Pinit : iProp Σ) : C_proto :=
  !! {{ "Hat_init" ∷ at_init ∗ "Hinitial_resources" ∷ Pinit }}
    "main" with []
  {{ x, RETV code_int x; ⌜Φ' x⌝ }}.

Definition prim_proto (p : prim) (Ψ : ML_proto) : C_proto :=
  match p with
  | Pint2val => int2val_proto
  | Pval2int => val2int_proto
  | Pregisterroot => registerroot_proto
  | Punregisterroot => unregisterroot_proto
  | Pinitlocalroot => initlocalroot_proto
  | Pregisterlocalroot => registerlocalroot_proto
  | Punregisterlocalroot => unregisterlocalroot_proto
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
  destruct p; try done. iNamedProto "H".
  iSplit; first done. do 10 iExists _; unfold named.
  iFrame. do 3 (iSplit; first done).
  iNext. iApply (wp_strong_mono with "[-] []"). 1-2: done.
  1: iFrame. by iIntros (v) "$".
Qed.

Lemma prims_proto_except_prims Ψ :
  (prims_proto Ψ) except prim_names ⊑ ⊥.
Proof using.
  iIntros (? ? ?) "H". rewrite /proto_except.
  iDestruct "H" as (Hnin%not_elem_of_prim_names ?) "H".
  destruct p; unfold prim_proto; last done;
    iDestruct "H" as (->) "?";
    by (exfalso; apply Hnin; eexists; constructor).
Qed.

Lemma main_proto_mono (Φ Φ' : Z → Prop) (P P' : iProp Σ) :
  (∀ x, Φ x → Φ' x) → (P' -∗ P) →
  main_proto Φ' P' ⊑ main_proto Φ P.
Proof.
  iIntros (Himpl Hwand ? ? ?) "H". iNamedProto "H".
  do 2 (iSplit; first done).
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
Lemma initlocalroot_refines_prims_proto Ψ : initlocalroot_proto ⊑ prims_proto Ψ.
Proof using. tac Pinitlocalroot. Qed.
Lemma registerlocalroot_refines_prims_proto Ψ : registerlocalroot_proto ⊑ prims_proto Ψ.
Proof using. tac Pregisterlocalroot. Qed.
Lemma unregisterlocalroot_refines_prims_proto Ψ : unregisterlocalroot_proto ⊑ prims_proto Ψ.
Proof using. tac Punregisterlocalroot. Qed.
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
Global Hint Resolve initlocalroot_refines_prims_proto : core.
Global Hint Resolve registerlocalroot_refines_prims_proto : core.
Global Hint Resolve unregisterlocalroot_refines_prims_proto : core.
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
