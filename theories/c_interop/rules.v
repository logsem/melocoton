From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources gctoken update_laws prims prims_proto.
From melocoton.ml_lang Require Import lang_instantiation primitive_laws.
From melocoton.c_interface Require Export defs resources.
From melocoton.c_lang Require Import primitive_laws tactics notation proofmode.
From iris.prelude Require Import options.

(* Derived WP rules for C<->ML interop.

   These follow from the generic rules of the wrapper (in interop/) that work
   for any language obeying the C interface (c_interface/) -- specialized to our
   concrete C language (c_lang/). *)

Section Laws.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ, !invGS_gen hlc Σ}.
Context `{!wrapperGCtokGS Σ}.

(* Reading and writing roots using plain C reads and writes *)

Lemma store_to_root E pe (l:loc) (v v' : lval) w θ :
  repr_lval θ v w →
  {{{ GC θ ∗ l ↦roots v' }}}
     (#l <- w)%CE @ pe; E
  {{{ RET LitV LitUnit; GC θ ∗ l ↦roots v }}}%CE.
Proof.
  iIntros (Hrepr Φ) "(HGC&Hroot) HΦ".
  iDestruct (update_root with "[$HGC $Hroot]") as (w') "(Hpto & _ & Hupd)".
  iApply wp_fupd.
  iApply (wp_store with "Hpto"). iIntros "!> Hpto".
  iMod ("Hupd" with "[$Hpto]") as "(? & ?)"; first done.
  iApply "HΦ". by iFrame.
Qed.

Lemma load_from_root E pe (l:loc) (v : lval) dq θ :
  {{{ GC θ ∗ l ↦roots{dq} v }}}
     ( * #l)%CE @ pe; E
  {{{ w, RET w; l ↦roots{dq} v ∗ GC θ ∗ ⌜repr_lval θ v w⌝ }}}%CE.
Proof.
  iIntros (Φ) "(HGC&Hroot) HΦ".
  iDestruct (access_root with "[$HGC $Hroot]") as (w') "(Hpto & %Hrepr & Hupd)".
  iApply (wp_load with "Hpto"). iIntros "!> Hpto".
  iDestruct ("Hupd" with "Hpto") as "(?&?)". iApply "HΦ". by iFrame.
Qed.

(* Calling to runtime primitives *)

(* TODO: move / refactor / merge with the other penv combinators *)
Definition penv_with_prims E (pe : language.weakestpre.prog_environ C_lang Σ) (T : ML_proto Σ) :
  language.weakestpre.prog_environ C_lang Σ
  :=
  {| penv_prog := filter (λ '(s, _), ¬ is_prim_name s) (penv_prog pe);
     penv_proto := (λ f vs Φ, proto_prims_in_C E T f vs Φ ∨ penv_proto pe f vs Φ)%I; |}.


Lemma int2val_spec E pe (T : ML_proto Σ) θ (x : Z) :
  {{{ GC θ }}}
    (call: &"int2val" with (Val #x))%CE @ (penv_with_prims E pe T); E
  {{{ w, RET w; GC θ ∗ ⌜repr_lval θ (Lint x) w⌝ }}}.
Proof.
  iIntros (Φ) "HGC Cont".
  wp_pures. wp_extern.
  { cbn. apply map_filter_lookup_None_2. right.
    intros _ _. intros H; apply H. eexists; constructor. }
  iModIntro. cbn. iLeft. iExists _. iSplit; first by eauto.
  iLeft. iLeft. rewrite /proto_int2val /named. iExists _, _. iFrame.
  do 2 (iSplit; first by eauto). iIntros "!>" (?) "HGC %".
  iApply wp_value; eauto. iApply "Cont"; eauto.
Qed.

Lemma val2int_spec E pe (T : ML_proto Σ) θ (w:word) (x:Z) :
  repr_lval θ (Lint x) w →
  {{{ GC θ }}}
    (call: &"val2int" with (Val w))%CE @ (penv_with_prims E pe T); E
  {{{ RET (#x); GC θ }}}.
Proof.
  iIntros (Hrepr Φ) "HGC Cont".
  wp_pures. wp_extern.
  { cbn. apply map_filter_lookup_None_2. right.
    intros _ _. intros H; apply H. eexists; constructor. }
  iModIntro. cbn. iLeft. iExists _. iSplit; first by eauto.
  iLeft. iRight; iLeft. rewrite /proto_val2int /named. iExists _, _, _. iFrame.
  do 3 (iSplit; first by eauto). iIntros "!> HGC".
  iApply wp_value; eauto. iApply "Cont"; eauto.
Qed.

Lemma registerroot_spec E pe (T : ML_proto Σ) θ v w a :
  repr_lval θ v w →
  {{{ GC θ ∗ a ↦C w }}}
    (call: &"registerroot" with (Val (# a)))%CE
      @ (penv_with_prims E pe T); E
  {{{ RET (# 0); GC θ ∗ a ↦roots v }}}.
Proof.
  iIntros (Hrepr Φ) "(HGC & Hpto) Cont".
  wp_pures. wp_extern.
  { cbn. apply map_filter_lookup_None_2. right.
    intros _ _. intros H; apply H. eexists; constructor. }
  iModIntro. cbn. iLeft. iExists _. iSplit; first by eauto.
  iLeft. do 2 iRight; iLeft. rewrite /proto_registerroot /named.
  iExists _, _, _, _. iFrame.
  do 3 (iSplit; first by eauto). iIntros "!> ? ?".
  iApply wp_value; eauto. iApply "Cont"; eauto. iFrame.
Qed.

Lemma unregisterroot_spec E pe (T : ML_proto Σ) θ v a :
  {{{ GC θ ∗ a ↦roots v }}}
    (call: &"unregisterroot" with (Val (# a)))%CE
      @ (penv_with_prims E pe T); E
  {{{ w, RET (# 0); GC θ ∗ a ↦C w ∗ ⌜repr_lval θ v w⌝ }}}.
Proof.
  iIntros (Φ) "(HGC & Hpto) Cont".
  wp_pures. wp_extern.
  { cbn. apply map_filter_lookup_None_2. right.
    intros _ _. intros H; apply H. eexists; constructor. }
  iModIntro. cbn. iLeft. iExists _. iSplit; first by eauto.
  iLeft. do 3 iRight; iLeft. rewrite /proto_unregisterroot /named.
  iExists _, _, _. iFrame.
  do 2 (iSplit; first by eauto). iIntros "!>" (?) "? ? %".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma modify_spec E pe (T : ML_proto Σ) θ γ w mut tg vs v' w' i :
  repr_lval θ (Lloc γ) w →
  vblock_access_le M mut →
  repr_lval θ v' w' →
  (0 ≤ i < length vs)%Z →
  {{{ GC θ ∗ γ ↦vblk[mut] (tg, vs) }}}
    (call: &"modify" with (Val w, Val (# i), Val w'))%CE
      @ (penv_with_prims E pe T); E
  {{{ RET (# 0); GC θ ∗ γ ↦vblk[mut] (tg, <[Z.to_nat i:=v']> vs) }}}.
Proof.
  intros. iIntros "(HGC & Hpto) Cont".
  wp_pures. wp_extern.
  { cbn. apply map_filter_lookup_None_2. right.
    intros _ _. intros HH; apply HH. eexists; constructor. }
  iModIntro. cbn. iLeft. iExists _. iSplit; first by eauto.
  iLeft. do 4 iRight; iLeft. rewrite /proto_modify /named.
  do 9 iExists _. iFrame.
  do 7 (iSplit; first by eauto with lia). iIntros "!> ? ?".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma readfield_spec E pe (T : ML_proto Σ) θ γ w m dq tg vs i :
  repr_lval θ (Lloc γ) w →
  (0 ≤ i < length vs)%Z →
  {{{ GC θ ∗ γ ↦vblk[m]{dq} (tg, vs) }}}
    (call: &"readfield" with (Val w, Val (# i)))%CE
      @ (penv_with_prims E pe T); E
  {{{ v' w', RET w';
        GC θ ∗ γ ↦vblk[m]{dq} (tg, vs) ∗
        ⌜vs !! (Z.to_nat i) = Some v'⌝ ∗
        ⌜repr_lval θ v' w'⌝ }}}.
Proof.
  intros. iIntros "(HGC & Hpto) Cont".
  wp_pures. wp_extern.
  { cbn. apply map_filter_lookup_None_2. right.
    intros _ _. intros HH; apply HH. eexists; constructor. }
  iModIntro. cbn. iLeft. iExists _. iSplit; first by eauto.
  iLeft. do 5 iRight; iLeft. rewrite /proto_readfield /named.
  do 8 iExists _. iFrame.
  do 5 (iSplit; first by eauto with lia). iIntros "!>" (? ?) "? ?".
  iIntros (? ?).
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma alloc_spec E pe (T : ML_proto Σ) θ tg tgnum sz :
  (0 ≤ sz)%Z →
  vblock_tag_as_int tg = tgnum →
  {{{ GC θ }}}
    (call: &"alloc" with (Val (# tgnum), Val (# sz)))%CE
      @ (penv_with_prims E pe T); E
  {{{ θ' γ w, RET w;
        GC θ' ∗ γ ↦fresh (tg, List.repeat (Lint 0) (Z.to_nat sz)) ∗
        ⌜repr_lval θ' (Lloc γ) w⌝ }}}.
Proof.
  intros. iIntros "HGC Cont".
  wp_pures. wp_extern.
  { cbn. apply map_filter_lookup_None_2. right.
    intros _ _. intros HH; apply HH. eexists; constructor. }
  iModIntro. cbn. iLeft. iExists _. iSplit; first by eauto.
  iLeft. do 6 iRight; iLeft. rewrite /proto_alloc /named.
  do 3 iExists _. iFrame. subst.
  do 3 (iSplit; first by eauto with lia). iIntros "!>" (? ? ?) "? ? %".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma alloc_foreign_spec E pe (T : ML_proto Σ) θ a :
  {{{ GC θ }}}
    (call: &"alloc_foreign" with (Val (# a)))%CE
      @ (penv_with_prims E pe T); E
  {{{ θ' γ w, RET w;
        GC θ' ∗ γ ↦foreign a ∗
        ⌜repr_lval θ' (Lloc γ) w⌝ }}}.
Proof.
  intros. iIntros "HGC Cont".
  wp_pures. wp_extern.
  { cbn. apply map_filter_lookup_None_2. right.
    intros _ _. intros HH; apply HH. eexists; constructor. }
  iModIntro. cbn. iLeft. iExists _. iSplit; first by eauto.
  iLeft. do 7 iRight; iLeft. rewrite /proto_alloc_foreign /named.
  do 2 iExists _. iFrame.
  do 2 (iSplit; first by eauto with lia). iIntros "!>" (? ? ?) "? ? %".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma write_foreign_spec E pe (T : ML_proto Σ) θ w γ a a' :
  repr_lval θ (Lloc γ) w →
  {{{ GC θ ∗ γ ↦foreign a }}}
    (call: &"write_foreign" with (Val w, Val (# a')))%CE
      @ (penv_with_prims E pe T); E
  {{{ RET (# 0); GC θ ∗ γ ↦foreign a' }}}.
Proof.
  intros. iIntros "(HGC & ?) Cont".
  wp_pures. wp_extern.
  { cbn. apply map_filter_lookup_None_2. right.
    intros _ _. intros HH; apply HH. eexists; constructor. }
  iModIntro. cbn. iLeft. iExists _. iSplit; first by eauto.
  iLeft. do 8 iRight; iLeft. rewrite /proto_write_foreign /named.
  do 5 iExists _. iFrame.
  do 3 (iSplit; first by eauto with lia). iIntros "!> ? ?".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma read_foreign_spec E pe (T : ML_proto Σ) θ w γ a :
  repr_lval θ (Lloc γ) w →
  {{{ GC θ ∗ γ ↦foreign a }}}
    (call: &"read_foreign" with (Val w))%CE
      @ (penv_with_prims E pe T); E
  {{{ RET (# a); GC θ ∗ γ ↦foreign a }}}.
Proof.
  intros. iIntros "(HGC & ?) Cont".
  wp_pures. wp_extern.
  { cbn. apply map_filter_lookup_None_2. right.
    intros _ _. intros HH; apply HH. eexists; constructor. }
  iModIntro. cbn. iLeft. iExists _. iSplit; first by eauto.
  iLeft. do 9 iRight. rewrite /proto_read_foreign /named.
  do 4 iExists _. iFrame.
  do 3 (iSplit; first by eauto with lia). iIntros "!> ? ?".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma callback_spec E pe (T : ML_proto Σ) θ w γ f x e lv' w' v' ψ :
  repr_lval θ (Lloc γ) w →
  repr_lval θ lv' w' →
  {{{ GC θ ∗
      γ ↦clos (f, x, e) ∗
      lv' ~~ v' ∗
      (▷ WP (App (ML_lang.Val (RecV f x e)) (ML_lang.Val v')) @ ⟨∅, T⟩; E {{ ψ }})
  }}}
    (call: &"callback" with (Val w, Val w'))%CE
      @ (penv_with_prims E pe T); E
  {{{ θ' vret lvret wret, RET wret;
        GC θ' ∗
        ψ vret ∗
        lvret ~~ vret ∗
        ⌜repr_lval θ' lvret wret⌝ }}}.
Proof.
  intros. iIntros "(? & ? & ? & ?) Cont".
  wp_pures. wp_extern.
  { cbn. apply map_filter_lookup_None_2. right.
    intros _ _. intros HH; apply HH. eexists; constructor. }
  iModIntro. cbn. iLeft. iExists _. iSplit; first by eauto.
  iRight. rewrite /proto_callback /named.
  do 10 iExists _. iFrame.
  do 4 (iSplit; first by eauto with lia). iIntros "!>" (? ? ? ?) "? ? ? %".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

End Laws.
