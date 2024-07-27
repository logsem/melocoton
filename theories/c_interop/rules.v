From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources gctoken update_laws prims prims_proto.
From melocoton.ml_lang Require Import lang_instantiation primitive_laws.
From melocoton.c_interface Require Export defs resources.
From melocoton.c_lang Require Import primitive_laws tactics notation proofmode.
From melocoton.c_interop Require Import notation.
From iris.prelude Require Import options.

(* Derived WP rules for C<->ML interop.

   These follow from the generic rules of the wrapper (in interop/) that work
r  for any language obeying the C interface (c_interface/) -- specialized to our
   concrete C language (c_lang/). *)

Section Laws.

Context {SI : indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ, !invG Σ}.
Context `{!wrapperGCtokG Σ}.

(* Reading and writing roots using plain C reads and writes *)

Lemma store_to_root pe (l:loc) (v v' : lval) w θ :
  repr_lval θ v w →
  {{{ GC θ ∗ l ↦roots v' }}}
     (#l <- w)%CE at pe
  {{{ RETV LitV LitUnit; GC θ ∗ l ↦roots v }}}%CE.
Proof.
  iIntros (Hrepr Φ) "(HGC&Hroot) HΦ".
  iDestruct (update_root with "[$HGC $Hroot]") as (w') "(Hpto & _ & Hupd)".
  iApply wp_fupd.
  iApply (wp_store with "Hpto"). iIntros "!> Hpto".
  iMod ("Hupd" with "[$Hpto]") as "(? & ?)"; first done.
  iApply "HΦ". by iFrame.
Qed.

Lemma store_to_local_root pe (l : loc) (f : gname) (r : gset addr) (v v' : lval) w θ :
  repr_lval θ v w →
  {{{ GC θ ∗ l ↦roots[f] v' ∗ local_roots f r }}}
     (#l <- w)%CE at pe
  {{{ RETV LitV LitUnit; GC θ ∗ l ↦roots[f] v ∗ local_roots f r }}}%CE.
Proof.
  iIntros (Hrepr Φ) "(HGC&Hroot&Hlocal) HΦ".
  iDestruct (update_local_root with "[$HGC $Hroot $Hlocal]") as (w') "(Hpto & _ & Hupd)".
  iApply wp_fupd.
  iApply (wp_store with "Hpto"). iIntros "!> Hpto".
  iMod ("Hupd" with "[$Hpto]") as "(? & ?)"; first done.
  iApply "HΦ". by iFrame.
Qed.

Lemma load_from_root pe (l:loc) (v : lval) dq θ :
  {{{ GC θ ∗ l ↦roots{dq} v }}}
     ( * #l)%CE at pe
  {{{ w, RETV w; l ↦roots{dq} v ∗ GC θ ∗ ⌜repr_lval θ v w⌝ }}}%CE.
Proof.
  iIntros (Φ) "(HGC&Hroot) HΦ".
  iDestruct (access_root with "[$HGC $Hroot]") as (w') "(Hpto & %Hrepr & Hupd)".
  iApply (wp_load with "Hpto"). iIntros "!> Hpto".
  iDestruct ("Hupd" with "Hpto") as "(?&?)". iApply "HΦ". by iFrame.
Qed.

Lemma load_from_local_root pe (l:loc) (f : gname) (r : gset addr) (v : lval) dq θ :
  {{{ GC θ ∗ l ↦roots[f]{dq} v ∗ local_roots f r }}}
     ( * #l)%CE at pe
  {{{ w, RETV w; l ↦roots[f]{dq} v ∗ GC θ ∗ local_roots f r ∗ ⌜repr_lval θ v w⌝ }}}%CE.
Proof.
  iIntros (Φ) "(HGC&Hroot) HΦ".
  iDestruct (access_local_root with "[$HGC $Hroot]") as (w') "(Hpto & %Hrepr & Hupd)".
  iApply (wp_load with "Hpto"). iIntros "!> Hpto".
  iDestruct ("Hupd" with "Hpto") as "(?&?&?)". iApply "HΦ". by iFrame.
Qed.

(* Calling to runtime primitives *)

Lemma wp_int2val p Ψ θ (x : Z) :
  p !! "int2val" = None →
  int2val_proto ⊑ Ψ →
  {{{ GC θ }}}
    (call: &"int2val" with (Val #x))%CE at ⟨p, Ψ⟩
  {{{ w, RETV w; GC θ ∗ ⌜repr_lval θ (Lint x) w⌝ }}}.
Proof.
  iIntros (Hp Hproto Φ) "HGC Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /int2val_proto /named. iSplit; first done. iExists _, _.
  iSplit; first done. iFrame. iIntros "!>" (?) "[HGC %]".
  iApply wp_outcome; eauto. iApply "Cont"; eauto.
Qed.

Lemma wp_val2int p Ψ θ (w:word) (x : Z) :
  p !! "val2int" = None →
  val2int_proto ⊑ Ψ →
  repr_lval θ (Lint x) w →
  {{{ GC θ }}}
    (call: &"val2int" with (Val w))%CE at ⟨p, Ψ⟩
  {{{ RETV #x; GC θ }}}.
Proof.
  iIntros (Hp Hproto Hrepr Φ) "HGC Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /val2int_proto /named. iSplit; first done.
  iExists _, _, _. iFrame.
  do 2 (iSplit; first by eauto). iIntros "!> HGC".
  iApply wp_outcome; eauto. iApply "Cont"; eauto.
Qed.

Lemma wp_registerroot p Ψ θ v w a :
  p !! "registerroot" = None →
  registerroot_proto ⊑ Ψ →
  repr_lval θ v w →
  {{{ GC θ ∗ a ↦C w }}}
    (call: &"registerroot" with (Val (# a)))%CE at ⟨p, Ψ⟩
  {{{ RETV # 0; GC θ ∗ a ↦roots v }}}.
Proof.
  iIntros (Hp Hproto Hrepr Φ) "(HGC & Hpto) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /registerroot_proto /named. iSplit; first done.
  iExists _, _, _, _. iFrame.
  do 2 (iSplit; first by eauto). iIntros "!> [? ?]".
  iApply wp_outcome; eauto. iApply "Cont"; eauto. iFrame.
Qed.

Lemma wp_unregisterroot p Ψ θ v a :
  p !! "unregisterroot" = None →
  unregisterroot_proto ⊑ Ψ →
  {{{ GC θ ∗ a ↦roots v }}}
    (call: &"unregisterroot" with (Val (# a)))%CE at ⟨p, Ψ⟩
  {{{ w, RETV # 0; GC θ ∗ a ↦C w ∗ ⌜repr_lval θ v w⌝ }}}.
Proof.
  iIntros (Hp Hproto Φ) "(HGC & Hpto) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /unregisterroot_proto /named. iSplit; first done.
  iExists _, _, _. iFrame.
  iSplit; first by eauto. iIntros "!>" (?) "(? & ? & %)".
  iApply wp_outcome; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_initlocalroot p Ψ θ fc :
  p !! "initlocalroot" = None →
  initlocalroot_proto ⊑ Ψ →
  {{{ GC θ ∗ current_fc fc }}}
    (call: &"initlocalroot" with ( ))%CE at ⟨p, Ψ⟩
  {{{ f, RETV # 0; GC θ ∗ current_fc (f :: fc) ∗ local_roots f ∅ }}}.
Proof.
  iIntros (Hp Hproto Φ) "(HGC & Hfc) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /initlocalroot_proto /named. iSplit; first done.
  repeat iExists _. iFrame.
  iSplit; first done.
  iIntros "!>" (?) "(? & ?)".
  iApply wp_outcome; eauto. iApply "Cont"; eauto. iFrame.
Qed.

Lemma wp_registerlocalroot p Ψ θ v w a f fc r :
  p !! "registerlocalroot" = None →
  registerlocalroot_proto ⊑ Ψ →
  repr_lval θ v w →
  {{{ GC θ ∗ a ↦C w ∗ current_fc (f :: fc) ∗ local_roots f r }}}
    (call: &"registerlocalroot" with (Val (# a)))%CE at ⟨p, Ψ⟩
  {{{ RETV # 0; GC θ ∗ a ↦roots[f] v ∗ current_fc (f :: fc) ∗ local_roots f ({[a]} ∪ r) }}}.
Proof.
  iIntros (Hp Hproto Hrepr Φ) "(HGC & Hpto & Hfc & Hlocals) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /registerlocalroot_proto /named. iSplit; first done.
  repeat iExists _. iFrame.
  do 2 (iSplit; first by eauto). iIntros "!> [? ?]".
  iApply wp_outcome; eauto. iApply "Cont"; eauto. iFrame.
Qed.

Lemma wp_unregisterlocalroot p Ψ θ f fc r :
  p !! "unregisterlocalroot" = None →
  unregisterlocalroot_proto ⊑ Ψ →
  {{{
    GC θ
  ∗ current_fc (f :: fc)
  ∗ local_roots f r
 }}}
    (call: &"unregisterlocalroot" with ( ))%CE at ⟨p, Ψ⟩
  {{{ RETV # 0;
     GC θ
   ∗ current_fc fc
   ∗ ([∗ list] l ∈ (elements r), ∃ w, l ↦C w)
  }}}.
Proof.
  iIntros (Hp Hproto Φ) "(HGC & Hfc & Hlocals) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /unregisterlocalroot_proto /named. iSplit; first done.
  repeat iExists _. iFrame.
  iSplit; first done.
  iIntros "!> [? ?]".
  iApply wp_outcome; eauto. iApply "Cont"; eauto. iFrame.
Qed.

Lemma wp_modify p Ψ θ γ w mut tg vs v' w' i :
  p !! "modify" = None →
  modify_proto ⊑ Ψ →
  repr_lval θ (Lloc γ) w →
  vblock_access_le M mut →
  repr_lval θ v' w' →
  (0 ≤ i < length vs)%Z →
  {{{ GC θ ∗ γ ↦vblk[mut] (tg, vs) }}}
    (call: &"modify" with (Val w, Val (# i), Val w'))%CE at ⟨p, Ψ⟩
  {{{ RETV #0; GC θ ∗ γ ↦vblk[mut] (tg, <[Z.to_nat i:=v']> vs) }}}.
Proof.
  intros Hp Hproto **. iIntros "(HGC & Hpto) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /modify_proto /named. iSplit; first done.
  do 9 iExists _. iFrame.
  do 2 (iSplit; first by eauto with lia). iIntros "!> [? ?]".
  iApply wp_outcome; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_readfield p Ψ θ γ w m dq tg vs i :
  p !! "readfield" = None →
  readfield_proto ⊑ Ψ →
  repr_lval θ (Lloc γ) w →
  (0 ≤ i < length vs)%Z →
  {{{ GC θ ∗ γ ↦vblk[m]{dq} (tg, vs) }}}
    (call: &"readfield" with (Val w, Val (# i)))%CE at ⟨p, Ψ⟩
  {{{ v' w', RETV w';
        GC θ ∗ γ ↦vblk[m]{dq} (tg, vs) ∗
        ⌜vs !! (Z.to_nat i) = Some v'⌝ ∗
        ⌜repr_lval θ v' w'⌝ }}}.
Proof.
  intros Hp Hproto **. iIntros "(HGC & Hpto) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /readfield_proto /named. iSplit; first done.
  do 8 iExists _. iFrame.
  do 2 (iSplit; first by eauto with lia). iIntros "!>" (? ?) "[? ?]".
  iApply wp_outcome; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_isblock p Ψ θ lv w :
  p !! "isblock" = None →
  isblock_proto ⊑ Ψ →
  repr_lval θ lv w →
  {{{ GC θ }}}
    (call: &"isblock" with (Val w))%CE at ⟨p, Ψ⟩
  {{{ RETV #(match lv return Z with | Lloc _ => 1 | _ => 0 end); GC θ }}}.
Proof.
  intros Hp Hproto **. iIntros "HGC Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /isblock_proto /named. iSplit; first done.
  do 3 iExists _. iFrame "HGC".
  do 2 (iSplit; first done). iNext.
  iIntros "HGC". wp_pures. iApply ("Cont" with "HGC").
Qed.

Lemma wp_isblock_true p Ψ θ γ w :
  p !! "isblock" = None →
  isblock_proto ⊑ Ψ →
  repr_lval θ (Lloc γ) w →
  {{{ GC θ }}}
    (call: &"isblock" with (Val w))%CE at ⟨p, Ψ⟩
  {{{ RETV #1; GC θ }}}.
Proof.
  intros Hp Hproto **. iIntros "HGC Cont".
  iApply (wp_isblock with "HGC"); [done..|].
  iIntros "!> HGC". by iApply "Cont".
Qed.

Lemma wp_isblock_false p Ψ θ z w :
  p !! "isblock" = None →
  isblock_proto ⊑ Ψ →
  repr_lval θ (Lint z) w →
  {{{ GC θ }}}
    (call: &"isblock" with (Val w))%CE at ⟨p, Ψ⟩
  {{{ RETV #0; GC θ }}}.
Proof.
  intros Hp Hproto **. iIntros "HGC Cont".
  iApply (wp_isblock with "HGC"); [done..|].
  iIntros "!> HGC". by iApply "Cont".
Qed.

Lemma wp_read_tag p Ψ θ γ w dq bl :
  p !! "read_tag" = None →
  read_tag_proto ⊑ Ψ →
  repr_lval θ (Lloc γ) w →
  {{{ GC θ ∗ lstore_own_elem γ dq bl}}}
    (call: &"read_tag" with (Val w))%CE at ⟨p, Ψ⟩
  {{{ RETV #(tag_as_int (block_tag bl)); GC θ ∗ lstore_own_elem γ dq bl }}}.
Proof.
  intros Hp Hproto **. iIntros "(HGC&Hpto) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /read_tag_proto /named. iSplit; first done.
  do 6 iExists _. iFrame "HGC Hpto".
  do 2 (iSplit; first done). iNext.
  iIntros "[HGC Hpto]". wp_pures. iApply ("Cont" with "[$]").
Qed.

Lemma wp_length p Ψ θ γ w m dq tg vs :
  p !! "length" = None →
  length_proto ⊑ Ψ →
  repr_lval θ (Lloc γ) w →
  {{{ GC θ ∗ γ ↦vblk[m]{dq} (tg, vs) }}}
    (call: &"length" with (Val w))%CE at ⟨p, Ψ⟩
  {{{ RETV #(length vs);
        GC θ ∗ γ ↦vblk[m]{dq} (tg, vs) }}}.
Proof.
  intros Hp Hproto **. iIntros "(HGC & Hpto) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /length_proto /named. iSplit; first done.
  do 6 iExists _. iFrame.
  do 2 (iSplit; first by eauto with lia). iIntros "!> [HGC Hpto]".
  cbn.
  iApply wp_outcome; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_alloc tg p Ψ θ tgnum sz :
  p !! "alloc" = None →
  alloc_proto ⊑ Ψ →
  (0 ≤ sz)%Z →
  vblock_tag_as_int tg = tgnum →
  {{{ GC θ }}}
    (call: &"alloc" with (Val (# tgnum), Val (# sz)))%CE at ⟨p, Ψ⟩
  {{{ θ' γ w, RETV w;
        GC θ' ∗ γ ↦fresh (tg, List.repeat (Lint 0) (Z.to_nat sz)) ∗
        ⌜repr_lval θ' (Lloc γ) w⌝ }}}.
Proof.
  intros Hp Hproto **. iIntros "HGC Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /alloc_proto /named. iSplit; first done.
  do 3 iExists _. iFrame. subst.
  do 2 (iSplit; first by eauto with lia). iIntros "!>" (? ? ?) "(? & ? & %)".
  iApply wp_outcome; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_alloc_foreign p Ψ θ :
  p !! "alloc_foreign" = None →
  alloc_foreign_proto ⊑ Ψ →
  {{{ GC θ }}}
    (call: &"alloc_foreign" with ( ))%CE at ⟨p, Ψ⟩
  {{{ θ' γ w, RETV w;
        GC θ' ∗ γ ↦foreignO[Mut] None ∗
        ⌜repr_lval θ' (Lloc γ) w⌝ }}}.
Proof.
  intros Hp Hproto **. iIntros "HGC Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /alloc_foreign_proto /named. iSplit; first done.
  do 1 iExists _. iFrame.
  iSplit; first by eauto. iIntros "!>" (? ? ?) "(? & ? & %)".
  iApply wp_outcome; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_write_foreign p Ψ θ w γ ao a' :
  p !! "write_foreign" = None →
  write_foreign_proto ⊑ Ψ →
  repr_lval θ (Lloc γ) w →
  {{{ GC θ ∗ γ ↦foreignO[Mut] ao }}}
    (call: &"write_foreign" with (Val w, Val a'))%CE at ⟨p, Ψ⟩
  {{{ RETV (# 0); GC θ ∗ γ ↦foreign[Mut] a' }}}.
Proof.
  intros Hp Hproto **. iIntros "(HGC & ?) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /write_foreign_proto /named. iSplit; first done.
  do 5 iExists _. iFrame.
  do 2 (iSplit; first by eauto with lia). iIntros "!> [? ?]".
  iApply wp_outcome; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_read_foreign p Ψ θ w γ a m dq :
  p !! "read_foreign" = None →
  read_foreign_proto ⊑ Ψ →
  repr_lval θ (Lloc γ) w →
  {{{ GC θ ∗ γ ↦foreign[m]{dq} a }}}
    (call: &"read_foreign" with (Val w))%CE at ⟨p, Ψ⟩
  {{{ RETV a; GC θ ∗ γ ↦foreign[m]{dq} a }}}.
Proof.
  intros Hp Hproto **. iIntros "(HGC & ?) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /read_foreign_proto /named. iSplit; first done.
  do 6 iExists _. iFrame.
  do 2 (iSplit; first by eauto with lia). iIntros "!> [? ?]".
  iApply wp_outcome; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_callback p ΨML Ψ θ fc w γ f x e lv' w' v' Φ :
  p !! "callback" = None →
  callback_proto ΨML ⊑ Ψ →
  repr_lval θ (Lloc γ) w →
  repr_lval θ lv' w' →
  {{{ GC θ ∗
      current_fc fc ∗
      γ ↦clos (f, x, e) ∗
      lv' ~~ v' ∗
      (▷ WP (App (ML_lang.Val (RecV f x e)) (ML_lang.Val v')) at ⟨∅, ΨML⟩ {{ Φ }})
  }}}
    (call: &"callback" with (Val w, Val w'))%CE at ⟨p, Ψ⟩
  {{{ θ' vret lvret wret, RET wret;
        GC θ' ∗
        current_fc fc ∗
        Φ vret ∗
        lvret ~~ₒ vret ∗
        ⌜repr_lval_out θ' lvret wret⌝ }}}.
Proof.
  intros Hp Hproto **. iIntros "(? & ? & ? & ?) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /callback_proto /named. iSplit; first done.
  repeat iExists _. iFrame.
  do 2 (iSplit; first by eauto with lia). iIntros "!>"(? ? ? ?) "(? & ? & ? & ? & %)".
  iApply wp_outcome; first apply to_of_outcome.
  iApply "Cont"; by iFrame.
Qed.

Lemma wp_main p Ψ Φ P :
  p !! "main" = None →
  main_proto Φ P ⊑ Ψ →
  {{{ at_init ∗ P }}}
    (call: &"main" with ( ))%CE at ⟨p, Ψ⟩
  {{{ x, RETV code_int x; ⌜Φ x⌝ }}}.
Proof.
  intros Hp Hproto **. iIntros "(Hinit&HP) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /main_proto /named. iSplit; first done.
  iSplit; first by eauto with lia. iFrame.
  iIntros "!>" (? ?).
  iApply wp_outcome; eauto. iApply "Cont"; eauto.
Qed.

(* Macro Laws *)
Lemma wp_CAMLlocal n e2 p Ψ Φ θ f fc r :
  p !! "int2val" = None →
  int2val_proto ⊑ Ψ →
  p !! "registerlocalroot" = None →
  registerlocalroot_proto ⊑ Ψ →
  (⊢ GC θ ∗ current_fc (f :: fc) ∗ local_roots f r  -∗
     (▷ ∀ (l:loc),
     ( GC θ
     ∗ l ↦roots[f] Lint 0
     ∗ current_fc (f :: fc)
     ∗ local_roots f ({[l]} ∪ r))
     -∗ WP (subst_all {[n := #l]} e2) at ⟨ p, Ψ ⟩ {{Φ}})
     -∗ WP (CAMLlocal: n in e2)%CE    at ⟨ p, Ψ ⟩ {{Φ}}%CE)%I.
Proof.
  iIntros (? ? ? ?) "(HGC&Hfc&Hroots) Cont". unfold CAMLlocal.
  wp_apply wp_Malloc. 1-2: done. change (Z.to_nat 1) with 1. cbn.
  iIntros (l) "(Hl&_)". rewrite loc_add_0.
  wp_pures. wp_apply (wp_int2val with "[$]"); [try done..|].
  iIntros (w) "(HGC&%Hrepr)".
  wp_apply (wp_store with "Hl"). iIntros "Hl".
  wp_pures.
  wp_apply (wp_registerlocalroot with "[$]"); [try done..|].
  iIntros "(HGC&Hroot&Hfc&Hroots)". wp_pures.
  iApply "Cont". iFrame.
Qed.

Lemma wp_CAMLunregister1 (l:loc) lv p θ Ψ :
  p !! "unregisterroot" = None →
  unregisterroot_proto ⊑ Ψ →
  {{{ GC θ ∗ l ↦roots lv}}}
    (CAMLunregister1 (#l))%CE at ⟨p, Ψ⟩
  {{{ RETV #0; GC θ }}}.
Proof.
  iIntros (???) "Hin Cont".
  unfold CAMLunregister1.
  wp_apply (wp_unregisterroot with "Hin"); [done..|].
  iIntros (w) "(HGC&Hw&_)".
  wp_pures. wp_apply (wp_free with "Hw").
  iIntros "_". iApply "Cont". iApply "HGC".
Qed.

End Laws.
