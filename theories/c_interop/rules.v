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
   for any language obeying the C interface (c_interface/) -- specialized to our
   concrete C language (c_lang/). *)

Section Laws.

Context {SI : indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ, !invG Σ}.
Context `{!wrapperGCtokG Σ}.

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

Lemma wp_int2val E p Ψ θ (x : Z) :
  p !! "int2val" = None →
  int2val_proto ⊑ Ψ →
  {{{ GC θ }}}
    (call: &"int2val" with (Val #x))%CE @ ⟨p, Ψ⟩; E
  {{{ w, RET w; GC θ ∗ ⌜repr_lval θ (Lint x) w⌝ }}}.
Proof.
  iIntros (Hp Hproto Φ) "HGC Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /int2val_proto /named. iExists _, _. iFrame.
  do 2 (iSplit; first by eauto). iIntros "!>" (?) "HGC %".
  iApply wp_value; eauto. iApply "Cont"; eauto.
Qed.

Lemma wp_val2int E p Ψ θ (w:word) (x : Z) :
  p !! "val2int" = None →
  val2int_proto ⊑ Ψ →
  repr_lval θ (Lint x) w →
  {{{ GC θ }}}
    (call: &"val2int" with (Val w))%CE @ ⟨p, Ψ⟩; E
  {{{ RET (#x); GC θ }}}.
Proof.
  iIntros (Hp Hproto Hrepr Φ) "HGC Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /val2int_proto /named. iExists _, _, _. iFrame.
  do 3 (iSplit; first by eauto). iIntros "!> HGC".
  iApply wp_value; eauto. iApply "Cont"; eauto.
Qed.

Lemma wp_registerroot E p Ψ θ v w a :
  p !! "registerroot" = None →
  registerroot_proto ⊑ Ψ →
  repr_lval θ v w →
  {{{ GC θ ∗ a ↦C w }}}
    (call: &"registerroot" with (Val (# a)))%CE @ ⟨p, Ψ⟩; E
  {{{ RET (# 0); GC θ ∗ a ↦roots v }}}.
Proof.
  iIntros (Hp Hproto Hrepr Φ) "(HGC & Hpto) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /registerroot_proto /named.
  iExists _, _, _, _. iFrame.
  do 3 (iSplit; first by eauto). iIntros "!> ? ?".
  iApply wp_value; eauto. iApply "Cont"; eauto. iFrame.
Qed.

Lemma wp_unregisterroot E p Ψ θ v a :
  p !! "unregisterroot" = None →
  unregisterroot_proto ⊑ Ψ →
  {{{ GC θ ∗ a ↦roots v }}}
    (call: &"unregisterroot" with (Val (# a)))%CE @ ⟨p, Ψ⟩; E
  {{{ w, RET (# 0); GC θ ∗ a ↦C w ∗ ⌜repr_lval θ v w⌝ }}}.
Proof.
  iIntros (Hp Hproto Φ) "(HGC & Hpto) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /unregisterroot_proto /named.
  iExists _, _, _. iFrame.
  do 2 (iSplit; first by eauto). iIntros "!>" (?) "? ? %".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_modify E p Ψ θ γ w mut tg vs v' w' i :
  p !! "modify" = None →
  modify_proto ⊑ Ψ →
  repr_lval θ (Lloc γ) w →
  vblock_access_le M mut →
  repr_lval θ v' w' →
  (0 ≤ i < length vs)%Z →
  {{{ GC θ ∗ γ ↦vblk[mut] (tg, vs) }}}
    (call: &"modify" with (Val w, Val (# i), Val w'))%CE @ ⟨p, Ψ⟩; E
  {{{ RET (# 0); GC θ ∗ γ ↦vblk[mut] (tg, <[Z.to_nat i:=v']> vs) }}}.
Proof.
  intros Hp Hproto **. iIntros "(HGC & Hpto) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /modify_proto /named.
  do 9 iExists _. iFrame.
  do 7 (iSplit; first by eauto with lia). iIntros "!> ? ?".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_readfield E p Ψ θ γ w m dq tg vs i :
  p !! "readfield" = None →
  readfield_proto ⊑ Ψ →
  repr_lval θ (Lloc γ) w →
  (0 ≤ i < length vs)%Z →
  {{{ GC θ ∗ γ ↦vblk[m]{dq} (tg, vs) }}}
    (call: &"readfield" with (Val w, Val (# i)))%CE @ ⟨p, Ψ⟩; E
  {{{ v' w', RET w';
        GC θ ∗ γ ↦vblk[m]{dq} (tg, vs) ∗
        ⌜vs !! (Z.to_nat i) = Some v'⌝ ∗
        ⌜repr_lval θ v' w'⌝ }}}.
Proof.
  intros Hp Hproto **. iIntros "(HGC & Hpto) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /readfield_proto /named.
  do 8 iExists _. iFrame.
  do 5 (iSplit; first by eauto with lia). iIntros "!>" (? ?) "? ?".
  iIntros (? ?).
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_alloc tg E p Ψ θ tgnum sz :
  p !! "alloc" = None →
  alloc_proto ⊑ Ψ →
  (0 ≤ sz)%Z →
  vblock_tag_as_int tg = tgnum →
  {{{ GC θ }}}
    (call: &"alloc" with (Val (# tgnum), Val (# sz)))%CE @ ⟨p, Ψ⟩; E
  {{{ θ' γ w, RET w;
        GC θ' ∗ γ ↦fresh (tg, List.repeat (Lint 0) (Z.to_nat sz)) ∗
        ⌜repr_lval θ' (Lloc γ) w⌝ }}}.
Proof.
  intros Hp Hproto **. iIntros "HGC Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /alloc_proto /named.
  do 3 iExists _. iFrame. subst.
  do 3 (iSplit; first by eauto with lia). iIntros "!>" (? ? ?) "? ? %".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_alloc_foreign E p Ψ θ :
  p !! "alloc_foreign" = None →
  alloc_foreign_proto ⊑ Ψ →
  {{{ GC θ }}}
    (call: &"alloc_foreign" with ( ))%CE @ ⟨p, Ψ⟩; E
  {{{ θ' γ w, RET w;
        GC θ' ∗ γ ↦foreignO None ∗
        ⌜repr_lval θ' (Lloc γ) w⌝ }}}.
Proof.
  intros Hp Hproto **. iIntros "HGC Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /alloc_foreign_proto /named.
  do 1 iExists _. iFrame.
  do 2 (iSplit; first by eauto). iIntros "!>" (? ? ?) "? ? %".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_write_foreign E p Ψ θ w γ ao a' :
  p !! "write_foreign" = None →
  write_foreign_proto ⊑ Ψ →
  repr_lval θ (Lloc γ) w →
  {{{ GC θ ∗ γ ↦foreignO ao }}}
    (call: &"write_foreign" with (Val w, Val a'))%CE @ ⟨p, Ψ⟩; E
  {{{ RET (# 0); GC θ ∗ γ ↦foreign a' }}}.
Proof.
  intros Hp Hproto **. iIntros "(HGC & ?) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /write_foreign_proto /named.
  do 5 iExists _. iFrame.
  do 3 (iSplit; first by eauto with lia). iIntros "!> ? ?".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_read_foreign E p Ψ θ w γ a dq :
  p !! "read_foreign" = None →
  read_foreign_proto ⊑ Ψ →
  repr_lval θ (Lloc γ) w →
  {{{ GC θ ∗ γ ↦foreign{dq} a }}}
    (call: &"read_foreign" with (Val w))%CE @ ⟨p, Ψ⟩; E
  {{{ RET a; GC θ ∗ γ ↦foreign{dq} a }}}.
Proof.
  intros Hp Hproto **. iIntros "(HGC & ?) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /read_foreign_proto /named.
  do 5 iExists _. iFrame.
  do 3 (iSplit; first by eauto with lia). iIntros "!> ? ?".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_callback E p ΨML Ψ θ w γ f x e lv' w' v' Φ :
  p !! "callback" = None →
  callback_proto E ΨML ⊑ Ψ →
  repr_lval θ (Lloc γ) w →
  repr_lval θ lv' w' →
  {{{ GC θ ∗
      γ ↦clos (f, x, e) ∗
      lv' ~~ v' ∗
      (▷ WP (App (ML_lang.Val (RecV f x e)) (ML_lang.Val v')) @ ⟨∅, ΨML⟩; E {{ Φ }})
  }}}
    (call: &"callback" with (Val w, Val w'))%CE @ ⟨p, Ψ⟩; E
  {{{ θ' vret lvret wret, RET wret;
        GC θ' ∗
        Φ vret ∗
        lvret ~~ vret ∗
        ⌜repr_lval θ' lvret wret⌝ }}}.
Proof.
  intros Hp Hproto **. iIntros "(? & ? & ? & ?) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /callback_proto /named.
  do 10 iExists _. iFrame.
  do 4 (iSplit; first by eauto with lia). iIntros "!>" (? ? ? ?) "? ? ? %".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

Lemma wp_main e E E' p ΨML Ψ Φ :
  p !! "main" = None →
  main_proto E' e ΨML ⊑ Ψ →
  {{{ at_init ∗
      (▷ WP e @ ⟨∅, ΨML⟩; E' {{ Φ }})
  }}}
    (call: &"main" with ( ))%CE @ ⟨p, Ψ⟩; E
  {{{ θ' vret lvret wret, RET wret;
        GC θ' ∗
        Φ vret ∗
        lvret ~~ vret ∗
        ⌜repr_lval θ' lvret wret⌝ }}}.
Proof.
  intros Hp Hproto **. iIntros "(Hinit&HWP) Cont".
  wp_pures. wp_extern; first done.
  iModIntro. cbn. iApply Hproto.
  rewrite /main_proto /named.
  iExists Φ. iFrame.
  do 2 (iSplit; first by eauto with lia). iIntros "!>" (? ? ? ?) "? ? ? %".
  iApply wp_value; eauto. iApply "Cont"; eauto. by iFrame.
Qed.

(* Macro Laws *)
Lemma wp_CAMLlocal n e2 E p Ψ Φ θ :
  p !! "int2val" = None →
  int2val_proto ⊑ Ψ →
  p !! "registerroot" = None →
  registerroot_proto ⊑ Ψ →
  (⊢ GC θ -∗ 
     (▷ ∀ (l:loc), GC θ ∗ l ↦roots Lint 0 -∗ WP (subst_all {[n := #l]} e2) @ ⟨ p, Ψ ⟩; E {{Φ}}) -∗
     WP (CAMLlocal: n in e2)%CE @ ⟨ p, Ψ ⟩ ; E
     {{Φ}}%CE)%I.
Proof.
  iIntros (????) "HGC Cont". unfold CAMLlocal.
  wp_apply wp_Malloc. 1-2: done. change (Z.to_nat 1) with 1. cbn.
  iIntros (l) "((Hl&_)&_)". rewrite loc_add_0.
  wp_pures. wp_apply (wp_int2val with "[$]"); [try done..|].
  iIntros (w) "(HGC&%Hrepr)".
  wp_apply (wp_store with "Hl"). iIntros "Hl".
  wp_pures.
  wp_apply (wp_registerroot with "[$]"); [try done..|].
  iIntros "(HGC&Hroot)". wp_pures.
  iApply "Cont". iFrame.
Qed.

Lemma wp_CAMLunregister1 (l:loc) lv E p θ Ψ :
  p !! "unregisterroot" = None →
  unregisterroot_proto ⊑ Ψ →
  {{{ GC θ ∗ l ↦roots lv}}}
    (CAMLunregister1 (#l))%CE @ ⟨p, Ψ⟩; E
  {{{ RET (#0); GC θ }}}.
Proof.
  iIntros (???) "Hin Cont".
  unfold CAMLunregister1.
  wp_apply (wp_unregisterroot with "Hin"); [done..|].
  iIntros (w) "(HGC&Hw&_)".
  wp_pures. wp_apply (wp_free with "Hw").
  iIntros "_". iApply "Cont". iApply "HGC".
Qed.

End Laws.
