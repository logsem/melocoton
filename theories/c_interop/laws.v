From iris.proofmode Require Import proofmode.
From melocoton.interop Require Import basics basics_resources weakestpre wp_update_laws.
From melocoton.ml_lang Require Import primitive_laws.
From melocoton.c_interface Require Export resources.
From melocoton.c_lang Require Import primitive_laws tactics notation proofmode.
From iris.prelude Require Import options.

(* Derived laws for C<->ML interop.

   These follow from the generic rules of the wrapper (in interop/) that work
   for any language obeying the C interface (c_interface/) -- specialized to our
   concrete C language (c_lang/). *)

Section Laws.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ, !invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Lemma store_to_root E pe (l:loc) (v v' : lval) w θ :
  repr_lval θ v w →
  {{{ GC θ ∗ l ↦roots v' }}}
     (#l <- w)%E @ pe; E
  {{{ RET LitV LitUnit; GC θ ∗ l ↦roots v }}}.
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
     ( * #l)%E @ pe; E
  {{{ w, RET w; l ↦roots{dq} v ∗ GC θ ∗ ⌜repr_lval θ v w⌝ }}}.
Proof.
  iIntros (Φ) "(HGC&Hroot) HΦ".
  iDestruct (access_root with "[$HGC $Hroot]") as (w') "(Hpto & %Hrepr & Hupd)".
  iApply (wp_load with "Hpto"). iIntros "!> Hpto".
  iDestruct ("Hupd" with "Hpto") as "(?&?)". iApply "HΦ". by iFrame.
Qed.

End Laws.
