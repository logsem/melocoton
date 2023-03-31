From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources.
From melocoton.interop Require Import lang weakestpre update_laws wp_utils prims_proto.
From melocoton.language Require Import weakestpre progenv.
From melocoton.c_interop Require Import rules notation.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import mlang_instantiation lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.c_lang Require Import notation proofmode.
From melocoton.examples Require Import compression.


Section C_code.

(** our code differs from the original in the paper as follows:

The paper has a record
------------------
|used_ref|cap|blk|
------------------
  ↓
------
|used|
------
where used_ref is a reference/mutable field

Since we don't have records, only two-value pairs, our value looks as follows (aux_ref is supposed to be another pair)
------------------
|used_ref|aux_ref|
------------------
  ↓          ↓
------   ---------
|used|   |cap|blk|
------   ---------

Additionally, we do not CAMLparam/CAMLlocal variables that
* are integers
* don't have to survive an allocation

Finally, note that the Store_field(&Field(x,y,z)) is syntactic sugar -- no addresses are being taken.
In general, our toy version of C does not have local variables, nor the notion of "taking an address".
Instead, everything that needs to be mutable must be heap-allocated (and freed at the end).
*)

Definition buf_alloc_code (cap : expr) : expr :=
  CAMLlocal: "bk" in 
  CAMLlocal: "bf" in 
  CAMLlocal: "bf2" in 
  "bk" <- caml_alloc_custom ( ) ;;
  (Custom_contents ( *"bk" ) :=  malloc(Int_val (cap))) ;;
  "bf"    <- caml_alloc (#2, #0) ;;
  "bf2"   <- caml_alloc (#2, #0) ;;
  let: "bfref" := caml_alloc (#1, #0) in
  Store_field ( &Field(  "bfref", #0), Val_int (#0)) ;;
  Store_field ( &Field( *"bf", #0), "bfref") ;;
  Store_field ( &Field( *"bf", #1), *"bf2") ;;
  Store_field ( &Field( *"bf2", #0), cap) ;;
  Store_field ( &Field( *"bf2", #1), *"bk") ;;
  CAMLreturn: * "bf" unregistering ["bk", "bf", "bf2"].
Definition buf_alloc_fun := Fun [BNamed "cap"] (buf_alloc_code "cap") .
Definition buf_alloc_name := "buf_alloc".


Definition buf_upd_code (iv jv f_arg bf_arg : expr) : expr :=
  CAMLlocal: "f" in "f" <- f_arg ;;
  CAMLlocal: "bf" in "bf" <- bf_arg ;;
  let: "bts" := Custom_contents(Field(Field("bf", #1), #1)) in
  let: "j" := Int_val ( jv ) in
  let: "i" := malloc ( #1 ) in
  "i" <- Int_val ( iv ) ;;
  while: * "i" ≤ "j" do
    ( "bts" +ₗ ( *"i") <- Int_val (call: &"callback" with ( *"f", Val_int ( *"i"))) ;;
      if: Int_val(Field(Field("bf", #0), #0)) < *"i" + #1
      then Store_field (&Field(Field("bf", #0), #0), Val_int ( *"i" + #1))
      else Skip ;;
      "i" <- *"i" + #1 ) ;;
  free ("i", #1);;
  CAMLreturn: Int_val (#0) unregistering ["f", "bf"].
Definition buf_upd_fun := Fun [BNamed "iv"; BNamed "jv"; BNamed "f_arg"; BNamed "bf_arg"]
                              (buf_upd_code "iv" "jv" "f_arg" "bf_arg").
Definition buf_upd_name := "buf_upd".

Definition wrap_max_len_code (i : expr) : expr :=
   Val_int (call: &buffy_max_len_name with (Int_val (i))).
Definition wrap_max_len_fun := Fun [BNamed "i"] (wrap_max_len_code "i").
Definition wrap_max_len_name := "wrap_max_len".

Definition wrap_compress_code (bf1 bf2 : expr) : expr :=
  let: "bts1" := Custom_contents(Field(Field(bf1, #1), #1)) in
  let: "bts2" := Custom_contents(Field(Field(bf2, #1), #1)) in
  let: "used1" := Int_val(Field(Field(bf1, #0), #0)) in
  let: "cap2p" := malloc(#1) ;; "cap2p" <- Int_val(Field(Field(bf2, #1), #0)) in
  let: "res" := call: &buffy_compress_name with ("bts1", "used1", "bts2", "cap2p") in
  Store_field(&Field(Field(bf2, #0), #0), Val_int( *"cap2p")) ;;
  free ("cap2p", #1) ;;
  if: "res" = #0 then Val_int(#1) else Val_int(#0).
Definition wrap_compress_fun := Fun [BNamed "bf1"; BNamed "bf2"] (wrap_compress_code "bf1" "bf2").
Definition wrap_compress_name := "wrap_compress".

Definition buf_lib_prog : lang_prog C_lang :=
  <[wrap_compress_name := wrap_compress_fun]> (
  <[wrap_max_len_name  := wrap_max_len_fun]> (
  <[buf_upd_name       := buf_upd_fun]> (
  <[buf_alloc_name     := buf_alloc_fun]>
    buffy_env ))).

End C_code.

Section Specs.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.

  Definition wrap_funcs_code E e Ψ : prog_environ C_lang Σ := {|
    penv_prog  := buf_lib_prog ;
    penv_proto := prims_proto E e Ψ |}.

  Definition isBufferForeignBlock (γ : lloc) (b:buffer) cap fid : iProp Σ := 
      ∃ (ℓbuf : loc) vused vrest, 
        "Hγfgnpto" ∷ γ ↦foreign (#ℓbuf)
      ∗ "#Hγfgnsim" ∷ γ ~foreign~ fid
      ∗ "Hℓbuf" ∷ ℓbuf ↦C∗ (vused++vrest)
      ∗ "%HisBuf" ∷ ⌜isBuffer vused b⌝
      ∗ "<-" ∷ ⌜length (vused++vrest) = cap⌝.

  Definition isBufferRecord (lv : lval) (b:buffer) (cap:nat) : iProp Σ :=
    ∃ (γ γref γaux γfgn : lloc) (used : nat) fid,
        "->" ∷ ⌜lv = Lloc γ⌝
      ∗ "#Hγbuf" ∷ γ ↦imm (TagDefault, [Lloc γref; Lloc γaux])
      ∗ "Hγusedref" ∷ γref ↦mut (TagDefault, [Lint used])
      ∗ "#Hγaux" ∷ γaux ↦imm (TagDefault, [Lint cap; Lloc γfgn])
      ∗ "Hbuf" ∷ isBufferForeignBlock γfgn b cap fid
      ∗ "->" ∷ ⌜used = length b⌝.

  Definition isBufferRecordML (v : MLval) (b:buffer) (cap:nat) : iProp Σ :=
    ∃ (ℓML:loc) (used fid:nat) γfgn, 
      "->" ∷ ⌜v = (ML_lang.LitV ℓML, (ML_lang.LitV cap, ML_lang.LitV (LitForeign fid)))%MLV⌝ 
    ∗ "HℓbufML" ∷ ℓML ↦M ML_lang.LitV used
    ∗ "Hbuf" ∷ isBufferForeignBlock γfgn b cap fid
    ∗ "->" ∷ ⌜used = length b⌝.

  Lemma bufToML lv b c θ:
      GC θ
   -∗ isBufferRecord lv b c
  ==∗ GC θ ∗ ∃ v, isBufferRecordML v b c ∗ lv ~~ v.
  Proof.
    iIntros "HGC H". iNamed "H". iNamed "Hbuf".
    iMod (mut_to_ml _ ([ML_lang.LitV (length b)]) with "[$HGC $Hγusedref]") as "(HGC&(%ℓML&HℓbufML&#HγML))".
    1: by cbn.
    iModIntro. iFrame "HGC".
    iExists _. iSplitL.
    { iExists ℓML, _, fid, γfgn. unfold named.
      iSplit; first done. iFrame "HℓbufML". iSplit; last done.
      iExists ℓbuf, vused, vrest.
      unfold named. by iFrame "Hγfgnpto Hℓbuf Hγfgnsim". }
    { cbn. iExists _, _, _. iSplitL; first done.
      iFrame "Hγbuf".
      iSplitL; first (iExists _; iSplit; done).
      iExists _, _, _. iSplit; first done.
      iFrame "Hγaux". iSplit; first done.
      iExists _; iSplit; done. }
  Qed.

  Lemma bufToC v b c lv θ:
      GC θ
   -∗ isBufferRecordML v b c
   -∗ lv ~~ v
  ==∗ GC θ ∗ isBufferRecord lv b c.
  Proof.
    iIntros "HGC H Hsim". iNamed "H". iNamed "Hbuf".
    iDestruct "Hsim" as "#(%γ&%&%&->&Hγbuf&(%γref&->&Hsim)&%γaux&%&%&->&Hγaux&->&%γfgn2&->&Hγfgnsim2)".
    iPoseProof (lloc_own_foreign_inj with "Hγfgnsim2 Hγfgnsim [$]") as "(HGC&%Hiff)".
    destruct Hiff as [_ ->]; last done.
    iMod (ml_to_mut with "[$HGC $HℓbufML]") as "(HGC&(%ℓvs&%γref2&Hγusedref&#Hsim2&#Hγrefsim))".
    iPoseProof (lloc_own_pub_inj with "Hsim2 Hsim [$]") as "(HGC&%Hiff)".
    destruct Hiff as [_ ->]; last done.
    iModIntro. iFrame "HGC".
    iExists _, _, _, _, _, _. unfold named.
    iSplit; first done.
    iFrame "Hγbuf". iFrame "Hγaux".
    iSplitL "Hγusedref".
    { destruct ℓvs as [|ℓvs [|??]]; cbn; try done.
      all: iDestruct "Hγrefsim" as "[-> ?]"; try done. }
    { iSplit; last done.
      cbn. iExists _, _, _. unfold named. iFrame "Hγfgnpto Hγfgnsim Hℓbuf".
      iPureIntro; done. }
  Qed.


  Import melocoton.ml_lang.notation.

  Definition buf_alloc_spec_ML s vv Φ : iProp Σ :=
    ∃ (z:Z),
      ⌜(0 < z)%Z⌝
    ∗ ⌜s = buf_alloc_name⌝
    ∗ ⌜vv = [ #z ]⌝
    ∗ ▷ (∀ v, isBufferRecordML v [] (Z.to_nat z) -∗ Φ v).

End Specs.

Section Proofs.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.

  Lemma buf_alloc_correct E1 E2 e Ψ :
    wrap_proto buf_alloc_spec_ML ⊑ prog_proto E2 buf_lib_prog (prims_proto E1 e Ψ).
  Proof.
    iIntros (s ws Φ) "H". iNamed "H".
    iDestruct "Hproto" as "(%cap&%Hcap&->&->&HΦ')".
    cbn. unfold prog_proto. solve_lookup_fixed.
    destruct lvs as [|lv [|??]]; first done.
    all: cbn; iDestruct "Hsim" as "(->&H)"; try done.
    destruct ws as [|w [|??]]; try (eapply Forall2_length in Hrepr; cbn in Hrepr; done).
    eapply Forall2_cons_inv_l in Hrepr as (wcap&?&Hlval&_&?); simplify_eq.
    cbn. iExists _. solve_lookup_fixed.
    iSplit; first done. iNext.
    wp_apply (wp_CAMLlocal with "HGC"); [done..|].
    iIntros (ℓbk) "(HGC&Hℓbk)"; wp_pures.
    wp_apply (wp_CAMLlocal with "HGC"); [done..|].
    iIntros (ℓbf) "(HGC&Hℓbf)"; wp_pures.
    wp_apply (wp_CAMLlocal with "HGC"); [done..|].
    iIntros (ℓbf2) "(HGC&Hℓbf2)". wp_finish.
    wp_apply (wp_alloc_foreign with "HGC"); [done..|].
    iIntros (θ1 γbk wbk) "(HGC&Hγbk&%Hbk'1)".
    wp_apply (store_to_root with "[$HGC $Hℓbk]"); [done..|].
    iIntros "(HGC&Hℓbk)". wp_pures.
    wp_apply (load_from_root with "[$HGC $Hℓbk]"); [done..|].
    iIntros (w) "(Hℓbk&HGC&%Hbk'1b)".
    wp_apply (wp_val2int with "HGC"); [try done..|].
    1: by eapply repr_lval_lint.
    iIntros "HGC".
    wp_apply (wp_Malloc); [try done..|].
    iIntros (ℓbts) "(Hbts&_)".
    wp_apply (wp_write_foreign with "[$HGC $Hγbk]"); [try done..|].
    iIntros "(HGC&Hγbk)". wp_pure _.
    wp_apply (wp_alloc TagDefault with "HGC"); [done..|].
    iIntros (θ2 γbf wbf) "(HGC&Hγbf&%Hbf'1)".
    wp_apply (store_to_root with "[$HGC $Hℓbf]"); [done..|].
    iIntros "(HGC&Hℓbf)". wp_pure _.
    wp_apply (wp_alloc TagDefault with "HGC"); [done..|].
    iIntros (θ3 γbf2 wbf2) "(HGC&Hγbf2&%Hbf2'1)".
    wp_apply (store_to_root with "[$HGC $Hℓbf2]"); [done..|].
    iIntros "(HGC&Hℓbf2)". wp_pure _.
    wp_apply (wp_alloc TagDefault with "HGC"); [done..|].
    iIntros (θ4 γbfref wbfref) "(HGC&Hγbfref&%Hbfref'1)".
    wp_pure _.
    wp_apply (wp_int2val with "HGC"); [done..|].
    iIntros (wunit) "(HGC&%Hwunit)".
    wp_apply (wp_modify with "[$HGC $Hγbfref]"); [done..|].
    iIntros "(HGC&Hγbfref)".
    wp_pure _.
    wp_apply (load_from_root with "[$HGC $Hℓbf]"); [done..|].
    iIntros (wbf'4) "(Hℓbf&HGC&%Hbf'4)".
    wp_apply (wp_modify with "[$HGC $Hγbf]"); [done..|].
    iIntros "(HGC&Hγbf)".
    wp_pure _.
    wp_apply (load_from_root with "[$HGC $Hℓbf]"); [done..|].
    iIntros (wbf'4') "(Hℓbf&HGC&%Hbf'4')".
    wp_apply (load_from_root with "[$HGC $Hℓbf2]"); [done..|].
    iIntros (wbf2'4) "(Hℓbf2&HGC&%Hbf2'4)".
    wp_apply (wp_modify with "[$HGC $Hγbf]"); [done..|].
    iIntros "(HGC&Hγbf)".
    wp_pure _.
    wp_apply (load_from_root with "[$HGC $Hℓbf2]"); [done..|].
    iIntros (wbf2'4') "(Hℓbf2&HGC&%Hbf2'4')".
    wp_apply (wp_modify with "[$HGC $Hγbf2]"); [try done..|].
    1: by eapply repr_lval_lint.
    iIntros "(HGC&Hγbf2)".
    wp_pure _.

    wp_apply (load_from_root with "[$HGC $Hℓbf2]"); [done..|].
    iIntros (wbf2'4'') "(Hℓbf2&HGC&%Hbf2'4'')".
    wp_apply (load_from_root with "[$HGC $Hℓbk]"); [done..|].
    iIntros (wbk'4') "(Hℓbk&HGC&%Hbk'4')".
    wp_apply (wp_modify with "[$HGC $Hγbf2]"); [done..|].
    iIntros "(HGC&Hγbf2)".
    wp_pure _.

    wp_apply (load_from_root with "[$HGC $Hℓbf]"); [done..|].
    iIntros (wbf'4'') "(Hℓbf&HGC&%Hbf'4'')". wp_pure _.
    wp_apply (wp_CAMLunregister1 with "[$HGC $Hℓbk]"); [done..|].
    iIntros "HGC". wp_pure _.
    wp_apply (wp_CAMLunregister1 with "[$HGC $Hℓbf]"); [done..|].
    iIntros "HGC". wp_pure _.
    wp_apply (wp_CAMLunregister1 with "[$HGC $Hℓbf2]"); [done..|].
    iIntros "HGC". wp_pure _.
    change (Z.to_nat 0) with 0.
    change (Z.to_nat 1) with 1.
    change (Z.to_nat 2) with 2.
    cbn.
    iMod (freeze_to_immut with "[$HGC $Hγbf]") as "(HGC&Hγbf)".
    iMod (freeze_to_immut with "[$HGC $Hγbf2]") as "(HGC&Hγbf2)".
    iMod (freeze_to_mut with "[$HGC $Hγbfref]") as "(HGC&Hγbfref)".
    iAssert (isBufferRecord (Lloc γbf) [] (Z.to_nat cap)) with "[Hγbk Hγbf Hγbf2 Hγbfref Hbts]" as "Hbuffer".
    { iDestruct "Hγbk" as "(Hγbk'&%fid&#Hfid)".
      assert (∃ k, Z.of_nat k = cap) as (ncap&<-) by (exists (Z.to_nat cap); lia).
      rewrite !Nat2Z.id.
      iExists γbf, γbfref, γbf2, γbk, 0, fid. unfold named. iFrame.
      iSplit; first done. iSplit; last done.
      iExists ℓbts, [], (replicate ncap None). unfold named, lstore_own_foreign.
      iFrame. iFrame "Hfid". iSplitL; first by iExists fid. iPureIntro; split_and!.
      1: done.
      cbn. by rewrite replicate_length. }
    iMod (bufToML with "HGC Hbuffer") as "(HGC&%vv&Hbuffer&#Hsim)".
    iModIntro. iApply ("Cont" with "HGC (HΦ' Hbuffer) Hsim [//]").
  Qed.

End Proofs.