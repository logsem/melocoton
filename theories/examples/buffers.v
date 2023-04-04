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
From melocoton.c_lang Require Import notation proofmode derived_laws.
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
Instead, everything that needs to be mutable must be heap-allocated (and preferably freed at the end).
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
  let: "bts" := Custom_contents(Field(Field( *"bf", #1), #1)) in
  let: "j" := Int_val ( jv ) in
  let: "i" := malloc ( #1 ) in
  "i" <- Int_val ( iv ) ;;
 (while: * "i" ≤ "j" do
    ( "bts" +ₗ ( *"i") <- Int_val (call: &"callback" with ( *"f", Val_int ( *"i"))) ;;
     (if: Int_val(Field(Field( *"bf", #0), #0)) < *"i" + #1
      then Store_field (&Field(Field( *"bf", #0), #0), Val_int ( *"i" + #1))
      else Skip) ;;
      "i" <- *"i" + #1 )) ;;
  free ("i", #1);;
  CAMLreturn: Val_int (#0) unregistering ["f", "bf"].
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
  let: "cap2p" := malloc(#1) in
 ("cap2p" <- Int_val(Field(Field(bf2, #1), #0))) ;;
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

  Definition wrap_funcs_code E Ψ : prog_environ C_lang Σ := {|
    penv_prog  := buf_lib_prog ;
    penv_proto := prims_proto E Ψ |}.

  Definition isBufferForeignBlock (γ : lloc) (ℓbuf : loc) (Pb : list (option Z) → iProp Σ) cap fid : iProp Σ := 
      ∃ vcontent, 
        "Hγfgnpto" ∷ γ ↦foreign (#ℓbuf)
      ∗ "#Hγfgnsim" ∷ γ ~foreign~ fid
      ∗ "Hℓbuf" ∷ ℓbuf ↦C∗ (map (option_map (λ (z:Z), #z)) vcontent)
      ∗ "HContent" ∷ Pb vcontent
      ∗ "->" ∷ ⌜cap = length vcontent⌝.

  Lemma isBufferForeignBlock_ext γ ℓbuf Pb1 Pb2 cap fid :
     (∀ lst, □ (Pb1 lst -∗ Pb2 lst))
  -∗ isBufferForeignBlock γ ℓbuf Pb1 cap fid
  -∗ isBufferForeignBlock γ ℓbuf Pb2 cap fid.
  Proof.
    iIntros "#Hiff Hbuf". iNamed "Hbuf".
    iExists vcontent; unfold named; iFrame.
    iFrame "Hγfgnsim". iSplit; last done.
    by iApply "Hiff".
  Qed.

  Definition isBufferRecord (lv : lval) (ℓbuf : loc) (Pb : nat → list (option Z) → iProp Σ) (cap:nat) : iProp Σ :=
    ∃ (γ γref γaux γfgn : lloc) (used : nat) fid,
        "->" ∷ ⌜lv = Lloc γ⌝
      ∗ "#Hγbuf" ∷ γ ↦imm (TagDefault, [Lloc γref; Lloc γaux])
      ∗ "Hγusedref" ∷ γref ↦mut (TagDefault, [Lint used])
      ∗ "#Hγaux" ∷ γaux ↦imm (TagDefault, [Lint cap; Lloc γfgn])
      ∗ "Hbuf" ∷ isBufferForeignBlock γfgn ℓbuf (Pb used) cap fid.

  Definition isBufferRecordML (v : MLval) (ℓbuf : loc)  (Pb : nat → list (option Z) → iProp Σ) (cap:nat) : iProp Σ :=
    ∃ (ℓML:loc) (used fid:nat) γfgn, 
      "->" ∷ ⌜v = (ML_lang.LitV ℓML, (ML_lang.LitV cap, ML_lang.LitV (LitForeign fid)))%MLV⌝ 
    ∗ "HℓbufML" ∷ ℓML ↦M ML_lang.LitV used
    ∗ "Hbuf" ∷ isBufferForeignBlock γfgn ℓbuf (Pb used) cap fid.


  Lemma isBufferRecordML_ext v ℓbuf Pb1 Pb2 cap :
     (∀ z lst, □ (Pb1 z lst -∗ Pb2 z lst))
  -∗ isBufferRecordML v ℓbuf Pb1 cap
  -∗ isBufferRecordML v ℓbuf Pb2 cap.
  Proof.
    iIntros "#Hiff Hbuf". iNamed "Hbuf".
    iExists ℓML, used, fid, γfgn; unfold named; iFrame.
    iSplit; first done.
    iApply (isBufferForeignBlock_ext with "[] Hbuf").
    iApply "Hiff".
  Qed.

  Lemma bufToML lv ℓbuf Pb c θ:
      GC θ
   -∗ isBufferRecord lv ℓbuf Pb c
  ==∗ GC θ ∗ ∃ v, isBufferRecordML v ℓbuf Pb c ∗ lv ~~ v.
  Proof.
    iIntros "HGC H". iNamed "H". iNamed "Hbuf".
    iMod (mut_to_ml _ ([ML_lang.LitV used]) with "[$HGC $Hγusedref]") as "(HGC&(%ℓML&HℓbufML&#HγML))".
    1: by cbn.
    iModIntro. iFrame "HGC".
    iExists _. iSplitL.
    { iExists ℓML, _, fid, γfgn. unfold named.
      iSplit; first done. iFrame "HℓbufML".
      iExists vcontent.
      unfold named. by iFrame "Hγfgnpto Hℓbuf Hγfgnsim HContent". }
    { cbn. iExists _, _, _. iSplitL; first done.
      iFrame "Hγbuf".
      iSplitL; first (iExists _; iSplit; done).
      iExists _, _, _. iSplit; first done.
      iFrame "Hγaux". iSplit; first done.
      iExists _; iSplit; done. }
  Qed.

  Lemma bufToC v ℓbuf Pb c lv θ:
      GC θ
   -∗ isBufferRecordML v ℓbuf Pb c
   -∗ lv ~~ v
  ==∗ GC θ ∗ isBufferRecord lv ℓbuf Pb c ∗ ∃ (ℓML:loc) fid, ⌜v = (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid)))%MLV⌝.
  Proof.
    iIntros "HGC H Hsim". iNamed "H". iNamed "Hbuf".
    iDestruct "Hsim" as "#(%γ&%&%&->&Hγbuf&(%γref&->&Hsim)&%γaux&%&%&->&Hγaux&->&%γfgn2&->&Hγfgnsim2)".
    iPoseProof (lloc_own_foreign_inj with "Hγfgnsim2 Hγfgnsim [$]") as "(HGC&%Hiff)".
    destruct Hiff as [_ ->]; last done.
    iMod (ml_to_mut with "[$HGC $HℓbufML]") as "(HGC&(%ℓvs&%γref2&Hγusedref&#Hsim2&#Hγrefsim))".
    iPoseProof (lloc_own_pub_inj with "Hsim2 Hsim [$]") as "(HGC&%Hiff)".
    destruct Hiff as [_ ->]; last done.
    iModIntro. iFrame "HGC". iSplit; last by repeat iExists _. 
    iExists _, _, _, _, _, _. unfold named.
    iSplit; first done.
    iFrame "Hγbuf". iFrame "Hγaux".
    iSplitL "Hγusedref".
    { destruct ℓvs as [|ℓvs [|??]]; cbn; try done.
      all: iDestruct "Hγrefsim" as "[-> ?]"; try done. }
    { cbn. iExists _. unfold named. iFrame "Hγfgnpto Hγfgnsim Hℓbuf HContent".
      iPureIntro; done. }
  Qed.

  Lemma bufToC_fixed ℓbuf Pb (c:nat) ℓML fid lv θ:
      GC θ
   -∗ isBufferRecordML (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid))) ℓbuf Pb c
   -∗ lv ~~ (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid)))
  ==∗ GC θ ∗ isBufferRecord lv ℓbuf Pb c.
  Proof.
    iIntros "HGC H #Hsim".
    iMod (bufToC with "HGC H Hsim") as "($&$&%ℓML1&%fid1&%Href)". done.
  Qed.

  Lemma bufToML_fixed lv ℓbuf Pb c (ℓML:loc) fid θ:
      GC θ
   -∗ isBufferRecord lv ℓbuf Pb c
   -∗ lv ~~ (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid)))
  ==∗ GC θ ∗ isBufferRecordML (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid))) ℓbuf Pb c.
  Proof.
    iIntros "HGC H #Hsim".
    iMod (bufToML with "HGC H") as "(HGC&%&HML&#Hsim2)".
    iAssert (⌜v = (ML_lang.LitV ℓML, (ML_lang.LitV c, ML_lang.LitV (LitForeign fid)))%MLV⌝)%I as "->"; last by iFrame.
    iNamed "HML".
    cbn.
    iDestruct "Hsim" as "#(%γ&%&%&->&Hγbuf&(%γref&->&Hsim)&%γaux&%&%&->&Hγaux&->&%γfgn2&->&Hγfgnsim2)".
    iDestruct "Hsim2" as "#(%γ2&%&%&%HHH&Hγbuf2&(%γref2&->&Hsim2)&%γaux2&%&%&->&Hγaux2&->&%γfgn3&->&Hγfgnsim3)".
    simplify_eq.
    unfold lstore_own_vblock, lstore_own_elem; cbn.
    iDestruct "Hγbuf" as "(Hγbuf&_)".
    iDestruct "Hγbuf2" as "(Hγbuf2&_)".
    iDestruct "Hγaux" as "(Hγaux&_)".
    iDestruct "Hγaux2" as "(Hγaux2&_)".
    iPoseProof (ghost_map.ghost_map_elem_agree with "Hγbuf Hγbuf2") as "%Heq1"; simplify_eq.
    iPoseProof (ghost_map.ghost_map_elem_agree with "Hγaux Hγaux2") as "%Heq1"; simplify_eq.
    iPoseProof (lloc_own_foreign_inj with "Hγfgnsim2 Hγfgnsim3 HGC") as "(HGC&%Heq1)"; simplify_eq.
    iPoseProof (lloc_own_pub_inj with "Hsim Hsim2 HGC") as "(HGC&%Heq2)"; simplify_eq.
    iPureIntro. f_equal; repeat f_equal.
    - symmetry; by eapply Heq2.
    - symmetry; by eapply Heq1.
  Qed.


  Import melocoton.ml_lang.notation.
  Definition buf_alloc_res_buffer z cap (b : list (option Z)) : iProp Σ := ⌜cap = 0⌝ ∗ ⌜b = replicate (Z.to_nat z) None⌝.
  Definition buf_alloc_spec_ML s vv Φ : iProp Σ :=
    ∃ (z:Z),
      ⌜(0 < z)%Z⌝
    ∗ ⌜s = buf_alloc_name⌝
    ∗ ⌜vv = [ #z ]⌝
    ∗ ▷ (∀ v ℓbuf, isBufferRecordML v ℓbuf (buf_alloc_res_buffer z) (Z.to_nat z) -∗ meta_token ℓbuf ⊤ -∗ Φ v).

  Definition buf_alloc1_spec idx vnew Pbold cap (b : list (option Z)) : iProp Σ :=
    ∃ bold (capold:nat) , ⌜b = <[ Z.to_nat idx := Some vnew ]> bold⌝ ∗ ⌜cap = max capold (Z.to_nat (idx+1))⌝ ∗ Pbold capold bold.
  Definition buf_update_spec_ML (protoCB : (protocol ML_lang.val Σ)) E s vv Φ: iProp Σ :=
    ∃ (Ψ Ψframe : Z → iProp Σ) (Φz : Z → iProp Σ) (i j : Z) ℓbuf (cap:nat) (Pb : Z → nat → _ → iProp Σ) vbuf b1 b2 (F : ML_lang.expr),
      "->" ∷ ⌜s = buf_upd_name⌝
    ∗ "->" ∷ ⌜vv = [ #i; #j; (RecV b1 b2 F); vbuf ]⌝
    ∗ "%Hb1" ∷ ⌜0%Z ≤ i⌝%Z
    ∗ "%Hb2" ∷ ⌜i ≤ j+1⌝%Z
    ∗ "%Hb3" ∷ ⌜j < cap⌝%Z
    ∗ "#HMerge" ∷ (□ ∀ z vnew, ⌜i ≤ z⌝%Z -∗ ⌜z ≤ j+1⌝%Z -∗ Ψframe z -∗ Φz vnew -∗
          isBufferRecordML vbuf ℓbuf (buf_alloc1_spec z vnew (Pb z)) cap ==∗ Ψ (z+1)%Z)
    ∗ "#HWP" ∷ (□ ∀ z, ⌜i ≤ z⌝%Z -∗ ⌜z ≤ j⌝%Z -∗ Ψ z -∗ 
              WP (RecV b1 b2 F) #z @ ⟨ ∅, protoCB ⟩ ; E 
              {{res, ∃ (znew:Z), ⌜res = #znew⌝ ∗ Φz znew ∗ Ψframe (z)%Z
                               ∗ isBufferRecordML vbuf ℓbuf (Pb (z)%Z) cap}})
    ∗ "Hframe" ∷ Ψframe i
    ∗ "Hrecord" ∷ isBufferRecordML vbuf ℓbuf (Pb i) cap
    ∗ "HMergeInitial" ∷ (Ψframe i ∗ isBufferRecordML vbuf ℓbuf (Pb i) cap ==∗ Ψ i)
    ∗ "HCont" ∷ ▷ (Ψ (j+1)%Z -∗ Φ #()).

  Definition wrap_max_len_ML s vv Φ : iProp Σ :=
    ∃ (n:nat),
      "->" ∷ ⌜s = wrap_max_len_name⌝
    ∗ "->" ∷ ⌜vv = [ #n ]⌝
    ∗ "HCont" ∷ ▷ Φ #(buffer_max_len n).

  Definition wrap_compress_ML s vv Φ : iProp Σ :=
    ∃ v1 v2 ℓ1 ℓ2 (vcompress:buffer) vrest1 Pb1 Pb2 cap1 cap2,
      "->" ∷ ⌜s = wrap_compress_name⌝
    ∗ "->" ∷ ⌜vv = [ v1 ; v2 ]⌝
    ∗ "%Hcap" ∷ ⌜buffer_max_len (length vcompress) ≤ cap2⌝
    ∗ "HBuf1" ∷ isBufferRecordML v1 ℓ1 (λ z vb, ⌜vb = map Some vcompress ++ vrest1⌝ ∗ ⌜length vcompress = z⌝ ∗ Pb1 z vb) cap1
    ∗ "HBuf2" ∷ isBufferRecordML v2 ℓ2 Pb2 cap2
    ∗ "HCont" ∷ ▷   ( isBufferRecordML v1 ℓ1 (λ z vb, ⌜vb = map Some vcompress ++ vrest1⌝ ∗ ⌜length vcompress = z⌝ ∗ Pb1 z vb) cap1
                   -∗ isBufferRecordML v2 ℓ2 (λ z vb, ∃ vov vrest zold, ⌜vb = map Some (compress_buffer vcompress) ++ vrest⌝  
                                                      ∗ ⌜length (compress_buffer vcompress) = z⌝ ∗ ⌜length vov = z⌝
                                                      ∗ Pb2 zold (vov ++ vrest)) cap2
                   -∗ Φ #true).


End Specs.

Section LemmasThatShouldBeInStdPP.

  Lemma map_replicate {A B : Type} (f : A → B) (v:A) n : map f (replicate n v) = replicate n (f v).
  Proof.
    induction n as [|n IH]; cbn; firstorder congruence.
  Qed.

  Lemma map_insert {A B : Type} (vpre : A) (f : A → B) (k : nat) (v : B) lst :
    v = f vpre →
    k < length lst →
    <[ k := v ]> (map f lst) = map f (<[ k := vpre ]> lst).
  Proof.
    intros Hv.
    induction lst as [|lh lr IH] in k|-*.
    1: cbn; lia.
    destruct k as [|k].
    - intros _. cbn. by subst v.
    - cbn. intros H%Nat.succ_lt_mono. by rewrite IH.
  Qed.

End LemmasThatShouldBeInStdPP.

Section Proofs.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.

  Lemma buf_alloc_correct E1 E2 Ψ :
    prims_proto E1 Ψ ||- buf_lib_prog @ E2 :: wrap_proto buf_alloc_spec_ML.
  Proof using.
    iIntros (s ws Φ) "H". iNamed "H".
    iDestruct "Hproto" as "(%cap&%Hcap&->&->&HΦ')".
    cbn. unfold progwp. solve_lookup_fixed.
    destruct lvs as [|lv [|??]]; first done.
    all: cbn; iDestruct "Hsim" as "(->&H)"; try done.
    destruct ws as [|w [|??]]; try (eapply Forall2_length in Hrepr; cbn in Hrepr; done).
    eapply Forall2_cons_inv_l in Hrepr as (wcap&?&Hlval&_&?); simplify_eq.
    cbn. iExists _. iSplit; first done.
    iExists _. cbn. solve_lookup_fixed.
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
    iIntros (ℓbts) "(Hbts&Hstuff)".
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

    iPoseProof "Hγbk" as "((Hγbk&%Hγbk)&%fid&#Hfid)".

    assert (∃ k, Z.of_nat k = cap) as (ncap&<-) by (exists (Z.to_nat cap); lia).
    rewrite !Nat2Z.id.
    iAssert (isBufferRecord (Lloc γbf) ℓbts (buf_alloc_res_buffer ncap) ncap) with "[Hγbk Hγbf Hγbf2 Hγbfref Hbts]" as "Hbuffer".
    { iExists γbf, γbfref, γbf2, γbk, 0, fid. unfold named. iFrame.
      iSplit; first done.
      iExists (replicate ncap None). unfold named, lstore_own_foreign.
      rewrite map_replicate; cbn.
      iFrame. iFrame "Hfid". iSplit; first (iSplit; first done; by iExists fid).
      iPureIntro; split_and!.
      1: done.
      1: f_equal; lia.
      cbn. by rewrite replicate_length. }
    iMod (bufToML with "HGC Hbuffer") as "(HGC&%vv&Hbuffer&#Hsim)".
    iAssert (meta_token ℓbts ⊤) with "[Hstuff]" as "Hmeta".
    { destruct ncap as [|ncap]; first lia.
      cbn. rewrite loc_add_0. iDestruct "Hstuff" as "($&_)". }
    iModIntro. iApply ("Cont" with "HGC (HΦ' Hbuffer Hmeta) Hsim [//]").
  Qed.


  Lemma buf_upd_correct E Ψ :
    prims_proto E Ψ ||- buf_lib_prog @ E :: wrap_proto (buf_update_spec_ML Ψ E).
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    cbn. unfold progwp. solve_lookup_fixed.
    destruct lvs as [|lvi [|lvj [| lvF [| lvbuf [|??]]]]]; try done.
    all: cbn; iDestruct "Hsim" as "(->&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(->&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "((%γF&->&HγF)&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(Hsim&?)"; try done.
    destruct ws as [|wi [|wj [|wF [|wbuf [|??]]]]]; try (eapply Forall2_length in Hrepr; cbn in Hrepr; done).
    eapply Forall2_cons in Hrepr as (Hrepri&Hrepr).
    eapply Forall2_cons in Hrepr as (Hreprj&Hrepr).
    eapply Forall2_cons in Hrepr as (HreprF&Hrepr).
    eapply Forall2_cons in Hrepr as (Hreprbuf&_).
    cbn. iExists _. iSplit; first done.
    iExists _. cbn. solve_lookup_fixed.
    iSplit; first done. iNext.
    wp_apply (wp_CAMLlocal with "HGC"); [done..|].
    iIntros (ℓF) "(HGC&HℓF)"; wp_pures.
    wp_apply (store_to_root with "[$HGC $HℓF]"); [done..|].
    iIntros "(HGC&HℓF)". wp_pures.
    wp_apply (wp_CAMLlocal with "HGC"); [done..|].
    iIntros (ℓbf) "(HGC&Hℓbf)"; wp_pures.
    wp_apply (store_to_root with "[$HGC $Hℓbf]"); [done..|].
    iIntros "(HGC&Hℓbf)". wp_pure _.
    iMod (bufToC with "HGC Hrecord Hsim") as "(HGC&Hrecord&%&%&->)".
    iNamed "Hrecord". iNamed "Hbuf".

    wp_apply (load_from_root with "[$HGC $Hℓbf]"); [done..|].
    iIntros (wγ1) "(Hℓbf&HGC&%Hwγ1)".
    wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [done..|].
    iIntros (? wγaux1) "(HGC&_&%Heq&%Hγaux'1)"; cbv in Heq; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγaux]"); [done..|].
    iIntros (? wγfgn1) "(HGC&_&%Heq&%Hγfgn'1)"; cbv in Heq; simplify_eq.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgnpto]"); [done..|].
    iIntros "(HGC&Hγfgnpto)". wp_pure _.
    wp_apply (wp_val2int with "HGC"); [done..|].
    iIntros "HGC". wp_pure _.
    wp_apply (wp_Malloc); [done..|].
    change (Z.to_nat 1) with 1; cbn.
    iIntros (ℓi) "((Hℓi&_)&_)". rewrite !loc_add_0. wp_pure _.
    wp_apply (wp_val2int with "HGC"); [done..|].
    iIntros "HGC".
    wp_apply (wp_store with "Hℓi").
    iIntros "Hℓi". wp_pure _.

    iMod (bufToML_fixed (Lloc γ) ℓbuf (Pb i) (length vcontent)
         with "HGC [Hγusedref Hℓbuf HContent Hγfgnpto] Hsim") as "(HGC&HBufML)".
    { iExists _, _, _, _, _, _. unfold named. iSplit; first done.
      iFrame "Hγusedref Hγbuf Hγaux".
      iExists _. unfold named. by iFrame "Hγfgnpto Hγfgnsim Hℓbuf HContent". }
    iMod ("HMergeInitial" with "[$Hframe $HBufML]") as "HΨ".
    wp_bind (While _ _).

    repeat match goal with [H : repr_lval _ _ ?x |- _] => clear H; try clear x end.

    Ltac iPosePure H c := let t := type of H in iAssert (⌜t⌝)%I as c; [iPureIntro; exact H|clear H].
    iRevert (Hb1 Hb2); iIntros "#Hb1 #Hb2".
    revert Hb3.
    generalize (length vcontent) as vcontent_length. intros vcontent_length Hb3.
    clear vcontent.

    wp_apply (wp_wand _ _ _ (λ _, ∃ θ, ℓF ↦roots Lloc γF ∗ ℓbf ↦roots Lloc γ ∗ GC θ ∗ Ψ0 (j + 1)%Z ∗ ℓi ↦C{DfracOwn 1} #(j + 1))%I
              with "[HℓF Hℓbf Hℓi HGC HΨ]").
    { iRevert "HMerge HWP Hb1 Hb2". iLöb as "IH" forall (i θ).
      iIntros "#HMerge #HWP %Hb1 %Hb2".
      wp_pure _.
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pure _.
      rewrite bool_decide_decide. destruct decide; last first.
      { wp_pures. iModIntro.
        assert (i=j+1)%Z as -> by lia. iExists _. iFrame. }
      wp_pure _.

      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". wp_pure _. 1: apply ptr_offset_add.
      wp_apply (load_from_root with "[$HGC $HℓF]").
      iIntros (wγF) "(HℓF&HGC&%HwγF)".
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi".
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (wi) "(HGC&%Hwi)".
      wp_apply (wp_callback _ _ _ _ _ _ _ _ _ _ _ _ (ML_lang.LitV i) with "[$HGC $HγF HΨ]"); [done..| |].
      { cbn. iSplit; first done.
        iNext. by iApply ("HWP" with "[] [] HΨ"). } cbn.
      cbn.
      iIntros (θ' vret lvret wret) "(HGC&(%zret&->&HΦz&HΨframe&HBuffer)&->&%Hzrep)".
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". iRename "Hγfgnsim" into "Hγfgnsim2". clear used.
      iDestruct "HBuffer" as "(%ℓML0&%&%&%&%Heq&HℓbufML&Hbuf)". simplify_eq. unfold named.
      iNamed "Hbuf".
      assert (∃ (ni:nat), Z.of_nat ni = i) as (ni&<-) by (exists (Z.to_nat i); lia).
      wp_apply (wp_store_offset with "Hℓbuf").
      1: rewrite map_length; lia.
      iIntros "Hℓbuf". erewrite (map_insert (Some zret)); [|done|lia].

      wp_pure _.
      wp_apply (load_from_root with "[$HGC $Hℓbf]"); [done..|].
      iIntros (wbf1) "(Hℓbf&HGC&%Hwbf1)".
      wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [done..|].
      iIntros (vγref wγref) "(HGC&_&%Heq&%Hvwγref)". cbv in Heq. simplify_eq.

      iMod (ml_to_mut with "[$HGC $HℓbufML]") as "(HGC&%&%&HℓbufML&#Hsim2&HHsim2)".
      destruct lvs as [|? [|??]].
      1: cbn; done.
      all: iDestruct "HHsim2" as "(->&HHr)"; try done. iClear "HHr".

      iAssert (⌜fid1 = fid0⌝ ∗ ⌜γfgn0 = γfgn⌝ ∗ ⌜γ0 = γref⌝)%I as "(->&->&->)".
      { iDestruct "Hsim" as "#(%γ2&%&%&%HHH&Hγbuf2&(%γref2&->&Hsim3)&%γaux2&%&%&->&Hγaux2&->&%γfgn3&->&Hγfgnsim3)".
        simplify_eq.
        unfold lstore_own_vblock, lstore_own_elem; cbn.
        iDestruct "Hγbuf" as "(Hγbuf&_)".
        iDestruct "Hγbuf2" as "(Hγbuf2&_)".
        iDestruct "Hγaux" as "(Hγaux&_)".
        iDestruct "Hγaux2" as "(Hγaux2&_)".
        iPoseProof (ghost_map.ghost_map_elem_agree with "Hγbuf Hγbuf2") as "%Heq1"; simplify_eq.
        iPoseProof (ghost_map.ghost_map_elem_agree with "Hγaux Hγaux2") as "%Heq1"; simplify_eq.
        iPoseProof (lloc_own_foreign_inj with "Hγfgnsim2 Hγfgnsim3 HGC") as "(HGC&%Heq1)"; simplify_eq.
        iPoseProof (lloc_own_foreign_inj with "Hγfgnsim Hγfgnsim3 HGC") as "(HGC&%Heq1b)"; simplify_eq.
        iPoseProof (lloc_own_pub_inj with "Hsim3 Hsim2 HGC") as "(HGC&%Heq2)"; simplify_eq.
        iPureIntro. split_and!. 1: symmetry; by eapply Heq1.
        1: by eapply Heq1b. 1: symmetry; by eapply Heq2. }

      wp_apply (wp_readfield with "[$HGC $HℓbufML]"); [done..|].
      iIntros (vγbuf wγbuf) "(HGC&HℓbufML&%Heq&%Hvwγbuf)". change (Z.to_nat 0) with 0 in Heq. cbn in Heq. simplify_eq.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC".
      wp_apply (wp_load with "Hℓi").
      iIntros "Hℓi". do 2 wp_pure _.
      wp_bind (If _ _ _).
      iApply (wp_wand _ _ _ (λ _, _ ∗ γref ↦mut (TagDefault, [Lint (max used (Z.to_nat (ni+1)))%Z]))%I with "[HGC Hℓi Hℓbf HℓbufML]").
      { rewrite bool_decide_decide. destruct decide; last first.
        { do 2 wp_pure _. rewrite max_l; last lia.
          iFrame "HℓbufML". iModIntro. iAccu. }
        { wp_pure _.
          wp_apply (load_from_root with "[$HGC $Hℓbf]"); [done..|].
          iIntros (wbf2) "(Hℓbf&HGC&%Hwbf2)".
          wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [done..|].
          iIntros (vγref2 wγref2) "(HGC&_&%Heq&%Hvwγref2)". cbv in Heq. simplify_eq.
          wp_apply (wp_load with "Hℓi").
          iIntros "Hℓi". wp_pure _.
          wp_apply (wp_int2val with "HGC"); [done..|].
          iIntros (vnp1) "(HGC&%Hnp1)".
          wp_apply (wp_modify with "[$HGC $HℓbufML]"); [done..|].
          iIntros "(HGC&HℓbufML)". iFrame "HGC Hℓbf Hℓi".
          rewrite max_r; last lia. change (Z.to_nat 0) with 0; cbn.
          rewrite Z2Nat.id; last lia. done. }
      }
      iIntros (vv) "((HGC&Hℓi&Hℓbf)&HℓbufML)". wp_pure _.
      wp_apply (wp_load with "Hℓi"). iIntros "Hℓi". wp_pure _.
      wp_apply (wp_store with "Hℓi"). iIntros "Hℓi". wp_pure _.
      iMod (mut_to_ml _ [ ML_lang.LitV (_:Z)] with "[$HGC $HℓbufML]") as "(HGC&%ℓML2&HℓbufML&Hsimℓ2)". 1: cbn; iFrame; done.
      iPoseProof (lloc_own_pub_inj with "Hsim2 Hsimℓ2 HGC") as "(HGC&%Heq3)"; simplify_eq.
      replace ℓML2 with ℓML0 by by eapply Heq3.
      iMod ("HMerge" with "[] [] HΨframe HΦz [Hγfgnpto HContent Hℓbuf HℓbufML]") as "HH". 1-2: iPureIntro; lia.
      { iExists _, _, _, _. unfold named. iSplit; first done. iFrame "HℓbufML".
        iExists _. unfold named. iFrame "Hγfgnpto Hγfgnsim Hℓbuf".
        rewrite insert_length. iSplit; last done.
        iExists vcontent, _. iFrame "HContent". iPureIntro. rewrite Nat2Z.id. split; first done.
        reflexivity. }
      iApply ("IH" with "HℓF Hℓbf Hℓi HGC HH").
      - iIntros "!> %z1 %z2 %HH1 %HH2". iApply "HMerge".
        all: iPureIntro; lia.
      - iIntros "!> %z1 %HH1 %HH2". iApply "HWP".
        all: iPureIntro; lia.
      - iPureIntro; lia.
      - iPureIntro; lia.
    }
    iIntros (vvv) "(%θ' & HℓF & Hℓbf & HGC & HΨ & Hℓi)".
    wp_pure _.
    wp_apply (wp_free with "Hℓi"). iIntros "_".
    wp_pure _.
    wp_apply (wp_int2val with "HGC"); [done..|].
    iIntros (v0) "(HGC&%Hrepr)".
    wp_pure _.
    wp_apply (wp_CAMLunregister1 with "[$HGC $HℓF]"); [done..|].
    iIntros "HGC"; wp_pure _.
    wp_apply (wp_CAMLunregister1 with "[$HGC $Hℓbf]"); [done..|].
    iIntros "HGC"; wp_pure _.
    iModIntro. iApply ("Cont" with "HGC (HCont HΨ) [//] [//]").
  Qed.


  Lemma wrap_max_len_correct E Ψ :
    prims_proto E Ψ ||- buf_lib_prog @ E :: wrap_proto (wrap_max_len_ML).
  Proof.
    iIntros (s ws Φ) "H". iNamed "H".
    iNamed "Hproto".
    cbn. unfold progwp. solve_lookup_fixed.
    destruct lvs as [|lv [|??]]; first done.
    all: cbn; iDestruct "Hsim" as "(->&H)"; try done.
    destruct ws as [|w [|??]]; try (eapply Forall2_length in Hrepr; cbn in Hrepr; done).
    eapply Forall2_cons_inv_l in Hrepr as (wcap&?&Hlval&_&?); simplify_eq.
    cbn. iExists _. iSplit; first done.
    iExists _. cbn. solve_lookup_fixed.
    iSplit; first done. iNext.

    wp_apply (wp_val2int with "HGC"); [done..|].
    iIntros "HGC".
    wp_bind (FunCall (&buffy_max_len_name) _).
    iApply wp_proto_mono. 2: iApply wp_wand.
    2: iApply buffy_max_len_spec.
    1: iIntros (???) "[]".
    1: by do 4 (apply insert_subseteq_r; [done|]).
    1: done.
    iIntros (v) "->".
    wp_apply (wp_int2val with "HGC"); [done..|].
    iIntros (w) "(HGC&%Hrepr)".
    iApply ("Cont" with "HGC HCont [//] [//]").
  Qed.

  Lemma wrap_compress_correct E Ψ :
    prims_proto E Ψ ||- buf_lib_prog @ E :: wrap_proto (wrap_compress_ML).
  Proof.
    iIntros (s ws Φ) "H". iNamed "H".
    iNamed "Hproto".
    cbn. unfold progwp. solve_lookup_fixed.
    destruct lvs as [|lv1 [|lv2 [|??]]]; first done.
    all: cbn; iDestruct "Hsim" as "(Hsim1&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(Hsim2&Hsim)"; try done.
    destruct ws as [|w1 [|w2 [|??]]]; try (eapply Forall2_length in Hrepr; cbn in Hrepr; done).
    eapply Forall2_cons in Hrepr as (Hrepr1&Hrepr).
    eapply Forall2_cons in Hrepr as (Hrepr2&Hrepr).
    cbn. iExists _. iSplit; first done.
    iExists _. cbn. solve_lookup_fixed.
    iSplit; first done. iNext.

    iMod (bufToC with "HGC HBuf1 Hsim1") as "(HGC&HBuf1&%&%&->)".
    iNamed "HBuf1". iNamed "Hbuf".
    iMod (bufToC with "HGC HBuf2 Hsim2") as "(HGC&HBuf2&%&%&->)".
    iDestruct "HBuf2" as "(%γ2&%γref2&%γaux2&%γfgn2&%used2&%fid2&->&#Hγbuf2&Hγusedref2&#Hγaux2&Hbuf2)".
    unfold named.
    iDestruct "Hbuf2" as "(%vcontent2&Hγfgnpto2&#Hγfgnsim2&Hℓbuf2&HContent2&->)". unfold named.

    wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [done..|].
    iIntros (vγaux1 wγaux1) "(HGC&_&%Heq1&%Hreprγaux1)". cbv in Heq1; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγaux]"); [done..|].
    iIntros (vγfgn1 wγfgn1) "(HGC&_&%Heq1&%Hreprγfgn1)". cbv in Heq1; simplify_eq.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgnpto]"); [done..|].
    iIntros "(HGC&Hγfgnpto)". wp_pure _.

    wp_apply (wp_readfield with "[$HGC $Hγbuf2]"); [done..|].
    iIntros (vγaux2 wγaux2) "(HGC&_&%Heq1&%Hreprγaux2)". cbv in Heq1; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγaux2]"); [done..|].
    iIntros (vγfgn2 wγfgn2) "(HGC&_&%Heq1&%Hreprγfgn2)". cbv in Heq1; simplify_eq.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgnpto2]"); [done..|].
    iIntros "(HGC&Hγfgnpto2)". wp_pure _.

    wp_apply (wp_readfield with "[$HGC $Hγbuf]"); [done..|].
    iIntros (vγref1 wγref1) "(HGC&_&%Heq1&%Hreprγref1)". cbv in Heq1; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγusedref]"); [done..|].
    iIntros (vv wused) "(HGC&Hγusedref&%Heq1&%Hreprwused)". change (Z.to_nat 0) with 0 in Heq1; cbn in Heq1; simplify_eq.
    wp_apply (wp_val2int with "HGC"); [done..|].
    iIntros "HGC". wp_pure _.
    wp_apply wp_Malloc; [done..|]. change (Z.to_nat 1) with 1. cbn.
    iIntros (ℓcap2) "((Hℓcap2&_)&_)". rewrite loc_add_0.
    wp_pure _.

    wp_apply (wp_readfield with "[$HGC $Hγbuf2]"); [done..|].
    iIntros (vγaux2' wγaux2') "(HGC&_&%Heq1&%Hreprγaux2')". cbv in Heq1; simplify_eq.
    wp_apply (wp_readfield with "[$HGC $Hγaux2]"); [done..|].
    iIntros (vv wcap) "(HGC&_&%Heq1&%Hreprcap2)". change (Z.to_nat 0) with 0 in Heq1; cbn in Heq1; simplify_eq.
    wp_apply (wp_val2int with "HGC"); [done..|].
    iIntros "HGC".
    wp_apply (wp_store with "Hℓcap2"). iIntros "Hℓcap2".
    wp_pure _.
    iDestruct "HContent" as "(->&<-&HContent)".
    rewrite map_app.
    iPoseProof (array_app with "Hℓbuf") as "(Hℓbuf&Hℓbufuninit)".
    wp_bind (FunCall _ _).
    iApply wp_proto_mono.
    2: iApply (wp_wand with "[Hℓbuf Hℓbuf2 Hℓcap2]").
    2: iApply (buffy_compress_spec with "Hℓbuf Hℓbuf2 [Hℓcap2]").
    - iIntros (???) "[]".
    - by do 4 (apply insert_subseteq_r; [done|]).
    - by rewrite map_map.
    - rewrite map_length; lia.
    - rewrite map_length. iApply "Hℓcap2".
    - iIntros (v) "(%bout&%vout&%vrest&%vov&%Hbufout&->&->&%Hvov&%Hlen&Hℓbuf2&Hℓbuf&Hℓcap2)".

      apply map_eq_app in Hvov as (zvov&zvrest&->&<-&<-).
      unfold isBuffer in Hbufout. subst vout.
      rewrite !map_length in Hlen. rewrite !map_length.

      wp_pure _.
      wp_apply (wp_readfield with "[$HGC $Hγbuf2]"); [done..|].
      iIntros (vγref2 wγref2) "(HGC&_&%Heq1&%Hreprγref2)". cbv in Heq1; simplify_eq.
      wp_apply (wp_load with "Hℓcap2"). iIntros "Hℓcap2".
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (w0) "(HGC&%Hrepr0)".
      wp_apply (wp_modify with "[$HGC $Hγusedref2]"); [done..|].
      iIntros "(HGC&Hγusedref2)". wp_pure _.
      wp_apply (wp_free with "Hℓcap2"). iIntros "_".
      do 2 wp_pure _.
      rewrite bool_decide_decide; destruct decide; try done.
      wp_pure _. iApply (wp_post_mono with "[HGC]").
      1: wp_apply (wp_int2val with "HGC"); [done..|iIntros (w) "H"; iAccu].
      iIntros (ww1) "(HGC&%Hreprw1)".
      iMod (bufToML_fixed with "HGC [Hγusedref Hγfgnpto Hℓbuf Hℓbufuninit HContent] Hsim1") as "(HGC&HBuf1)"; last first.
      1: iMod (bufToML_fixed with "HGC [Hγusedref2 Hγfgnpto2 Hℓbuf2 HContent2] Hsim2") as "(HGC&HBuf2)"; last first.
      1: iApply ("Cont" $! _ (ML_lang.LitV true) with "HGC (HCont HBuf1 HBuf2) [//] [//]").
      { iExists _, _, _, _, _, _. unfold named.
        iSplit; first done.
        change (Z.to_nat 0) with 0; cbn.
        iFrame "Hγbuf2 Hγaux2 Hγusedref2".
        iExists _. unfold named.
        iFrame "Hγfgnpto2 Hγfgnsim2".
        iSplitL "Hℓbuf2"; last first.
        - iSplit.
          1: iExists _, zvrest, _.
          1: repeat (iSplit; first done); iApply "HContent2".
          iPureIntro. rewrite !app_length !map_length Hlen //.
        - rewrite !map_app !map_map. cbn. done.
      }
      { iExists _, _, _, _, _, _. unfold named.
        iSplit; first done.
        iFrame "Hγbuf Hγaux Hγusedref".
        iExists _. unfold named.
        iFrame "Hγfgnpto Hγfgnsim". iSplitR "HContent".
        2: { iSplit; [iSplit; [|iSplit]|]. 3: iApply "HContent".
             all: done. }
        rewrite map_app. iApply array_app. rewrite !map_length. iFrame. }
  Qed.

End Proofs.
