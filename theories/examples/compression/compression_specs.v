From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.c_interface Require Import defs notation pretty resources.
From melocoton.c_lang Require Import lang notation.
From melocoton.examples.compression Require Import compression_defs.
From melocoton Require Import language_commons.

Definition buffy_compress_rec_name : string := "buffy_compress_rec".
Definition buffy_max_len_name : string := "buffy_max_compressed_length".
Definition buffy_compress_name : string := "buffy_compress".

Definition buffy_max_len_code (inlen:expr) : expr := (BinOp MultOp inlen (#2))%CE.
Definition buffy_compress_rec_code (inbuf inlen outbuf:expr) := (
  if: inlen ≤ #0 then #0 else
  if: inlen = #1
    then ( outbuf <- #1 ;; outbuf +ₗ #1 <- *inbuf ;; #2 )
    else if: ( *inbuf = #0) && ( *(inbuf +ₗ #1) = #0 )
      then ( outbuf <- #0 ;; #1 + call: &buffy_compress_rec_name with (inbuf +ₗ #2, inlen - #2, outbuf +ₗ #1) )
      else ( outbuf <- #1 ;; outbuf +ₗ #1 <- *inbuf ;; #2 + call: &buffy_compress_rec_name with (inbuf +ₗ #1, inlen - #1, outbuf +ₗ #2) ) )%CE.
Definition buffy_compress_code (inbuf inlen outbuf outlenp:expr) := (
  if: *outlenp < call: &buffy_max_len_name with (inlen) then #1 else
    (outlenp <- call: &buffy_compress_rec_name with (inbuf, inlen, outbuf)) ;; #0 )%CE.

Definition buffy_env : gmap string function :=
  <[buffy_max_len_name      := Fun [BNamed "len"] (buffy_max_len_code "len")]> (
  <[buffy_compress_rec_name := Fun [BNamed "inbuf"; BNamed "inlen"; BNamed "outbuf"] (buffy_compress_rec_code "inbuf" "inlen" "outbuf")]> (
  <[buffy_compress_name     := Fun [BNamed "inbuf"; BNamed "inlen"; BNamed "outbuf"; BNamed "outlenp"]
                                   (buffy_compress_code "inbuf" "inlen" "outbuf" "outlenp")]>
  ∅)).

Section CBuffers.

Context `{SI:indexT}.
Context `{!heapG_C Σ, !invG Σ}.

(* XXX seal this *)
Definition isBuffer (vl : list (option val)) (b : buffer) := vl = map (λ x:Z, Some (#x)) b.


Definition buffy_max_len_spec : protocol val Σ := (λ s vv Φ,
  ∃ (n:nat),
    "->" ∷ ⌜s = buffy_max_len_name⌝
  ∗ "->" ∷ ⌜vv = [ #n ]⌝
  ∗ "Hcont" ∷ ▷ Φ (OVal #(buffer_max_len n)))%I.
Definition buffy_compress_spec_ok : protocol val Σ := (λ s vv Φ,
  ∃ (ℓin ℓout ℓlen : loc) vin bin vspace,
    "->" ∷ ⌜s = buffy_compress_name⌝
  ∗ "->" ∷ ⌜vv = [ #ℓin; #(length bin); #ℓout; #ℓlen ]⌝
  ∗ "%Hlength" ∷ ⌜length vspace ≥ buffer_max_len (length bin)⌝
  ∗ "%HBuffer" ∷ ⌜isBuffer vin bin⌝
  ∗ "Hℓin" ∷ ℓin  I↦C∗ vin
  ∗ "Hℓout" ∷ ℓout I↦C∗ vspace
  ∗ "Hℓlen" ∷ ℓlen ↦C  #(length vspace)
  ∗ "HCont" ∷ ▷ (∀ bout vout vrest voverwritten,
         ⌜isBuffer vout bout⌝
      -∗ ⌜bout = compress_buffer bin⌝
      -∗ ⌜vspace = voverwritten ++ vrest⌝
      -∗ ⌜length voverwritten = length vout⌝
      -∗ ℓout I↦C∗ (vout ++ vrest)
      -∗ ℓin  I↦C∗ vin
      -∗ ℓlen ↦C  #(length vout)
      -∗ Φ (OVal #0)))%I.

Definition buffy_compress_spec_fail : protocol val Σ := (λ s vv Φ,
  ∃ (ℓlen:loc) (z:Z) (nlen:nat) vv1 vv2,
    "->" ∷ ⌜s = buffy_compress_name⌝
  ∗ "->" ∷ ⌜vv = [ vv1; #nlen; #vv2; #ℓlen ]⌝
  ∗ "%Hlen" ∷ ⌜z < buffer_max_len (nlen)⌝%Z
  ∗ "Hℓlen" ∷ ℓlen ↦C #z
  ∗ "HCont" ∷ ▷ (ℓlen ↦C #z
      -∗ Φ (OVal #1)))%I.

Definition buffy_library_spec : protocol val Σ :=
  buffy_max_len_spec ⊔ buffy_compress_spec_ok ⊔ buffy_compress_spec_fail.

End CBuffers.
