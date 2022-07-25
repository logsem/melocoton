From Coq Require Import ZArith.
From stdpp Require Import base functions.
From melocoton.interop Require Import assums.

(* global parameters of the wrapping semantics. *)

Class WrapperParameters :=
  { encodeInt : Z → word;
    encodeAddr : addr → word;
    encodeInt_injective := Inj (=) (=) encodeInt;
    encodeAddr_injective := Inj (=) (=) encodeAddr;
  }.
