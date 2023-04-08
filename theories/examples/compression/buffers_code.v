From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources basics_constructions.
From melocoton.interop Require Import lang weakestpre prims_proto.
From melocoton.language Require Import weakestpre progenv.
From melocoton.c_interop Require Import notation.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.c_lang Require Import notation proofmode derived_laws.
From melocoton.examples.compression Require Import compression_defs compression_specs.


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

Definition buf_free_code (bf : expr) : expr :=
  let: "bts" := Custom_contents(Field(Field( bf, #1), #1)) in
  let: "cap" := Int_val ( Field(Field( bf, #1), #0) ) in
  (if: "bts" ≠ #LitNull
      then free("bts", "cap") else Skip );;
  (Custom_contents(Field(Field( bf, #1), #1)) := #LitNull) ;;
  Store_field (&Field(Field( bf, #0), #0), Val_int (#-1) ) ;;
  Val_int (#0).
Definition buf_free_fun := Fun [BNamed "bf"] (buf_free_code "bf").
Definition buf_free_name := "buf_free".

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
  <[buf_free_name      := buf_free_fun]> (
  <[buf_upd_name       := buf_upd_fun]> (
  <[buf_alloc_name     := buf_alloc_fun]>
    ∅ )))).

End C_code.