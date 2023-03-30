From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.interop Require Import lang weakestpre update_laws wp_utils wp_ext_call_laws wp_simulation.
From melocoton.c_interop Require Import rules.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import mlang_instantiation lang_instantiation.
From melocoton.ml_lang Require proofmode.
From melocoton.c_lang Require notation proofmode.
From melocoton.mlanguage Require Import progenv.
From melocoton.mlanguage Require weakestpre.
From melocoton.linking Require Import lang weakestpre.


Section C_prog.
Import melocoton.c_lang.notation melocoton.c_lang.proofmode.

Context `{SI:indexT}.
Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.

Definition CAMLlocal (n:string) (e : expr) : expr :=
  (let: n := malloc (#1) in
    (Var n <- (call: &"int2val" with (Val (#0))));;
    (call: &"registerroot" with (Var n));; e).

Notation "'CAMLlocal:' x 'in' e2" := (CAMLlocal x%string e2%CE)
  (at level 200, x at level 1, e2 at level 200,
   format "'[' 'CAMLlocal:'  x   'in'  '/' e2 ']'") : c_expr_scope.

Definition buf_alloc_code (cap : expr) : expr :=
  CAMLlocal: "bk" in
  "bk" <- call: &"allocforeign" with ( ) ;;
  call: &"writeforeign" with ( *"bk", malloc (call: &"val2int" with (cap))) ;;
  CAMLlocal: "bf" in
  "bf" <- call: &"alloc" with (Val #2, Val #0) ;;
  CAMLlocal: "bf2" in
  "bf2" <- call: &"alloc" with (Val #2, Val #0) ;;
  CAMLlocal: "bfref" in
  "bfref" <- call: &"alloc" with (Val #1, Val #0) ;;
  call: &"modify" with ( *"bf", Val #0, *"bfref") ;;
  call: &"modify" with ( *"bf", Val #1, *"bf2") ;;
  call: &"modify" with ( *"bf2", Val #0, cap ) ;;
  call: &"modify" with ( *"bf2", Val #1, *"bk") ;;
  call: &"modify" with ( *"bfref", Val #0, call: &"int2val" with (Val #0) ) ;;
  call: &"unregisterroot" with ( *"bk" ) ;;
  call: &"unregisterroot" with ( *"bf" ) ;;
  call: &"unregisterroot" with ( *"bf2" ) ;;
  call: &"unregisterroot" with ( *"bfref" ) ;;
  let: "retval" := *"bf" in
  free ("bk", #1) ;; free ("bf", #1) ;; free ("bf2", #1) ;; free ("bfref", #1) ;;
  "retval".

Definition buf_upd_code (iv jv f_arg bf_arg : expr) : expr :=
  CAMLlocal: "f" in
  "f" <- f_arg ;;
  CAMLlocal: "bf" in
  "bf" <- bf_arg ;;
  let: "bts" := call: &"readforeign" with (
      call: &"readfield" with ( call: &"readfield" with ( *"bf", Val #1), Val #1)) in
  let: "j" := call: &"val2int" with ( jv ) in
  let: "i" := malloc ( #1 ) in
  "i" <- call: &"val2int" with ( iv ) ;;
  while: * "i" ≤ "j" do
    ( "bts" +ₗ ( *"i") <- call: &"val2int" with (call: &"callback" with ( *"f", call: &"int2val" with ( *"i"))) ;;
      if: (call: &"val2int" with (call: &"readfield" with (call: &"readfield" with ( *"bf", Val #0), Val #0)) < *"i" + #1)
      then (call: &"modify" with (call: &"readfield" with ( *"bf", Val #0), Val #0, call: &"int2val" with ( *"i" + #1)))
      else Skip ;;
      "i" <- *"i" + #1 ) ;;
  call: &"unregisterroot" with ( *"f" ) ;;
  call: &"unregisterroot" with ( *"bf" ) ;;
  free ("f", #1);; free ("bf", #1);; free ("i", #1) ;;
  call: &"int2val" with (Val #0).
  

End C_prog.

