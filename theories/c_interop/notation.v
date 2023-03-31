From melocoton.c_interface Require Export notation.
From melocoton.c_lang Require Export lang notation.
From iris.prelude Require Import options.

Definition CAMLlocal (n:string) (e : expr) : expr :=
  (let: n := malloc (#1) in
    (Var n <- (call: &"int2val" with (Val (#0))));;
    (call: &"registerroot" with (Var n));; e).

Notation "'CAMLlocal:' x 'in' e2" := (CAMLlocal x%string e2%CE)
  (at level 200, x at level 1, e2 at level 200,
   format "'[' 'CAMLlocal:'  x   'in'  '/' e2 ']'") : c_expr_scope.

Notation "'Field' '(' x ',' y ')'" := (call: &"readfield" with (x%CE, y%CE))%CE
  (at level 100, x, y at level 99,
  format "'Field' '(' x ','  '/' y ')'") : c_expr_scope.
Notation "'Store_field' '(' '&' 'Field' '(' x ',' y ')' ',' z ')'" := (call: &"modify" with (x%CE, y%CE, z%CE))%CE
  (at level 100, x, y, z at level 99,
  format "'Store_field' '(' '&' 'Field' '(' x ','  y ')' ','  '/' z ')'") : c_expr_scope.

Notation "'Int_val' '(' x ')'" := (call: &"val2int" with (x%CE))%CE
  (at level 100, x at level 99,
  format "'Int_val' '(' x ')'") : c_expr_scope.
Notation "'Val_int' '(' x ')'" := (call: &"val2int" with (x%CE))%CE
  (at level 100, x at level 99,
  format "'Val_int' '(' x ')'") : c_expr_scope.

Notation "'Custom_contents' '(' x ')'" := (call: &"readforeign" with (x%CE))%CE
  (at level 100, x at level 99,
  format "'Custom_contents' '(' x ')'") : c_expr_scope.
Notation "'Custom_contents' '(' x ')' ':=' y" := (call: &"writeforeign" with (x%CE, y%CE))%CE
  (at level 100, x, y at level 99,
  format "'Custom_contents' '(' x ')'  ':='  '/' y") : c_expr_scope.

Notation "'caml_alloc' '(' len ',' tag ')'" := (call: &"alloc" with (len%CE, tag%CE))%CE
  (at level 100, len, tag at level 99,
  format "'caml_alloc' '(' len ','  tag ')'") : c_expr_scope.
Notation "'caml_alloc_custom' '(' ')'" := (call: &"allocforeign" with ( ))%CE
  (at level 100, 
  format "'caml_alloc_custom' '(' ')'") : c_expr_scope.
(* XXX maybe make this list-based? *)
Notation do_unreg1 ek := (call: &"unregisterroot" with ( * (ek) ) ;; free (ek%CE, #1))%CE.
Notation "'CAMLreturn:' x 'unregistering' '[' e1 , .. , en ']'" := (let: "!Hret" := x%CE in (Seq (do_unreg1 e1%CE) .. (Seq (do_unreg1 en%CE) "!Hret"%CE) ..))%CE.

