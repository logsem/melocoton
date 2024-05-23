From melocoton.c_interface Require Export notation.
From melocoton.c_lang Require Export lang notation.
From iris.prelude Require Import options.



Notation "'Field' '(' x ',' y ')'" := (call: &"readfield" with (x%CE, y%CE))%CE
  (at level 70, x, y at level 69,
  format "'Field' '(' x ','  '/' y ')'") : c_expr_scope.
Notation "'Store_field' '(' x ',' y ',' z ')'" := (call: &"modify" with (x%CE, y%CE, z%CE))%CE
  (at level 70, x, y, z at level 69,
  format "'Store_field' '(' x ','  y ','  z ')'") : c_expr_scope.

Notation "'Int_val' '(' x ')'" := (call: &"val2int" with (x%CE))%CE
  (at level 70, x at level 69,
  format "'Int_val' '(' x ')'") : c_expr_scope.
Notation "'Val_int' '(' x ')'" := (call: &"int2val" with (x%CE))%CE
  (at level 70, x at level 69,
  format "'Val_int' '(' x ')'") : c_expr_scope.

Definition Val_unit := Val_int (#C 0)%CE.

Notation "'BoxedInt_val' '(' x ')'" := (call: &"read_foreign" with (x%CE))%CE
  (at level 70, x at level 69,
  format "'BoxedInt_val' '(' x ')'") : c_expr_scope.

Notation "'Custom_contents' '(' x ')'" := (call: &"read_foreign" with (x%CE))%CE
  (at level 70, x at level 69,
  format "'Custom_contents' '(' x ')'") : c_expr_scope.
Notation "'Custom_contents' '(' x ')' ':=' y" := (call: &"write_foreign" with (x%CE, y%CE))%CE
  (at level 70, x at level 69, y at level 68,
  format "'Custom_contents' '(' x ')'  ':='  '/' y") : c_expr_scope.
(* XXX whoops the order is wrong *)
Notation "'caml_alloc' '(' len ',' tag ')'" := (call: &"alloc" with (tag%CE, len%CE))%CE
  (at level 70, len, tag at level 69,
  format "'caml_alloc' '(' len ','  tag ')'") : c_expr_scope.
Notation "'caml_alloc_custom' '(' ')'" := (call: &"alloc_foreign" with ( ))%CE
  (at level 70,
  format "'caml_alloc_custom' '(' ')'") : c_expr_scope.

(* XXX maybe make this list-based? *)
Definition CAMLunregister1 ek :=
  (call: &"unregisterroot" with (ek))%CE.

Notation "'CAMLreturn:' x 'unregistering' '[' e1 , .. , en ']'" :=
  (let: "!Hret" := x%CE in
  (Seq (CAMLunregister1 e1%CE) .. (Seq (CAMLunregister1 en%CE) "!Hret"%CE) ..))%CE.

Definition CAMLlocal (n:string) (e : expr) : expr :=
  (let: n := Val_unit in
  (call: &"registerroot" with (&: n));; e).

Notation "'CAMLlocal:' x 'in' e2" := (CAMLlocal x%string e2%CE)
  (at level 200, x at level 1, e2 at level 200,
   format "'[' 'CAMLlocal:'  x  'in'  '/' e2 ']'") : c_expr_scope.
