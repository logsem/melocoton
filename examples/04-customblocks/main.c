#include <stdio.h>
#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>

// NB: when custom, the functions provided below must never trigger a GC,
// must not call back to ocaml code, and must not use CAMLparam/CAMLreturn
static struct custom_operations caml_cpair_custom_ops = {
  identifier: "caml_cpair",
  finalize: custom_finalize_default,
  compare: custom_compare_default, // always raises Failure
  compare_ext: custom_compare_ext_default, // always raises Failure
  hash: custom_hash_default, // ignores the content of the block
  serialize: custom_serialize_default, // always raises Failure
  deserialize: custom_deserialize_default, // always raises Failure
  fixed_length: custom_fixed_length_default
};

struct c_pair {
  int x;
  int y;
};

value caml_mkpair(value unit) {
  CAMLparam0();
  CAMLlocal1(p);
  p = caml_alloc_custom(&caml_cpair_custom_ops, sizeof(struct c_pair),
                        // parameters for controlling GC speed when the custom
                        // block uses out-of-heap memory
                        // (not the case here)
                        0, 1);

  struct c_pair* cp = Data_custom_val(p);
  cp->x = 0;
  cp->y = 0;
  CAMLreturn(p);
}

value caml_set_x(value p, value n) {
  CAMLparam2(p, n);
  struct c_pair* cp = Data_custom_val(p);
  cp->x = Int_val(n);
  CAMLreturn(Val_unit);
}

value caml_set_y(value p, value n) {
  CAMLparam2(p, n);
  struct c_pair* cp = Data_custom_val(p);
  cp->y = Int_val(n);
  CAMLreturn(Val_unit);
}

value caml_get_x(value p) {
  CAMLparam1(p);
  struct c_pair* cp = Data_custom_val(p);
  CAMLreturn(Val_int(cp->x));
}

value caml_get_y(value p) {
  CAMLparam1(p);
  struct c_pair* cp = Data_custom_val(p);
  CAMLreturn(Val_int(cp->y));
}
