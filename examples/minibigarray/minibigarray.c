#include <stdio.h>
#include <snappy-c.h>
#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/callback.h>
#include <caml/custom.h>

   //   some boilerplate related to OCaml custom blocks
static struct custom_operations ops = {
  "mini_ba",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default,
  custom_compare_ext_default,
  custom_fixed_length_default
};

size_t max(size_t a, size_t b) {
  return a>b?a:b;
}

#define caml_alloc_custom(k) (caml_alloc_custom(&ops, k, 0, 1))
#define Custom_contents(k) (*(unsigned char**) (Data_custom_val(k)))



value wrap_max_len(value i) {
  CAMLparam1(i);
  CAMLreturn(Val_int(snappy_max_compressed_length(Int_val(i))));
}
value buf_alloc(value cap) {
  CAMLparam1(cap); CAMLlocal2(bk, bf);   // \label{line:bufalloc:gc_one}   // 
  bk = caml_alloc_custom(sizeof(void*));    // \label{line:bufalloc:custom}   // 
  Custom_contents(bk) = malloc(Int_val(cap));   // \label{line:bufalloc:bytes}   // 
  bf = caml_alloc(3, 0);   // \label{line:bufalloc:buffer_start}   // 
  Store_field(bf, 0, bk);
  Store_field(bf, 1, Val_int(0));
  Store_field(bf, 2, cap);   // \label{line:bufalloc:buffer_end}   //
  CAMLreturn(bf);   // \label{line:bufalloc:gc_two}   // 
}
value buf_upd(value iv, value jv, value f, value bf) {
  CAMLparam4(iv, jv, f, bf);
  unsigned char* bts = Custom_contents(Field(bf, 0)); size_t j = Int_val(jv);
  for (size_t i = Int_val(iv); i <= j; i++) {
    bts[i] = Int_val(caml_callback(f, Val_int(i)));
    if (i+1 > Int_val(Field(bf, 1))) Store_field(bf, 1, Val_int(i+1));
  }
  CAMLreturn(Val_unit);
}
value wrap_compress(value bf1, value bf2) {
  CAMLparam2(bf1, bf2);
  unsigned char* bts1 = Custom_contents(Field(bf1, 0));
  unsigned char* bts2 = Custom_contents(Field(bf2, 0));
  size_t used1 = Int_val(Field(bf1, 1)); size_t cap2 = Int_val(Field(bf2, 2));
  int res = snappy_compress(bts1, used1, bts2, &cap2);
  Store_field(bf2, 1, Val_int(cap2));
  CAMLreturn((res == SNAPPY_OK) ? Val_int(1) : Val_int(0));
}



value buf_free(value bf) {
  value bk = Field(bf, 0);
  unsigned char* bts = Custom_contents(bk);
  if (bts != NULL) free(bts);
  Custom_contents(bk) = NULL;
  return Val_unit;
}

value buf_get(value bf, value i) {
  value bk = Field(bf, 0);
  unsigned char* bg = Custom_contents(bk);
  return Val_int(bg[Int_val(i)]);
}
