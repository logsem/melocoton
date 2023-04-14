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
  CAMLparam1(cap); CAMLlocal3(bk, bf, r);    // \label{line:bufalloc:gc_one}  //
  r  = caml_alloc(1, 0);                 // allocate the `used` reference block   // \label{line:bufalloc:ref_alloc}  //
  Store_field(r, 0, Val_int(0));                 // \label{line:bufalloc:ref_init} \label{line:bufalloc:val_int}  //
  bk = caml_alloc_custom(sizeof(void*)); // allocate the `data` custom block    // \label{line:bufalloc:custom}  //
  Custom_contents(bk) = malloc(Int_val(cap));    // \label{line:bufalloc:bytes} \label{line:bufalloc:int_val}  //
  bf = caml_alloc(3, 0);                 // allocate the `{cap, used, data}` block   // \label{line:bufalloc:buffer_start}  //
  Store_field(bf, 0, cap); Store_field(bf, 1, r); Store_field(bf, 2, bk);    // \label{line:bufalloc:buffer_end}  //
  CAMLreturn(bf);    // \label{line:bufalloc:gc_two}  //
}

value buf_upd(value iv, value jv, value f, value bf) {
  CAMLparam4(iv, jv, f, bf);
  unsigned char* bts = Custom_contents(Field(bf, 2)); size_t j = Int_val(jv);
  for (size_t i = Int_val(iv); i <= j; i++) {
    bts[i] = Int_val(caml_callback(f, Val_int(i)));
    if (i+1 > Int_val(Field(Field(bf, 1), 0))) Store_field(Field(bf,1), 0, Val_int(i+1));
  }
  CAMLreturn(Val_unit);
}
value wrap_compress(value bf1, value bf2) {
  CAMLparam2(bf1, bf2);
  unsigned char* bts1 = Custom_contents(Field(bf1, 2));
  unsigned char* bts2 = Custom_contents(Field(bf2, 2));
  size_t used1 = Int_val(Field(Field(bf1, 1), 0)); size_t cap2 = Int_val(Field(bf2, 0));
  int res = snappy_compress(bts1, used1, bts2, &cap2);
  Store_field(Field(bf2, 1), 0, Val_int(cap2));
  CAMLreturn((res == SNAPPY_OK) ? Val_int(1) : Val_int(0));
}



value buf_free(value bf) {
  value bk = Field(bf, 2);
  unsigned char* bts = Custom_contents(bk);
  if (bts != NULL) free(bts);
  Custom_contents(bk) = NULL;
  Store_field(Field(bf, 1), 0, Val_int(-1)); // deallocated marker
  return Val_unit;
}

value buf_get(value bf, value i) {
  value bk = Field(bf, 2);
  unsigned char* bg = Custom_contents(bk);
  return Val_int(bg[Int_val(i)]);
}
