#include <stdio.h>
#include <snappy-c.h>
#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/callback.h>
#include <caml/custom.h>

// some boilerplate related to OCaml custom blocks
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

int max(int a, int b) {
  return a>b?a:b;
}

#define caml_alloc_custom(k) (caml_alloc_custom(&ops, k, 0, 1))


#define Data_val(k) (*(unsigned char**) (Data_custom_val(k)))
value buf_alloc(value cap) {
  CAMLparam0(); CAMLlocal1(bk);
  bk = caml_alloc_custom(sizeof(void*));
  size_t len = snappy_max_compressed_length(Int_val(cap));
  void *bts = malloc(len); Data_val(bk) = bts;
  value bf = caml_alloc(3, 0);
  caml_modify(&Field(bf, 0), bk);
  caml_modify(&Field(bf, 1), Val_int(0));
  caml_modify(&Field(bf, 2), Val_int(len));
  CAMLreturn(bf);
}
value buf_upd(value iv, value jv, value f, value bf) {
  CAMLparam1(f);
  value bk = Field(bf, 0);  unsigned char* bts = Data_val(bk); size_t j = Int_val(jv);
  size_t sz = max(j+1, Int_val(Field(bf, 1))); caml_modify(&Field(bf, 1), Val_int(sz));
  for (size_t i = Int_val(iv); i <= j; i++)
    bts[i] = Int_val(caml_callback(f, Val_int(i)));
  CAMLreturn(Val_unit);
}
value buf_compress(value bf1, value bf2) {
  value bk1 = Field(bf1, 0); value bk2 = Field(bf2, 0);
  unsigned char* bts1 = Data_val(bk1); unsigned char* bts2 = Data_val(bk2);
  size_t used1 = Int_val(Field(bf1, 1)); size_t nused2 = Int_val(Field(bf2, 2));
  int res = snappy_compress(bts1, used1, bts2, &nused2);
  caml_modify(&Field(bf2, 1), Val_int(nused2));
  return (res == SNAPPY_OK) ? Val_int(1) : Val_int(0);
}

value buf_free(value bf) {
  value bk = Field(bf, 0);
  unsigned char* bts = Data_val(bk);
  if (bts != NULL) free(bts);
  Data_val(bk) = NULL;
  return Val_unit;
}

value buf_get(value bf, value i) {
  value bk = Field(bf, 0);
  unsigned char* bg = Data_val(bk);
  return Val_int(bg[Int_val(i)]);
}
