#include <stdio.h>
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

// Not completely sure about the integer sizes here;
// maybe some of those 'int's should be something else--oh well.
value caml_miniba_init(value clos, value len)
{
  CAMLparam1(clos); // registerroot(&clos);
  int sz = Int_val(len); // val2int

  // allocate the C buffer
  char* buf = malloc(sz);

  // initialize it by invoking the callback
  value byte;
  for (int i = 0; i < sz; i++) {
    byte = caml_callback(clos, Val_int(i) /* int2val */);
    buf[i] = (char)Int_val(byte); //val2int
  }

  // allocate the foreign block holding the C pointer to the buffer
  value fblock = caml_alloc_custom(&ops, sizeof(char*), 0, 1); // allocforeign
  *((char**)Data_custom_val(fblock)) = buf; // writeforeign

  CAMLreturn(fblock); // unregisterroot(&clos); return fblock;
}

value caml_miniba_free(value fblock)
{
  char* buf = *((char**)Data_custom_val(fblock)); // readforeign
  // write NULL in the foreign block to mark it as deallocated
  *((char**)Data_custom_val(fblock)) = NULL; // writeforeign
  // free the underlying C buffer
  free(buf);

  return Val_unit;
}

// function coming from a pre-existing C library
int myhash(char* data, int sz) {
  // do something smarter here...
  int hash = 0;
  for (int i = 0; i < sz; i++)
    hash += data[i];
  return hash;
}


value caml_miniba_hash(value fblock, value len)
{
  char* buf = *((char**)Data_custom_val(fblock)); // readforeign

  value ret;

  // Check that the underlying C buffer has not been deallocated
  if (buf == NULL) {
    // return None.
    // in OCaml, None corresponds to 0.
    // TODO: what is the representation of option in our miniML language?
    ret = Val_int(0); // int2val
  } else {
    // call myhash on the C buffer
    int hash = myhash(buf, Int_val(len) /* val2int */);
    // return Some(hash)
    // in OCaml, this is implemented by a structured block containing the hash
    ret = caml_alloc(1 /* size */, 0 /* tag */); // alloc
    Store_field(ret, 0, Val_int(hash) /* int2val */); // modify
  }

  return ret;
}
