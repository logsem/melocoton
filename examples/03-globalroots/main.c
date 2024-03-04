#include <stdio.h>
#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>

static value storage;

value caml_init_storage(value unit)
{
  CAMLparam0();
  // note that the empty string is a block of size 1 containing \0, for
  // compatibility with C strings, it is not a 0-sized block of tag String_tag
  storage = caml_alloc_string(0);
  caml_register_global_root(&storage);
  CAMLreturn(Val_unit);
}

value caml_store_string(value str)
{
  CAMLparam1(str);
  storage = str;
  // when using CAMLparam/CAMLlocal, we MUSN'T use the [return] keyword
  // but use CAMLreturn instead
  CAMLreturn(Val_unit);
}

value caml_retrieve_string(value unit)
{
  CAMLparam0();
  CAMLreturn(storage);
}
