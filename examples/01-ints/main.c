#include <stdio.h>
#define CAML_NAME_SPACE
#include <caml/mlvalues.h>

value caml_get_int(value u)
{
  return Val_int(42);
}

value caml_my_print_int(value x)
{
  printf("from c: %d\n", Int_val(x));
  return Val_unit; /* = Val_int(0) */
}
