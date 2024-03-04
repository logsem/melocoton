#include <stdio.h>
#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/callback.h>

value caml_twice(value f, value x) {
  CAMLparam2(f, x);
  caml_callback(f, x);
  caml_callback(f, x);
  CAMLreturn(Val_unit);
}

void handle_exn(value exn) {
  CAMLparam1(exn);
  if (exn == *caml_named_value("myexn"))
    printf("C: raised MyExn\n");
  else
    printf("C: raised an exception\n");
  CAMLreturn0;
}

value caml_twice_catch(value f, value x) {
  CAMLparam2(f, x);
  CAMLlocal1(ret);
  ret = caml_callback_exn(f, x);
  if(Is_exception_result(ret))
    handle_exn(Extract_exception(ret));
  ret = caml_callback_exn(f, x);
  if(Is_exception_result(ret))
    handle_exn(Extract_exception(ret));
  CAMLreturn(Val_unit);
}
