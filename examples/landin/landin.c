#include <stdio.h>
#include <snappy-c.h>
#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/callback.h>
#include <caml/custom.h>

#define caml_alloc_custom(k) (caml_alloc_custom(&ops, k, 0, 1))
#define Custom_contents(k) (*(unsigned char**) (Data_custom_val(k)))


value callk(value l, value x) {
  value f = Field(l, 0);
  return caml_callback(f, x);
}