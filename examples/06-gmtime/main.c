#include <time.h>
#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>

value caml_gmtime(value t) {
  CAMLparam1(t);
  CAMLlocal1(result);
  time_t timer;
  struct tm *tm;

  timer  = (time_t) Double_val(t);
  tm     = gmtime(&timer);

  result = caml_alloc(9, 0);

  Store_field(result, 0, Val_int (tm->tm_sec  ));
  Store_field(result, 1, Val_int (tm->tm_min  ));
  Store_field(result, 2, Val_int (tm->tm_hour ));
  Store_field(result, 3, Val_int (tm->tm_mday ));
  Store_field(result, 4, Val_int (tm->tm_mon  ));
  Store_field(result, 5, Val_int (tm->tm_year ));
  Store_field(result, 6, Val_int (tm->tm_wday ));
  Store_field(result, 7, Val_int (tm->tm_yday ));
  Store_field(result, 8, Val_bool(tm->tm_isdst));

  CAMLreturn(result);
}

