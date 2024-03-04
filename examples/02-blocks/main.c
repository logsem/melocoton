#include <stdio.h>
#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>

value caml_swap_pair(value pair)
{
  // (non-scalar) function parameters of type [value] must be registered using CAMLparamX
  CAMLparam1(pair);

  // (non-scalar) local variables of type [value] must be registered using CAMLlocalX
  CAMLlocal3(fst, snd, result);

  // [pair] is a block, composed of:
  // - a header, holding the size of the block, and a tag
  // - following, as many fields as the size of the block
  //   (each field holding a [value], in the case of 0-tagged blocks)
  //
  // in the case of pairs, the tag is 0, and there are two fields (size=2)
  fst = Field(pair, 0);
  snd = Field(pair, 1);

  // alloc: possible preemption point
  result = caml_alloc(2 /* size */, 0 /* tag (0 for tuples/records) */);

  // at this point, [result] is already a valid caml value: it has been
  // pre-initialized by [caml_alloc] (with Val_unit), so it would be safe to
  // trigger a GC now.
  //
  // There are lower level functions that are slightly faster and do not perform
  // automatic initialization, and thus require more care
  // -> See manual Chapter 20, Sec 5.2

  // updating a block: write barrier
  // does not call the GC, but may need to update GC tables in the general case
  //
  // in some restricted scenarios, it is possible to update the field directly
  // without going through the barrier, i.e.
  // Field(result, 0) = ...
  // -> See manual Chapter 20, Sec 5.2
  Store_field(result, 0, snd);
  Store_field(result, 1, fst);

  CAMLreturn(result);
}
