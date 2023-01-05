/* -------------------------------------------------------------------- */
#include <sys/types.h>
#include <stdlib.h>

#define CAML_NAME_SPACE

#include <caml/mlvalues.h>
#include <caml/memory.h>

/* -------------------------------------------------------------------- */
static unsigned fls64(uint64_t x) {
  uint64_t mask = ((1L << 32) - 1) << 32;
  unsigned i = 32;
  unsigned r = 64;

  if (!x)
    return 0;

  while (i != 0) {
    if (!(x & mask)) {
      x <<= i;
      r  -= i;
    }

    i    >>= 1;
    mask <<= i;
  }

  return r;
}

/* -------------------------------------------------------------------- */
CAMLprim value fls_63 (value i) {
  CAMLparam1(i);
  const long vi = Long_val(i) & 0x7fffffffffffffff;
  CAMLreturn(Val_int(fls64(vi)));
}
