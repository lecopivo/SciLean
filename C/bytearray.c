#include <math.h>
#include <lean/lean.h>
#include <string.h>
#include "util.h"

LEAN_EXPORT lean_obj_res scilean_byte_array_mk_exclusive(lean_obj_arg a){
  lean_obj_res r;
  if (lean_is_exclusive(a)) r = a;
  else r = lean_copy_byte_array(a);
  return r;
}

LEAN_EXPORT lean_obj_res scilean_byte_array_uset_float_unsafe(lean_obj_arg a, size_t i, double v){
  /* double * r = (double*)(lean_sarray_cptr(a)); */
  /* r[i] = v; */
  return ((((double*)(lean_sarray_cptr(a)))[i] = v), a);
}


LEAN_EXPORT lean_obj_res scilean_byte_array_replicate(b_lean_obj_arg size, uint8_t v){
  if (!lean_is_scalar(size)) lean_internal_panic_out_of_memory();
  size_t n = lean_unbox(size);
  lean_obj_res r = lean_alloc_sarray(1, n, n);
  memset(lean_sarray_cptr(r), v, n);
  return r;
}
