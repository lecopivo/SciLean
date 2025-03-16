#include <math.h>
#include <lean/lean.h>
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
