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

// Float32 FFI functions (Float32 is boxed in Lean)
// i is a byte offset (must be 4-byte aligned for Float32)

LEAN_EXPORT lean_obj_res scilean_byte_array_uget_float32(b_lean_obj_arg a, size_t i){
  uint8_t* bytes = lean_sarray_cptr(a);
  float v = *(float*)(bytes + i);
  return lean_box_float32(v);
}

LEAN_EXPORT lean_obj_res scilean_byte_array_uset_float32(lean_obj_arg a, size_t i, b_lean_obj_arg v_box){
  float v = lean_unbox_float32(v_box);
  lean_obj_res r;
  if (lean_is_exclusive(a)) r = a;
  else r = lean_copy_byte_array(a);
  uint8_t* bytes = lean_sarray_cptr(r);
  *(float*)(bytes + i) = v;
  return r;
}
