#include <math.h>
#include <lean/lean.h>
#include "util.h"

LEAN_EXPORT lean_obj_res scilean_float_array_to_byte_array(lean_obj_arg a){
  lean_obj_res r;
  if (lean_is_exclusive(a)) r = a;
  else r = lean_copy_float_array(a);
  lean_to_sarray(r)->m_size *= 8;
  lean_to_sarray(r)->m_capacity *= 8;
  return r;
}

LEAN_EXPORT lean_obj_res scilean_byte_array_to_float_array(lean_obj_arg a){
  lean_obj_res r;
  if (lean_is_exclusive(a)) r = a;
  else r = lean_copy_byte_array(a);
  lean_to_sarray(r)->m_size /= 8;
  lean_to_sarray(r)->m_capacity /= 8;
  return r;
}




