#include <lean/lean.h>
#include "util.h"


void ensure_exclusive_float_array(lean_object ** X){
  if (!lean_is_exclusive(*X)) {
    /* printf("warning: making array copy!\n"); */
    *X = lean_copy_float_array(*X);
  }
}

void ensure_exclusive_byte_array(lean_object ** X){
  if (!lean_is_exclusive(*X)) {
    /* printf("warning: making array copy!\n"); */
    *X = lean_copy_byte_array(*X);
  }
}
