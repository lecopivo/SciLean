#pragma once

#include <lean/lean.h>

template<class T>
static void CppClass_finalize(void * obj){
  delete static_cast<T*>(obj);
}

template<class T>
static void CppClass_foreach(void *, b_lean_obj_arg){
  // do nothing since `S` does not contain nested Lean objects
}

template<class T>
static lean_external_class *CppClass_class = nullptr;

template<class T>
static inline lean_object * CppClass_to_lean(T * t) {
    if (CppClass_class<T> == nullptr) {
        CppClass_class<T> = lean_register_external_class(CppClass_finalize<T>, CppClass_foreach<T>);
    }
    return lean_alloc_external(CppClass_class<T>, t);
}

template<class T>
static inline T const * to_cppClass(b_lean_obj_arg o) {
  return static_cast<T *>(lean_get_external_data(o));
}


