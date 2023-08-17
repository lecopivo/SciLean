#include "CppClass.h"
#include <Eigen/Dense>
#include <lean/lean.h>
// #include <iostream>

extern "C" lean_object * eigenlean_get_matrix_array(size_t n, size_t m, lean_object * matrix);
extern "C" size_t eigenlean_get_matrix_rows(b_lean_obj_arg matrix);
extern "C" size_t eigenlean_get_matrix_cols(b_lean_obj_arg matrix);
extern "C" lean_object * eigenlean_array_to_matrix(lean_object * array, size_t n, size_t m, lean_object*);

extern "C" double * eigenlean_get_matrix_ptr(size_t n, size_t m, b_lean_obj_arg matrix){
  return lean_float_array_cptr(eigenlean_get_matrix_array(n, m, matrix));
}

Eigen::Map<Eigen::MatrixXd> to_eigenMatrix(lean_object * matrix, size_t n, size_t m){
  return Eigen::Map<Eigen::MatrixXd>(eigenlean_get_matrix_ptr(n, m, matrix), n, m);  
}

extern "C" LEAN_EXPORT lean_obj_res eigenlean_ldlt(size_t n, b_lean_obj_arg matrix){

  auto const& A = to_eigenMatrix(matrix, n, n);

  auto ldlt = new Eigen::LDLT<Eigen::MatrixXd>{A};

  return CppClass_to_lean(ldlt);
}

extern "C" LEAN_EXPORT lean_obj_res eigenlean_ldlt_solve(size_t n, size_t m, b_lean_obj_arg _ldlt, b_lean_obj_arg _rhs){ // b_lean_obj_arg _rhs)

  auto const& ldlt = *to_cppClass<Eigen::LDLT<Eigen::MatrixXd>>(_ldlt);
  auto const& rhs  = to_eigenMatrix(_rhs, n, m);

  // `FloatArray` is just `sarray`, see for example `lean_mk_empty_float_array`
  lean_object * result = lean_alloc_sarray(sizeof(double), n*m, n*m); 

  auto lhs = Eigen::Map<Eigen::MatrixXd>(lean_float_array_cptr(result), n, m);

  lhs = ldlt.solve(rhs);
  
  return eigenlean_array_to_matrix(result, n, m, nullptr);
}
