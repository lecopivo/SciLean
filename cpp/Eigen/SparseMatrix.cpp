#include <Eigen/Sparse>

#include <lean/lean.h>

#include "CppClass.h"

extern "C" size_t eigenlean_triplets_get_row(size_t, size_t, lean_object*, size_t, lean_object*);
extern "C" size_t eigenlean_triplets_get_col(size_t, size_t, lean_object*, size_t, lean_object*);
extern "C" double eigenlean_triplets_get_val(size_t, size_t, lean_object*, size_t, lean_object*);
extern "C" lean_object * eigenlean_array_to_matrix(lean_object * array, size_t n, size_t m, lean_object*);

struct TripletIterator {
  using value_type = double;
  lean_object * lean_array;
  size_t i;

  Eigen::Index row() const{
    lean_inc(lean_array);
    return eigenlean_triplets_get_row(0, 0, lean_array, i, nullptr);
  }
  
  Eigen::Index col() const{
    lean_inc(lean_array);
    return eigenlean_triplets_get_col(0, 0, lean_array, i, nullptr);
  }
  
  double value() const{
    lean_inc(lean_array);
    return eigenlean_triplets_get_val(0, 0, lean_array, i, nullptr);
  }
  
  TripletIterator const* operator->() const{
    return this;
  }

  TripletIterator& operator++(){
    i++;
    return *this;
  }

  bool operator!=(TripletIterator const& it) const{
    return (i != it.i);
  }
};

extern "C" LEAN_EXPORT lean_obj_res eigenlean_sparse_matrix_mk_from_triplets(size_t n , size_t m, b_lean_obj_arg entries){

  size_t N = lean_array_size(entries);
  
  auto A = new Eigen::SparseMatrix<double>{(Eigen::Index)n, (Eigen::Index)m};

  TripletIterator begin = {entries, 0};
  TripletIterator end = {entries, N};

  A->setFromTriplets(begin, end);
  
  return CppClass_to_lean(A);
}

extern "C" LEAN_EXPORT lean_obj_res eigenlean_sparse_matrix_mk_zero(size_t n , size_t m){

  auto A = new Eigen::SparseMatrix<double>{(Eigen::Index)n, (Eigen::Index)m};
  
  return CppClass_to_lean(A);
}

extern "C" LEAN_EXPORT lean_obj_res eigenlean_sparse_matrix_mk_identity(size_t n){

  auto A = new Eigen::SparseMatrix<double>{(Eigen::Index)n, (Eigen::Index)n};

  A->setIdentity();
  
  return CppClass_to_lean(A);
}

extern "C" LEAN_EXPORT lean_obj_res eigenlean_sparse_matrix_to_dense(size_t n, size_t m, b_lean_obj_arg _A){

  auto A = to_cppClass<Eigen::SparseMatrix<double>>(_A);

    // `FloatArray` is just `sarray`, see for example `lean_mk_empty_float_array`
  lean_object * result = lean_alloc_sarray(sizeof(double), n*m, n*m); 

  auto denseA = Eigen::Map<Eigen::MatrixXd>(lean_float_array_cptr(result), n, m);

  denseA = *A;
  
  return eigenlean_array_to_matrix(result, n, m, nullptr);
}

