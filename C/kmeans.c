#include <lean/lean.h>
#include <float.h>
#include <string.h> 
#include "util.h"

LEAN_EXPORT double scilean_kmeans(size_t d, size_t n, size_t k, b_lean_obj_arg points, b_lean_obj_arg centroids){
  double * p = lean_float_array_cptr(points);
  double * c = lean_float_array_cptr(centroids);

  double loss = 0.0;
  for (int i=0; i<n; i++){

    double minNorm2 = DBL_MAX;

    for (int j=0; j<k; j++){

      double norm2 = 0.0;

      for (int l=0; l<d; l++){
        double dx = p[i*d+l] - c[j*d+l];
        norm2 += dx*dx;
      }

      if (norm2 < minNorm2) {
        minNorm2 = norm2;
      }
    }

    loss += minNorm2;
  }

  return loss;
}

LEAN_EXPORT lean_obj_res scilean_kmeans_direction(size_t d, size_t n, size_t k, b_lean_obj_arg points, b_lean_obj_arg centroids){

  lean_obj_res r = lean_alloc_sarray(1, k * d * sizeof(double), k * d * sizeof(double));

  double * J = (double*)lean_float_array_cptr(r);
  double * diagH = (double*)malloc(k * d * sizeof(double));
  
  memset(J, 0, k * d * sizeof(double));
  memset(diagH, 0, k * d * sizeof(double));

  double * p = lean_float_array_cptr(points);
  double * c = lean_float_array_cptr(centroids);

  double loss = 0.0;
  for (int i=0; i<n; i++){

    int minj = 0;
    double minNorm2 = DBL_MAX;

    for (int j=0; j<k; j++){

      double norm2 = 0.0;

      for (int l=0; l<d; l++){
        double dx = p[i*d+l] - c[j*d+l];
        norm2 += dx*dx;
      }

      if (norm2 < minNorm2) {
        minNorm2 = norm2;
        minj = j;
      }
    }

    for (int l=0; l<d; l++){
      int idx = minj*d + l;
      diagH[idx] += 2.0;
      J[idx] += 2 * (c[idx] - p[i*d+l]);
    }

    loss += minNorm2;
  }

  for (int i=0; i<d*k; i++){
    // J[i] /= diag[i]
    J[i] += diagH[i];
  }
  free(diagH);

  return r;
}
