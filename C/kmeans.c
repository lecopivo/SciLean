#include <lean/lean.h>
#include <float.h>
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
