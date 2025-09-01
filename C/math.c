#include <lean/lean.h>
#include <math.h>

LEAN_EXPORT double scilean_float_lgamma(double x){
  return lgamma(x);
}

LEAN_EXPORT double scilean_float_tgamma(double x){
  return tgamma(x);
}




