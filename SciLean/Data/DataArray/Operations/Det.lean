import SciLean.Data.DataArray.Operations.Trace
import SciLean.Data.DataArray.Operations.Matmul

namespace SciLean

open DataArrayN

def_fun_prop det in A
    with_transitive : Differentiable R by sorry_proof

abbrev_fun_trans det in A [DecidableEq I] : fderiv R by
  -- Jacobi's formula: https://en.wikipedia.org/wiki/Jacobi%27s_formula
  equals (fun A => fun dA =>L[R] A.det * (A⁻¹ * dA).trace) =>
    sorry_proof

abbrev_fun_trans det in A [DecidableEq I] : fwdFDeriv R by unfold fwdFDeriv; autodiff

abbrev_fun_trans det in A [DecidableEq I] : revFDeriv R by
              unfold revFDeriv
              fun_trans
