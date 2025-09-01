import SciLean
import SciLean.Data.DataArray
import SciLean.Data.ArrayType
-- import SciLean.Data.ArrayType.Properties

namespace SciLean.ML


variable
  {R : Type} [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R] [LawfulBLAS (DataArray R) R R]
  {ι : Type} {nι} [IndexType ι nι] [DecidableEq ι]

set_default_scalar K

def dense [BLAS (DataArray R) R R] [LawfulBLAS (DataArray R) R R] (n : Nat)
    (weights : R^[n,ι]) (bias : R^[n]) (x : R^[ι]) : R^[n] :=
  (weights * x + bias) rewrite_by simp[vector_optimize]

-- def_fun_prop dense in weights bias x
--   with_transitive
--   : Differentiable R

-- def_fun_trans dense in weights bias x
--   arg_subsets
--   [DecidableEq ι] : revFDeriv R  by (unfold dense; autodiff)

-- def_fun_trans dense in weights bias x
--   arg_subsets
--   [DecidableEq ι] : fwdFDeriv R  by (unfold dense; autodiff)
