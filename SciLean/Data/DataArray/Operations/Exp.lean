import SciLean.Data.DataArray.Operations.Multiply
import SciLean.Data.ArrayType.Properties
import SciLean.Analysis.SpecialFunctions.Exp

namespace SciLean.DataArrayN

open  Scalar

variable
  {R : Type*} [RealScalar R] [PlainDataType R]
  {I : Type*} [IndexType I]

set_default_scalar R


def_fun_prop exp in x : Differentiable R by
  unfold exp; fun_prop

abbrev_fun_trans DataArrayN.exp in x : fderiv R by
  equals (fun x => fun dx =>L[R] dx.multiply x.exp) =>
    fun_trans[multiply,exp,Function.HasUncurry.uncurry]

abbrev_fun_trans DataArrayN.exp in x : fwdFDeriv R by
  unfold fwdFDeriv
  autodiff

abbrev_fun_trans DataArrayN.exp in x [DecidableEq I] : revFDeriv R by
  unfold revFDeriv
  autodiff
