import SciLean.Data.DataArray.Operations.Multiply
import SciLean.Data.ArrayType.Properties
import SciLean.Analysis.SpecialFunctions.Log

namespace SciLean.DataArrayN

open  Scalar

variable
  {R : Type*} [RealScalar R] [PlainDataType R]
  {W} [NormedAddCommGroup W] [NormedSpace R W]
  {U} [NormedAddCommGroup U] [AdjointSpace R U] [CompleteSpace U]
  {I : Type*} [IndexType I]

set_default_scalar R

def_fun_prop (x : W → R^[I]) (hx : Differentiable R x) (hx' : ∀ w i, (x w)[i] ≠ 0) :
    Differentiable R (fun w => (x w).log) by
  unfold log
  intro x
  fun_prop (disch:=sorry_proof)

-- abbrev_fun_trans DataArrayN.log in x : fderiv R by
--   equals (fun x => fun dx =>L[R] dx.multiply x.exp) =>
--     fun_trans[multiply,exp,Function.HasUncurry.uncurry]

-- abbrev_fun_trans DataArrayN.exp in x : fwdFDeriv R by
--   unfold fwdFDeriv
--   autodiff

-- abbrev_fun_trans DataArrayN.exp in x [DecidableEq I] : revFDeriv R by
--   unfold revFDeriv
--   autodiff
