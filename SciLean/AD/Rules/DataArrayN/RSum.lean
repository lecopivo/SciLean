module

public import SciLean.Data.DataArray.TensorOperations
public import SciLean.Data.DataArray.Algebra
public import SciLean.Data.ArrayOperations.Operations.GetElem

public import SciLean.AD.Rules.Common

@[expose] public section


namespace SciLean

open DataArrayN

-- def_fun_prop rsum in x
--   with_transitiveo
--   [BLAS (DataArray R) R R] :
--   IsContinuousLinearMap R by sorry_proof

-- #generate_linear_map_simps rsum.arg_x.IsLinearMap_rule

-- abbrev_data_synth rsum in x [BLAS (DataArray R) R R] (x₀ : X^[I]) : (HasFDerivAt (𝕜:=R) · · x₀) by
--   apply hasFDerivAt_from_isContinuousLinearMap; fun_prop

-- abbrev_data_synth rsum in x [BLAS (DataArray R) R R] : HasFwdFDeriv R by
--   apply hasFwdFDeriv_from_hasFDerivAt
--   case deriv => intros; data_synth
--   case simp => intros; rfl

-- abbrev_data_synth rsum in x [BLAS (DataArray R) R R] : (HasAdjoint R · (rconst X I)) by
--   sorry_proof

-- abbrev_data_synth rsum in x [BLAS (DataArray R) R R] :
--     (HasAdjointUpdate R · (fun ds x' => x'.rscalAdd (1:R) ds)) by
--   sorry_proof

-- abbrev_data_synth rsum in x [BLAS (DataArray R) R R] : HasRevFDeriv R by
--   apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
--   case deriv => intros; data_synth
--   case adjoint => intros; (try simp); data_synth
--   case simp => rfl

-- abbrev_data_synth rsum in x [BLAS (DataArray R) R R] : HasRevFDerivUpdate R by
--   apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
--   case deriv => intros; data_synth
--   case adjoint => intros; (try simp); data_synth
--   case simp => rfl
