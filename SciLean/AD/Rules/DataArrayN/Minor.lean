module

public import SciLean.Data.DataArray.Operations

public import SciLean.AD.Rules.Common

public import SciLean.AD.Rules.IndexType.Fold
public import SciLean.Data.ArrayOperations.Operations.GetElem
public import SciLean.Data.ArrayOperations.Operations.OfFn

@[expose] public section


namespace SciLean

set_option linter.unusedTactic false

open DataArrayN


def_fun_prop minor in A [RealScalar R] [BLAS (DataArray R) R R] : IsContinuousLinearMap R by
  unfold minor; fun_prop

data_synth_variable [RealScalar R] [BLAS (DataArray R) R R]

abbrev_data_synth DataArrayN.minor in A (A₀) : (HasFDerivAt (𝕜:=R) · · A₀) by hasFDerivAt_from_linear
abbrev_data_synth DataArrayN.minor in A : HasFwdFDeriv R by hasFwdFDeriv_from_def => simp

def_data_synth DataArrayN.minor in A : HasAdjoint R by
  unfold DataArrayN.minor
  simp -zeta [Function.HasUncurry.uncurry]
  data_synth => enter[3]; skip

def_data_synth DataArrayN.minor in A : HasAdjointUpdate R by
  unfold DataArrayN.minor
  simp -zeta [Function.HasUncurry.uncurry]
  data_synth => enter[3]; skip

abbrev_data_synth DataArrayN.minor in A : HasRevFDeriv R by hasRevFDeriv_from_def => skip
abbrev_data_synth DataArrayN.minor in A : HasRevFDerivUpdate R by hasRevFDerivUpdate_from_def => skip
