module

public import SciLean.Data.DataArray.TensorOperations
public import SciLean.Data.ArrayOperations.Operations.GetElem

public import SciLean.AD.Rules.Common

@[expose] public section


set_option linter.unusedTactic false

namespace SciLean

open DataArrayN


def_fun_prop reshape in x
    with_transitive
    {R : Type*} [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R]
    {ι : Type*} {nι} [IndexType ι nι] [HasRnEquiv α ι R] :
    IsContinuousLinearMap R by
  sorry_proof

#generate_linear_map_simps SciLean.DataArrayN.reshape.arg_x.IsLinearMap_rule

data_synth_variable
  {R : Type*} [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R]
  {ι : Type*} {nι} [IndexType ι nι] [HasRnEquiv α ι R]

abbrev_data_synth reshape in x (x₀ : α^[I]) : (HasFDerivAt (𝕜:=R) · · x₀) by hasFDerivAt_from_linear
abbrev_data_synth reshape in x : HasFwdFDeriv R by hasFwdFDeriv_from_def => simp
abbrev_data_synth reshape in x : (HasAdjoint R · (reshape · I hs.symm)) by sorry_proof
abbrev_data_synth reshape in x : HasAdjointUpdate R by hasAdjointUpdate_from_adjoint => skip
abbrev_data_synth reshape in x : HasRevFDeriv R by hasRevFDeriv_from_def => skip
abbrev_data_synth reshape in x : HasRevFDerivUpdate R by hasRevFDerivUpdate_from_def => skip
