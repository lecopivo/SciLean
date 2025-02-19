import SciLean.Data.VectorType.Operations.Scal
import SciLean.Data.VectorType.Operations.Mul
import SciLean.Analysis.SpecialFunctions.Exp

namespace SciLean

open VectorType

def_fun_prop exp in x with_transitive [InjectiveGetElem X n] : Differentiable K by
  apply (Differentiable.injective_comp_iff toVec (by fun_prop) (getElem_injective)).2
  simp +unfoldPartialApp [vector_to_spec,VectorType.toVec]
  fun_prop

-- fderiv
abbrev_fun_trans exp in x [InjectiveGetElem X n] : fderiv K by
  conv => enter[2,x]; rw[← fromVec_toVec (exp _)]; simp[vector_to_spec]
  fun_trans
  simp[vector_from_spec]

abbrev_data_synth exp in x [InjectiveGetElem X n] (x₀) : (HasFDerivAt (𝕜:=K) · · x₀) by
  apply hasFDerivAt_from_fderiv
  case deriv => conv => rhs; fun_trans
  case diff => dsimp[autoParam]; fun_prop

-- forward AD
abbrev_fun_trans exp in x [InjectiveGetElem X n] : fwdFDeriv K by
  conv => enter[2,x]; rw[← fromVec_toVec (exp _)]; simp[vector_to_spec]
  fun_trans
  simp[vector_from_spec]; to_ssa; to_ssa; lsimp

-- reverse AD
abbrev_fun_trans exp in x [InjectiveGetElem X n] : revFDeriv K by
  unfold revFDeriv
  fun_trans; to_ssa

abbrev_data_synth exp in x [InjectiveGetElem X n] : HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => conv => rhs; to_ssa; to_ssa; lsimp

abbrev_data_synth exp in x [InjectiveGetElem X n] : HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => conv => rhs; to_ssa; to_ssa; lsimp
