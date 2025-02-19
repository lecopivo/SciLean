import SciLean.Data.VectorType.Operations.ToVec
import SciLean.Analysis.SpecialFunctions.StarRingEnd
import SciLean.Lean.ToSSA

namespace SciLean

open VectorType ComplexConjugate

-- linearity
def_fun_prop scal in x with_transitive [InjectiveGetElem X n] : IsContinuousLinearMap K by
  simp only [blas_to_module]; fun_prop

def_fun_prop scal in alpha with_transitive [InjectiveGetElem X n] : IsContinuousLinearMap K by
  simp only [blas_to_module]; fun_prop

#generate_linear_map_simps VectorType.Base.scal.arg_x.IsLinearMap_rule
#generate_linear_map_simps VectorType.Base.scal.arg_alpha.IsLinearMap_rule

-- differentiable
def_fun_prop scal in alpha x with_transitive [InjectiveGetElem X n] : Differentiable K by
  simp only [blas_to_module]; fun_prop

-- fderiv
abbrev_fun_trans scal in alpha x [InjectiveGetElem X n] : fderiv K by
  simp only [blas_to_module]
  conv => enter[x]; fun_trans
  simp [vector_optimize]

abbrev_data_synth scal in alpha x [InjectiveGetElem X n] (x₀) : (HasFDerivAt (𝕜:=K) · · x₀) by
  simp only [blas_to_module]
  data_synth => enter[2]; simp[vector_optimize]

-- forward AD
abbrev_fun_trans scal in alpha x [InjectiveGetElem X n] : fwdFDeriv K by
  simp only [blas_to_module]
  conv => enter[x]; fun_trans
  simp [vector_optimize]; to_ssa; to_ssa; lsimp

-- adjoint
abbrev_fun_trans scal in x [InjectiveGetElem X n] : adjoint K by
  simp only [blas_to_module]
  fun_trans
  simp [vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_fun_trans scal in alpha [InjectiveGetElem X n] : adjoint K by
  simp only [blas_to_module]
  fun_trans
  simp [vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth scal in x [InjectiveGetElem X n] : HasAdjoint K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]

abbrev_data_synth scal in x [InjectiveGetElem X n] : HasAdjointUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]

abbrev_data_synth scal in alpha [InjectiveGetElem X n] : HasAdjoint K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]

abbrev_data_synth scal in alpha [InjectiveGetElem X n] : HasAdjointUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]


-- reverse AD
abbrev_fun_trans VectorType.scal in alpha x [InjectiveGetElem X n] : revFDeriv K by
  simp only [blas_to_module]
  fun_trans
  simp [vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth scal in alpha x [InjectiveGetElem X n] : HasRevFDeriv K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth scal in alpha x [InjectiveGetElem X n] : HasRevFDerivUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp
