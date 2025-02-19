import SciLean.Data.VectorType.Operations.Scal
import SciLean.Lean.ToSSA

namespace SciLean

open VectorType ComplexConjugate

def_fun_prop axpby in alpha y with_transitive [InjectiveGetElem X n] : IsContinuousLinearMap K by
  simp only [blas_to_module]; fun_prop

def_fun_prop axpby in alpha beta with_transitive [InjectiveGetElem X n] : IsContinuousLinearMap K by
  simp only [blas_to_module]; fun_prop

def_fun_prop axpby in x y with_transitive [InjectiveGetElem X n] : IsContinuousLinearMap K by
  simp only [blas_to_module]; fun_prop

-- #generate_linear_map_simps VectorType.Base.axpby.arg_alphay.IsLinearMap_rule
-- #generate_linear_map_simps VectorType.Base.axpby.arg_xy.IsLinearMap_rule

def_fun_prop axpby in alpha x beta y [InjectiveGetElem X n] : Differentiable K by
  simp only [blas_to_module]; fun_prop


-- fderiv
abbrev_fun_trans axpby in alpha x beta y [InjectiveGetElem X n] : fderiv K by
  simp only [blas_to_module]
  fun_trans only; simp[vector_optimize]

-- forward AD
abbrev_fun_trans axpby in alpha beta x y [InjectiveGetElem X n] : fwdFDeriv K by
  simp only [blas_to_module]
  autodiff; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth axpby in alpha beta x y [InjectiveGetElem X n] (x₀) : (HasFDerivAt (𝕜:=K) · · x₀) by
  simp only [blas_to_module]
  data_synth => enter[2]; simp[vector_optimize]

-- adoint
abbrev_data_synth axpby in alpha beta [InjectiveGetElem X n] : HasAdjoint K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth axpby in alpha beta [InjectiveGetElem X n] : HasAdjointUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth axpby in x y [InjectiveGetElem X n] : HasAdjoint K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth axpby in x y [InjectiveGetElem X n] : HasAdjointUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth axpby in alpha y [InjectiveGetElem X n] : HasAdjoint K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth axpby in alpha y [InjectiveGetElem X n] : HasAdjointUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp


-- reverse AD
abbrev_data_synth axpby in alpha x beta y [InjectiveGetElem X n] : HasRevFDeriv K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth axpby in alpha x beta y [InjectiveGetElem X n] : HasRevFDerivUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp
