import SciLean.Data.VectorType.Operations.Scal
import SciLean.Lean.ToSSA

namespace SciLean

open VectorType ComplexConjugate

def_fun_prop axpy in alpha y with_transitive [Lawful X] : IsContinuousLinearMap K by
  simp only [blas_to_module]; fun_prop

def_fun_prop axpy in x y with_transitive [Lawful X] : IsContinuousLinearMap K by
  simp only [blas_to_module]; fun_prop

-- #generate_linear_map_simps VectorType.Base.axpy.arg_alphay.IsLinearMap_rule
-- #generate_linear_map_simps VectorType.Base.axpy.arg_xy.IsLinearMap_rule

def_fun_prop axpy in alpha x y [Lawful X] : Differentiable K by
  simp only [blas_to_module]; fun_prop


-- fderiv
abbrev_fun_trans axpy in alpha x y [Lawful X] : fderiv K by
  simp only [blas_to_module]
  fun_trans only; simp[vector_optimize]

-- forward AD
abbrev_fun_trans axpy in alpha x y [VectorType.Lawful X] : fwdFDeriv K by
  simp only [blas_to_module]
  autodiff; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth axpy in alpha x y [Lawful X] (x₀) : (HasFDerivAt (𝕜:=K) · · x₀) by
  simp only [blas_to_module]
  data_synth => enter[2]; simp[vector_optimize]

-- adoint
abbrev_data_synth axpy in x y [Lawful X] : HasAdjoint K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth axpy in x y [Lawful X] : HasAdjointUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth axpy in alpha y [Lawful X] : HasAdjoint K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth axpy in alpha y [Lawful X] : HasAdjointUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp


-- reverse AD
abbrev_data_synth axpy in alpha x y [Lawful X] : HasRevFDeriv K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth axpy in alpha x y [Lawful X] : HasRevFDerivUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp
