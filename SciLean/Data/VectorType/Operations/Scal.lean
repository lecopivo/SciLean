import SciLean.Data.VectorType.Operations.ToVec
import SciLean.Data.VectorType.BaseSimps
import SciLean.Analysis.SpecialFunctions.StarRingEnd
import SciLean.Data.VectorType.Optimize
import SciLean.Lean.ToSSA

namespace SciLean


section Simps

variable
  {R K} {_ : RealScalar R} {_ : Scalar R K}
  {n} {_ : IndexType n}
  {X} [VectorType.Base X n K] [VectorType.Lawful X]


end Simps

set_option linter.unusedVariables false in
theorem IsContinuousLinearMap.injective_comp_iff
  {R : Type*} [RCLike R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace R Z]
  {f : X → Y} (g : Y → Z) (hg : IsContinuousLinearMap R g) (hg' : g.Injective)  :
  IsContinuousLinearMap R f ↔ IsContinuousLinearMap R (fun x => g (f x)) := sorry_proof

set_option linter.unusedVariables false in
theorem Differentiable.injective_comp_iff
  {R : Type*} [RCLike R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace R Z]
  {f : X → Y} (g : Y → Z) (hg : Differentiable R g) (hg' : g.Injective)  :
  Differentiable R f ↔ Differentiable R (fun x => g (f x)) := sorry_proof

open VectorType ComplexConjugate

-- linearity
def_fun_prop scal in x with_transitive [Lawful X] : IsContinuousLinearMap K by
  simp only [blas_to_module]; fun_prop

def_fun_prop scal in alpha with_transitive [Lawful X] : IsContinuousLinearMap K by
  simp only [blas_to_module]; fun_prop

#generate_linear_map_simps VectorType.Base.scal.arg_x.IsLinearMap_rule
#generate_linear_map_simps VectorType.Base.scal.arg_alpha.IsLinearMap_rule

-- differentiable
def_fun_prop scal in alpha x with_transitive [Lawful X] : Differentiable K by
  simp only [blas_to_module]; fun_prop

-- fderiv
abbrev_fun_trans scal in alpha x [Lawful X] : fderiv K by
  simp only [blas_to_module]
  conv => enter[x]; fun_trans
  simp [vector_optimize]

abbrev_data_synth scal in alpha x [Lawful X] (x₀) : (HasFDerivAt (𝕜:=K) · · x₀) by
  simp only [blas_to_module]
  data_synth => enter[2]; simp[vector_optimize]

-- forward AD
abbrev_fun_trans scal in alpha x [Lawful X] : fwdFDeriv K by
  simp only [blas_to_module]
  conv => enter[x]; fun_trans
  simp [vector_optimize]; to_ssa; to_ssa; lsimp

-- adjoint
abbrev_fun_trans scal in x [Lawful X] : adjoint K by
  simp only [blas_to_module]
  fun_trans
  simp [vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_fun_trans scal in alpha [Lawful X] : adjoint K by
  simp only [blas_to_module]
  fun_trans
  simp [vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth scal in x [Lawful X] : HasAdjoint K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]

abbrev_data_synth scal in x [Lawful X] : HasAdjointUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]

abbrev_data_synth scal in alpha [Lawful X] : HasAdjoint K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]

abbrev_data_synth scal in alpha [Lawful X] : HasAdjointUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]


-- reverse AD
abbrev_fun_trans VectorType.scal in alpha x [VectorType.Lawful X] : revFDeriv K by
  simp only [blas_to_module]
  fun_trans
  simp [vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth scal in alpha x [Lawful X] : HasRevFDeriv K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth scal in alpha x [Lawful X] : HasRevFDerivUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp
