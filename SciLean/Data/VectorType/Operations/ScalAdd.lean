import SciLean.Data.VectorType.Operations.ToVec
import SciLean.Data.VectorType.Operations.FromVec
import SciLean.Analysis.SpecialFunctions.StarRingEnd
import SciLean.Data.VectorType.Operations.Scal
import SciLean.Lean.ToSSA

namespace SciLean


section Simps

@[fun_trans]
theorem fderiv_affine_map
  {R : Type*} [RCLike R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace R Y] [FiniteDimensional R Y]
  {f : X → Y} (_hf : IsAffineMap R f) :
  fderiv R f = fun _ => ContinuousLinearMap.mk' R (fun dx => (f dx - f 0)) sorry_proof := sorry_proof

open VectorType

-- affine, linear, differentiable
def_fun_prop scalAdd in alpha with_transitive [InjectiveGetElem X n] : IsAffineMap K by
  simp only [blas_to_module]; fun_prop

def_fun_prop scalAdd in beta with_transitive [InjectiveGetElem X n] : IsAffineMap K by
  simp only [blas_to_module]; fun_prop

def_fun_prop scalAdd in x with_transitive [InjectiveGetElem X n] : IsAffineMap K by
  simp only [blas_to_module]; fun_prop

def_fun_prop scalAdd in beta x with_transitive [InjectiveGetElem X n] : IsContinuousLinearMap K by
  simp only [blas_to_module]; fun_prop

#generate_linear_map_simps VectorType.Dense.scalAdd.arg_betax.IsLinearMap_rule

def_fun_prop scalAdd in alpha beta x with_transitive [InjectiveGetElem X n] : Differentiable K by
  simp only [blas_to_module]; fun_prop

-- fderiv
abbrev_fun_trans scalAdd in alpha beta x [InjectiveGetElem X n] : fderiv K by
  rw[fderiv_wrt_prod3]
  autodiff [vector_optimize,←sub_eq_add_neg]
  simp[vector_optimize]

abbrev_data_synth scalAdd in alpha beta x [InjectiveGetElem X n] (x₀) : (HasFDerivAt (𝕜:=K) · · x₀) by
  apply hasFDerivAt_from_fderiv
  case deriv => (conv => rhs; dsimp; autodiff; enter[2]; to_ssa; to_ssa; lsimp)
  case diff => dsimp [autoParam]; fun_prop

-- forward AD
abbrev_fun_trans scalAdd in alpha beta x [InjectiveGetElem X n] : fwdFDeriv K by
  unfold fwdFDeriv
  fun_trans;
  to_ssa; to_ssa; lsimp

-- adjoint
abbrev_fun_trans scalAdd in beta x [InjectiveGetElem X n] : adjoint K by
  simp only [blas_to_module]
  fun_trans
  simp [vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_fun_trans scalAdd in alpha beta [InjectiveGetElem X n] : adjoint K by
  simp only [blas_to_module]
  fun_trans
  simp [vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth scalAdd in beta x [InjectiveGetElem X n] : HasAdjoint K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth scalAdd in beta x [InjectiveGetElem X n] : HasAdjointUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth scalAdd in alpha beta [InjectiveGetElem X n] : HasAdjoint K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth scalAdd in alpha beta [InjectiveGetElem X n] : HasAdjointUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

-- reverse AD
abbrev_data_synth scalAdd in alpha beta x [InjectiveGetElem X n] : HasRevFDeriv K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth scalAdd in alpha beta x [InjectiveGetElem X n] : HasRevFDerivUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp


abbrev_data_synth scalAdd in beta x [InjectiveGetElem X n] : HasRevFDeriv K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp

abbrev_data_synth scalAdd in beta x [InjectiveGetElem X n] : HasRevFDerivUpdate K by
  simp only [blas_to_module]
  data_synth => enter[3]; simp[vector_optimize]; to_ssa; to_ssa; lsimp
