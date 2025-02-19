import SciLean.Data.VectorType.Operations.ToVec

namespace SciLean

def_fun_prop VectorType.fromVec in f [InjectiveGetElem X n] : IsLinearMap K by
  constructor <;> (intros; ext i; simp[vector_to_spec])

def_fun_prop VectorType.fromVec in f [InjectiveGetElem X n] : Continuous by
  have h : (fun x => VectorType.fromVec (X:=X) x) = fun f =>ₗ[K] VectorType.fromVec f := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional

def_fun_prop VectorType.fromVec in f [InjectiveGetElem X n] : IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

#generate_linear_map_simps VectorType.Dense.fromVec.arg_f.IsLinearMap_rule


-- fderiv
abbrev_fun_trans VectorType.fromVec in f [InjectiveGetElem X n] : fderiv K by
  fun_trans

abbrev_data_synth VectorType.fromVec in f [InjectiveGetElem X n] (f₀) : (HasFDerivAt (𝕜:=K) · · f₀) by
  exact hasFDerivAt_from_isContinuousLinearMap

-- forward AD
abbrev_fun_trans VectorType.fromVec in f [InjectiveGetElem X n] : fwdFDeriv K by
  fun_trans

-- adjoint
open Classical in
abbrev_fun_trans VectorType.fromVec in f [InjectiveGetElem X n] : adjoint K by
  equals (fun x (i : n) => x[i]) =>
    funext f
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, Finset.sum_ite, Finset.filter_eq,Inner.inner,sum_to_finset_sum]

abbrev_data_synth VectorType.fromVec in f [InjectiveGetElem X n] : HasAdjoint K by
  conv => enter [3]; assign (fun (x : X) (i : n) => x[i])
  constructor
  case adjoint => intros; simp[vector_to_spec, Inner.inner,sum_to_finset_sum]
  case is_linear => fun_prop

abbrev_data_synth VectorType.fromVec in f [InjectiveGetElem X n] : HasAdjointUpdate K by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; rfl

-- reverse AD
abbrev_fun_trans VectorType.fromVec in f [InjectiveGetElem X n] : revFDeriv K by
  unfold revFDeriv
  autodiff

abbrev_data_synth VectorType.fromVec in f [InjectiveGetElem X n] : HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl
