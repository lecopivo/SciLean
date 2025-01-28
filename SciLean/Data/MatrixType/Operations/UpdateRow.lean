import SciLean.Data.MatrixType.Operations.ToMatrix
import SciLean.Data.VectorType.Operations.Scal
import SciLean.Data.VectorType.Optimize
import SciLean.Data.MatrixType.Optimize

namespace SciLean

open MatrixType Classical

def_fun_prop MatrixType.updateRow in A x [VectorType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] : IsLinearMap K by
  constructor <;>
  (intros; ext i; simp[vector_to_spec,Matrix.updateRow,Function.update]; split_ifs <;> simp)

#exit

def_fun_prop MatrixType.updateRow in A [VectorType.Lawful M] [VectorType.Lawful X] : Continuous by
  have h : (fun x => MatrixType.updateRow (M:=M) (X:=X) (Y:=Y) x i) = fun x =>ₗ[K] MatrixType.updateRow x i := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional

def_fun_prop MatrixType.updateRow in A with_transitive [VectorType.Lawful M] [VectorType.Lawful X] : IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

-- fderiv
abbrev_fun_trans MatrixType.updateRow in A [VectorType.Lawful M] [VectorType.Lawful X] : fderiv K by
  autodiff

abbrev_data_synth updateRow in A [VectorType.Lawful M] [VectorType.Lawful X] (A₀) : (HasFDerivAt (𝕜:=K) · · A₀) by
  apply hasFDerivAt_from_isContinuousLinearMap (by fun_prop)

-- forward AD
abbrev_fun_trans MatrixType.updateRow in A [VectorType.Lawful M] [VectorType.Lawful X] : fwdFDeriv K by
  autodiff

-- adjoint
abbrev_fun_trans MatrixType.updateRow in A [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful X] : adjoint K by
  equals (fun r => MatrixType.Dense.updateUpdateRow 0 i r) =>
    funext x
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec]
    sorry_proof

abbrev_data_synth updateRow in A [VectorType.Lawful M] [Dense M] [VectorType.Lawful X] : HasAdjoint K by
  conv => enter[3]; assign (fun r => updateUpdateRow (0:M) i r)
  constructor
  case adjoint => intros; simp[vector_to_spec]; sorry_proof
  case is_linear => fun_prop

abbrev_data_synth updateRow in A [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful X] : HasAdjointUpdate K by
  conv => enter[3]; assign (fun r (A : M) => let ri := updateRow A i; updateUpdateRow A i (ri + r))
  constructor
  case adjoint => intros; simp[vector_to_spec]; sorry_proof
  case is_linear => fun_prop

-- reverse AD
abbrev_fun_trans MatrixType.updateRow in A [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful X] : revFDeriv K by
  unfold revFDeriv
  autodiff

abbrev_data_synth updateRow in A [VectorType.Lawful M] [Dense M] [VectorType.Lawful X] : HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl

abbrev_data_synth updateRow in A [VectorType.Lawful M] [Dense M] [VectorType.Lawful X] : HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl


#exit
attribute [local instance] MatrixType.vectorTypeLawful

def_rev_deriv MatrixType.updateRow in A
    [MatrixType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful X] [DecidableEq m] by
  constructor
  · intro A
    conv => rhs; autodiff; simp -zeta [vector_optimize]
  · fun_prop
