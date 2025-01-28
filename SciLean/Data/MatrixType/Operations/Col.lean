import SciLean.Data.MatrixType.Operations.ToMatrix
import SciLean.Data.VectorType.Operations.Scal
import SciLean.Data.VectorType.Optimize
import SciLean.Data.MatrixType.Optimize

namespace SciLean

open MatrixType

-- linear, continusous, differentiable
def_fun_prop col in A [VectorType.Lawful M] [VectorType.Lawful Y] : IsLinearMap K by
  constructor <;> (intros; ext j; simp[vector_to_spec,matrix_to_spec])

def_fun_prop col in A [VectorType.Lawful M] [VectorType.Lawful Y] : Continuous by
  have h : (fun x => MatrixType.col (M:=M) (X:=X) (Y:=Y) x j) = fun x =>ₗ[K] MatrixType.col x j := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional

def_fun_prop col in A with_transitive [VectorType.Lawful M] [VectorType.Lawful Y] : IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

-- fderiv
abbrev_fun_trans MatrixType.col in A [VectorType.Lawful M] [VectorType.Lawful Y] : fderiv K by
  autodiff

abbrev_data_synth col in A [VectorType.Lawful M] [VectorType.Lawful Y] (A₀) : (HasFDerivAt (𝕜:=K) · · A₀) by
  apply hasFDerivAt_from_isContinuousLinearMap (by fun_prop)

-- forward AD
abbrev_fun_trans MatrixType.col in A [VectorType.Lawful M] [VectorType.Lawful Y] : fwdFDeriv K by
  autodiff

-- adjoint
abbrev_fun_trans MatrixType.col in A [VectorType.Lawful M] [Dense M] [VectorType.Lawful Y] : adjoint K by
  equals (fun r => MatrixType.Dense.updateCol 0 j r) =>
    funext x
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec]
    sorry_proof

abbrev_data_synth col in A [VectorType.Lawful M] [Dense M] [VectorType.Lawful Y] : HasAdjoint K by
  conv => enter[3]; assign (fun r => updateCol (0:M) j r)
  constructor
  case adjoint => intros; simp[vector_to_spec]; sorry_proof
  case is_linear => fun_prop

abbrev_data_synth col in A [VectorType.Lawful M] [Dense M] [VectorType.Lawful Y] : HasAdjointUpdate K by
  conv => enter[3]; assign (fun c (A : M) => let cj := col A j; updateCol A j (cj + c))
  constructor
  case adjoint => intros; simp[vector_to_spec]; sorry_proof
  case is_linear => fun_prop

-- reverse AD
abbrev_fun_trans MatrixType.col in A [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful Y] : revFDeriv K by
  unfold revFDeriv
  autodiff

abbrev_data_synth col in A [VectorType.Lawful M] [Dense M] [VectorType.Lawful Y] : HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl

abbrev_data_synth col in A [VectorType.Lawful M] [Dense M] [VectorType.Lawful Y] : HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl
