import SciLean.Data.MatrixType.Operations.ToMatrix
import SciLean.Data.VectorType.Operations.Scal
import SciLean.Data.VectorType.Optimize
import SciLean.Data.MatrixType.Optimize

namespace SciLean

open MatrixType


-- linear, continusous, differentiable
def_fun_prop MatrixType.row in A [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] : IsLinearMap K by
  constructor <;> (intros; ext i; simp[vector_to_spec,matrix_to_spec])


def_fun_prop MatrixType.row in A [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] : Continuous by
  have h : (fun x => MatrixType.row (M:=M) (X:=X) (Y:=Y) x i) = fun x =>ₗ[K] MatrixType.row x i := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional

def_fun_prop MatrixType.row in A with_transitive [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] : IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

-- fderiv
abbrev_fun_trans MatrixType.row in A [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] : fderiv K by
  autodiff

abbrev_data_synth row in A [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] (A₀) : (HasFDerivAt (𝕜:=K) · · A₀) by
  apply hasFDerivAt_from_isContinuousLinearMap (by fun_prop)

-- forward AD
abbrev_fun_trans MatrixType.row in A [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] : fwdFDeriv K by
  autodiff

-- adjoint
abbrev_fun_trans MatrixType.row in A [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] : adjoint K by
  equals (fun r => MatrixType.Dense.updateRow 0 i r) =>
    funext x
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec]
    sorry_proof

abbrev_data_synth row in A [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] : HasAdjoint K by
  conv => enter[3]; assign (fun r => updateRow (0:M) i r)
  constructor
  case adjoint => intros; simp[vector_to_spec]; sorry_proof
  case is_linear => fun_prop

abbrev_data_synth row in A [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] : HasAdjointUpdate K by
  conv => enter[3]; assign (fun r (A : M) => let ri := row A i; updateRow A i (ri + r))
  constructor
  case adjoint => intros; simp[vector_to_spec]; sorry_proof
  case is_linear => fun_prop

-- reverse AD
abbrev_fun_trans MatrixType.row in A [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] : revFDeriv K by
  unfold revFDeriv
  autodiff

abbrev_data_synth row in A [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] : HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl

abbrev_data_synth row in A [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] : HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl
