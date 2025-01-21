import SciLean.Data.MatrixType.Operations.ToMatrix
import SciLean.Tactic.DataSynth.DefRevDeriv
import SciLean.Data.VectorType.Operations.Scal
import SciLean.Data.VectorType.Optimize
import SciLean.Data.MatrixType.Optimize

namespace SciLean

def_fun_prop MatrixType.row in A [VectorType.Lawful M] [VectorType.Lawful X] : IsLinearMap K by
  constructor <;> (intros; ext i; simp[vector_to_spec,matrix_to_spec])


def_fun_prop MatrixType.row in A [VectorType.Lawful M] [VectorType.Lawful X] : Continuous by
  have h : (fun x => MatrixType.row (M:=M) (X:=X) (Y:=Y) x i) = fun x =>ₗ[K] MatrixType.row x i := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional


def_fun_prop MatrixType.row in A with_transitive [VectorType.Lawful M] [VectorType.Lawful X] : IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop


abbrev_fun_trans MatrixType.row in A [VectorType.Lawful M] [VectorType.Lawful X] : fderiv K by
  autodiff

abbrev_fun_trans MatrixType.row in A [VectorType.Lawful M] [VectorType.Lawful X] : fwdFDeriv K by
  autodiff

abbrev_fun_trans MatrixType.row in A [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful X] : adjoint K by
  equals (fun r => MatrixType.Dense.updateRow 0 i r) =>
    funext x
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, matrix_to_spec, MatrixType.toVec_eq_toMatrix]
    sorry_proof

abbrev_fun_trans MatrixType.row in A [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful X] : revFDeriv K by
  unfold revFDeriv
  autodiff

def_rev_deriv MatrixType.row in A
    [MatrixType.Lawful M] [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful X] [DecidableEq m] by
  constructor
  · intro A
    conv => rhs; autodiff; simp -zeta [vector_optimize]
  · fun_prop
