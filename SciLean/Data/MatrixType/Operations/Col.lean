import SciLean.Data.MatrixType.Operations.ToMatrix
import SciLean.Tactic.DataSynth.DefRevDeriv
import SciLean.Data.VectorType.Operations.Scal
import SciLean.Data.VectorType.Optimize
import SciLean.Data.MatrixType.Optimize

namespace SciLean

def_fun_prop MatrixType.col in A [VectorType.Lawful M] [VectorType.Lawful Y] : IsLinearMap K by
  constructor <;> (intros; ext i; simp[vector_to_spec,matrix_to_spec])


def_fun_prop MatrixType.col in A [VectorType.Lawful M] [VectorType.Lawful Y] : Continuous by
  have h : (fun x => MatrixType.col (M:=M) (X:=X) (Y:=Y) x j) = fun x =>ₗ[K] MatrixType.col x j := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional


def_fun_prop MatrixType.col in A with_transitive [VectorType.Lawful M] [VectorType.Lawful Y] : IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop


abbrev_fun_trans MatrixType.col in A [VectorType.Lawful M] [VectorType.Lawful Y] : fderiv K by
  autodiff

abbrev_fun_trans MatrixType.col in A [VectorType.Lawful M] [VectorType.Lawful Y] : fwdFDeriv K by
  autodiff

abbrev_fun_trans MatrixType.col in A [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful Y] : adjoint K by
  equals (fun r => MatrixType.Dense.updateCol 0 j r) =>
    funext x
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec, matrix_to_spec, MatrixType.toVec_eq_toMatrix]
    sorry_proof

abbrev_fun_trans MatrixType.col in A [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful Y] : revFDeriv K by
  unfold revFDeriv
  autodiff

attribute [local instance] MatrixType.vectorTypeLawful

def_rev_deriv MatrixType.col in A
    [MatrixType.Lawful M] [VectorType.Lawful M] [MatrixType.Dense M] [VectorType.Lawful Y] [DecidableEq m] by
  constructor
  · intro A
    conv => rhs; autodiff; simp -zeta [vector_optimize]
  · fun_prop
