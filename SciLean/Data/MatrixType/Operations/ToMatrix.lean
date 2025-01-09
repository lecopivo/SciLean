import SciLean.Data.VectorType.Base
import SciLean.Data.MatrixType.Base
import SciLean.Data.MatrixType.Dense
import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
import SciLean.Analysis.Matrix

import SciLean.Meta.GenerateFunTrans

namespace SciLean

def_fun_prop MatrixType.toMatrix in A [VectorType.Lawful M] : IsLinearMap K by
  constructor <;> (intros; simp[vector_to_spec,matrix_to_spec])

def_fun_prop MatrixType.toMatrix in A
    add_suffix _real
    [ScalarSMul R K] [VectorType.Lawful M] :
    IsLinearMap R by
  apply IsLinearMap.restrictScalars (S:=K)
  fun_prop

def_fun_prop MatrixType.toMatrix in A [VectorType.Lawful M] : Continuous by
  rename_i i _
  have h : (fun x => MatrixType.toMatrix (M:=M) (X:=X) (Y:=Y) x) = fun x =>ₗ[K] MatrixType.toMatrix x := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional

def_fun_prop MatrixType.toMatrix in A [VectorType.Lawful M] : IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

def_fun_prop MatrixType.toMatrix in A
    add_suffix _real
    [ScalarSMul R K] [VectorType.Lawful M] :
    IsContinuousLinearMap R by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

#generate_linear_map_simps MatrixType.Base.toMatrix.arg_A.IsLinearMap_rule

abbrev_fun_trans MatrixType.toMatrix in A [VectorType.Lawful M] : fderiv K by
  fun_trans

abbrev_fun_trans MatrixType.toMatrix in A
    add_suffix _real [ScalarSMul R K] [VectorType.Lawful M] : fderiv R by
  fun_trans

abbrev_fun_trans MatrixType.toMatrix in A [VectorType.Lawful M] : fwdFDeriv K by
  fun_trans

abbrev_fun_trans MatrixType.toMatrix in A
    add_suffix _real [ScalarSMul R K] [VectorType.Lawful M] : fwdFDeriv R by
  fun_trans


-- open Classical in
-- abbrev_fun_trans MatrixType.toMatrix in A [VectorType.Lawful M] [MatrixType.Dense M] : adjoint K by
--   equals (fun A => MatrixType.fromMatrix A) => -- todo: add specific definition for canonical basis: `VectorType.set 0 i 1`
--     funext x
--     apply AdjointSpace.ext_inner_left K
--     intro z
--     rw[← adjoint_ex _ (by fun_prop)]
--     simp[matrix_to_spec, vector_to_spec,
--          ←Finset.univ_product_univ,Finset.sum_product,
--          MatrixType.toVec_eq_toMatrix]
--     rfl

-- abbrev_fun_trans MatrixType.toMatrix in A [VectorType.Lawful M] [MatrixType.Dense M] : revFDeriv K by
--   unfold revFDeriv
--   autodiff



section HasRevFDerivUpdate

variable
  {m n : Type} {_ : IndexType m} {_ : IndexType n}
  {R K : Type} {_ : RealScalar R} {_ : Scalar R K}
  {X Y : Type} {_ : VectorType.Base X n K} {_ : VectorType.Base Y m K}
  [MatrixType.Base M X Y] [MatrixType.Lawful M] [MatrixType.Dense M]


@[fun_trans]
theorem MatrixType.Base.toMatrix.arg_x.adjoint_rule_apply [DecidableEq m] [DecidableEq n] (i : m) (j : n) :
    adjoint K (fun A => (MatrixType.toMatrix A i j))
    =
    fun c =>
      MatrixType.fromMatrix (M:=M) (fun i' j' => if i = i' ∧ j = j' then c else 0) := by
  funext x
  apply AdjointSpace.ext_inner_left K
  intro z
  rw[← adjoint_ex _ (by fun_prop)]
  simp[matrix_to_spec, vector_to_spec,
       ←Finset.univ_product_univ,Finset.sum_product,
       MatrixType.toVec_eq_toMatrix]
  sorry_proof


@[fun_trans]
theorem MatrixType.Base.toMatrix.arg_x.revFDeriv_rule_apply [DecidableEq m] [DecidableEq n] (i : m) (j : n) :
    revFDeriv K (fun A => (MatrixType.toMatrix A i j))
    =
    fun A =>
      (MatrixType.toMatrix A i j,
       fun dc =>
         MatrixType.fromMatrix (M:=M) (fun i' j' => if i = i' ∧ j = j' then dc else 0)) := by
  unfold revFDeriv
  fun_trans


@[data_synth]
theorem MatrixType.Base.toMatrix.arg_x.HasRevFDerivUpdate_rule_apply [DecidableEq m] [DecidableEq n] (i : m) (j : n):
    HasRevFDerivUpdate K
      (MatrixType.toMatrix (M:=M) · i j)
      (fun A => (MatrixType.toMatrix A i j,
        fun dk dA =>
           MatrixType.updateElem dA i j (fun aij => aij + dk))) := by
  constructor
  · fun_trans
    funext dc dA
    apply MatrixType.toMatrix_injective
    simp[updateElem, matrix_to_spec]
    sorry_proof
  · fun_prop
