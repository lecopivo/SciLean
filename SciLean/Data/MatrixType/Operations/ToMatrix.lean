import SciLean.Data.MatrixType.Base
import SciLean.Data.MatrixType.Dense
import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.Calculus.HasRevFDeriv
import SciLean.Analysis.Matrix
import SciLean.Tactic.ConvAssign

import SciLean.Meta.GenerateFunTrans

namespace SciLean

open MatrixType

-- linear, continuous, differentiable
def_fun_prop toMatrix in A [VectorType.Lawful M] : IsLinearMap K by
  constructor <;> (intros; simp[vector_to_spec]; rfl)

def_fun_prop toMatrix in A
    add_suffix _real
    [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful M] [VectorType.RealOp M] :
    IsLinearMap R by
  apply IsLinearMap.restrictScalars (S:=K)
  fun_prop

def_fun_prop toMatrix in A [VectorType.Lawful M] : Continuous by
  rename_i i _
  have h : (fun x => toMatrix (M:=M) (X:=X) (Y:=Y) x) = fun x =>ₗ[K] toMatrix x := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional

def_fun_prop toMatrix in A [VectorType.Lawful M] : IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

def_fun_prop toMatrix in A
    add_suffix _real
    [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful M] [VectorType.RealOp M] :
    IsContinuousLinearMap R by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

#generate_linear_map_simps Base.toMatrix.arg_A.IsLinearMap_rule

-- fderiv
abbrev_fun_trans toMatrix in A [VectorType.Lawful M] : fderiv K by
  fun_trans

abbrev_fun_trans toMatrix in A
    add_suffix _real [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful M] [VectorType.RealOp M] : fderiv R by
  fun_trans

abbrev_data_synth toMatrix in A [VectorType.Lawful M] (A₀) : (HasFDerivAt (𝕜:=K) · · A₀) by
  apply hasFDerivAt_from_fderiv
  case deriv => conv => rhs; fun_trans
  case diff => dsimp [autoParam]; fun_prop

-- forward AD
abbrev_fun_trans toMatrix in A [VectorType.Lawful M] : fwdFDeriv K by
  fun_trans

abbrev_fun_trans toMatrix in A
    add_suffix _real [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful M] [VectorType.RealOp M] : fwdFDeriv R by
  fun_trans

-- adjoint
abbrev_data_synth toMatrix in A [VectorType.Lawful M] [Dense M] : HasAdjoint K by
  conv => enter[3]; assign (fun f => fromMatrix (M:=M) f)
  constructor
  case adjoint =>
    intros; simp[vector_to_spec,Inner.inner,sum_to_finset_sum,
                 ←Finset.univ_product_univ,Finset.sum_product]
  case is_linear => fun_prop

abbrev_data_synth toMatrix in A [VectorType.Lawful M] [Dense M] : HasAdjointUpdate K by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; rfl

-- reverse AD
abbrev_data_synth toMatrix in A [VectorType.Lawful M] [Dense M] : HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl

abbrev_data_synth toMatrix in A [VectorType.Lawful M] [Dense M] : HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl

@[data_synth]
theorem MatrixType.Base.toMatrix.arg_A.HasRevFDeriv_simple_rule_ij {M : Type u_1} {m : outParam (Type u_2)}
    {n : outParam (Type u_3)} {inst : IndexType m} {_ : IndexType n} {R : outParam (Type u_4)}
    {K : outParam (Type u_5)} {_ : RealScalar R} {_ : Scalar R K} {X : outParam (Type u_6)}
    {Y : outParam (Type u_7)} {_ : VectorType.Base X n K} {_ : VectorType.Base Y m K} [self : Base M X Y]
    [VectorType.Lawful M] [Dense M]
    (i : m) (j : n) :
    HasRevFDeriv K
      (fun A : M => toMatrix A i j)
      (fun A => (toMatrix A i j, fun dk => MatrixType.set' (0:M) i j dk)) := by
  sorry_proof

@[data_synth]
theorem MatrixType.Base.toMatrix.arg_A.HasRevFDerivUpdate_simple_rule_ij
    {M : Type u_1} {m : outParam (Type u_2)}
    {n : outParam (Type u_3)} {inst : IndexType m} {_ : IndexType n} {R : outParam (Type u_4)}
    {K : outParam (Type u_5)} {_ : RealScalar R} {_ : Scalar R K} {X : outParam (Type u_6)}
    {Y : outParam (Type u_7)} {_ : VectorType.Base X n K} {_ : VectorType.Base Y m K} [self : Base M X Y]
    [VectorType.Lawful M] [Dense M]
    (i : m) (j : n) :
    HasRevFDerivUpdate K
      (fun A : M => toMatrix A i j)
      (fun A => (toMatrix A i j, fun dk A' => MatrixType.updateElem A' i j (·+dk))) := by
  sorry_proof
