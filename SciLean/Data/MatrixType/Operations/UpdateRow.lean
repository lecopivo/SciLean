import SciLean.Data.MatrixType.Operations.ToMatrix
import SciLean.Data.VectorType.Operations.Scal
import SciLean.Data.VectorType.Optimize
import SciLean.Data.MatrixType.Optimize

namespace SciLean

open MatrixType Classical ComplexConjugate

def_fun_prop updateRow in A x
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] :
    IsLinearMap K by
  constructor <;>
  (intros; ext i; cases i; simp[vector_to_spec,Matrix.updateRow,Function.update]; split_ifs <;> simp)

def_fun_prop MatrixType.updateRow in A x
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] :
    Continuous by
  have h : (fun x : M×X => MatrixType.updateRow (M:=M) (X:=X) (Y:=Y) x.1 i x.2)
           =
           fun x =>ₗ[K] MatrixType.updateRow x.1 i x.2 := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional

def_fun_prop MatrixType.updateRow in A x with_transitive
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] :
    IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

-- fderiv
abbrev_fun_trans MatrixType.updateRow in A x
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] :
    fderiv K by
  autodiff

abbrev_data_synth updateRow in A x
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] (A₀) :
    (HasFDerivAt (𝕜:=K) · · A₀) by
  apply hasFDerivAt_from_isContinuousLinearMap (by fun_prop)

-- forward AD
abbrev_fun_trans MatrixType.updateRow in A x
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] :
    fwdFDeriv K by
  autodiff

-- adjoint
abbrev_fun_trans MatrixType.updateRow in A x
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] :
    adjoint K by
  equals (fun B : M => (updateRow B i 0, row B i)) =>
    funext x
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec]
    sorry_proof

abbrev_data_synth updateRow in A x
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] :
    HasAdjoint K by
  conv => enter[3]; assign (fun B : M => (updateRow B i 0, row B i))
  constructor
  case adjoint =>
    intros Ar B;
    simp[vector_to_spec,AdjointSpace.inner_prod_split, sum_to_finset_sum,
         ← Finset.univ_product_univ, Finset.sum_product,
         Matrix.updateRow, Function.update]
    conv =>
      rhs; enter[2]
      equals (∑ i' : m, ∑ x : n,
               if i'=i then conj (VectorType.toVec Ar.2 x) * VectorType.toVec B (i, x) else 0) =>
        simp [sum_to_finset_sum]
    simp only [←Finset.sum_add_distrib,sum_to_finset_sum]
    congr 1; funext i; congr 1; funext j
    split_ifs <;> simp_all;
  case is_linear => fun_prop

abbrev_data_synth updateRow in A x
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] :
    HasAdjointUpdate K by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => dsimp; data_synth
  case simp => intro B Ar; conv => rhs; simp[Prod.add_def]; to_ssa;  lsimp

-- reverse AD
abbrev_fun_trans MatrixType.updateRow in A x [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] : revFDeriv K by
  unfold revFDeriv
  autodiff

abbrev_data_synth updateRow in A x
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] :
    HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl

abbrev_data_synth updateRow in A x
    [InjectiveGetElem M (m×n)] [InjectiveGetElem X n] :
    HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl
