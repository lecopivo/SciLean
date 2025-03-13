import SciLean.Data.MatrixType.Operations.ToMatrix
import SciLean.Data.VectorType.Operations.Scal
import SciLean.Data.VectorType.Optimize
import SciLean.Data.MatrixType.Optimize

namespace SciLean

open MatrixType Classical ComplexConjugate

def_fun_prop updateCol in A y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem Y m] :
    IsLinearMap K by
  constructor <;>
  (intros; ext i; cases i; simp[vector_to_spec,Matrix.updateCol,Function.update]; try split_ifs <;> simp)

def_fun_prop MatrixType.updateCol in A y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem Y m] :
    Continuous by
  have h : (fun x : M×Y => MatrixType.updateCol (M:=M) (X:=X) (Y:=Y) x.1 j x.2)
           =
           fun x =>ₗ[K] MatrixType.updateCol x.1 j x.2 := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional

def_fun_prop MatrixType.updateCol in A y with_transitive
    [InjectiveGetElem M (m×n)] [InjectiveGetElem Y m] :
    IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

-- fderiv
abbrev_fun_trans MatrixType.updateCol in A y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem Y m] :
    fderiv K by
  autodiff

abbrev_data_synth updateCol in A y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem Y m] (A₀) :
    (HasFDerivAt (𝕜:=K) · · A₀) by
  apply hasFDerivAt_from_isContinuousLinearMap (by fun_prop)

-- forward AD
abbrev_fun_trans MatrixType.updateCol in A y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem Y m] :
    fwdFDeriv K by
  autodiff

-- adjoint
abbrev_fun_trans MatrixType.updateCol in A y
    [InjectiveGetElem M (m×n)] [InjectiveGetElem Y m] :
    adjoint K by
  equals (fun B : M => (updateCol B j 0, col B j)) =>
    funext x
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec]
    sorry_proof

abbrev_data_synth updateCol in A y
    [IdxType.Fold' m] [IdxType.Fold' n]
    [InjectiveGetElem M (m×n)] [InjectiveGetElem Y m] :
    HasAdjoint K by
  conv => enter[3]; assign (fun B : M => (updateCol B j 0, col B j))
  constructor
  case adjoint =>
    intros Ar B;
    simp[vector_to_spec,AdjointSpace.inner_prod_split, sum_to_finset_sum,
         ← Finset.univ_product_univ, Finset.sum_product,
         Matrix.updateCol, Function.update]
    conv =>
      rhs; enter[2]
      equals (∑ᴵ i' : m, ∑ᴵ j' : n,
               if j'=j then conj (Ar.2[i']) * B[(i', j')] else 0) =>
        simp [IdxType.sum_eq_finset_sum]
    simp only [←Finset.sum_add_distrib,IdxType.sum_eq_finset_sum]
    congr 1; funext i; congr 1; funext j
    split_ifs <;> simp_all;
  case is_linear => fun_prop

abbrev_data_synth updateCol in A y
    [IdxType.Fold' m] [IdxType.Fold' n]
    [InjectiveGetElem M (m×n)] [InjectiveGetElem Y m] :
    HasAdjointUpdate K by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => dsimp; data_synth
  case simp => intro B Ar; conv => rhs; simp[Prod.add_def]; to_ssa;  lsimp

-- reverse AD
abbrev_fun_trans MatrixType.updateCol in A y
    [IdxType.Fold' m] [IdxType.Fold' n]
    [InjectiveGetElem M (m×n)] [InjectiveGetElem Y m] :
    revFDeriv K by
  unfold revFDeriv
  autodiff

abbrev_data_synth updateCol in A y
    [IdxType.Fold' m] [IdxType.Fold' n]
    [InjectiveGetElem M (m×n)] [InjectiveGetElem Y m] :
    HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl

abbrev_data_synth updateCol in A y
    [IdxType.Fold' m] [IdxType.Fold' n]
    [InjectiveGetElem M (m×n)] [InjectiveGetElem Y m] :
    HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl
