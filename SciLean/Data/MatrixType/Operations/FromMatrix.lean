import SciLean.Data.MatrixType.Operations.ToMatrix

namespace SciLean

open MatrixType

def_fun_prop fromMatrix in f [InjectiveGetElem M (m×n)] : IsLinearMap K by
  constructor <;>
  (intros; ext i;
   simp[vector_to_spec])


def_fun_prop fromMatrix in f [InjectiveGetElem M (m×n)] : Continuous by
  have h : (fun x => fromMatrix (M:=M) x) = fun f =>ₗ[K] fromMatrix f := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional


def_fun_prop fromMatrix in f [InjectiveGetElem M (m×n)] : IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop


#generate_linear_map_simps MatrixType.Dense.fromMatrix.arg_f.IsLinearMap_rule

-- fderiv
abbrev_fun_trans fromMatrix in f [InjectiveGetElem M (m×n)] : fderiv K by
  fun_trans

abbrev_data_synth fromMatrix in f [InjectiveGetElem M (m×n)] (f₀) : (HasFDerivAt (𝕜:=K) · · f₀) by
  apply hasFDerivAt_from_fderiv
  case deriv => conv => rhs; fun_trans
  case diff => dsimp [autoParam]; fun_prop

-- forward AD
abbrev_fun_trans fromMatrix in f [InjectiveGetElem M (m×n)] : fwdFDeriv K by
  fun_trans

-- adjoint
open Classical in
abbrev_fun_trans fromMatrix in f [IdxType.Fold' n] [IdxType.Fold' m] [InjectiveGetElem M (m×n)] : adjoint K by
  equals (fun x => toMatrix x) =>
    funext f
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec,
         Finset.sum_ite, Finset.filter_eq,Inner.inner,IdxType.sum_eq_finset_sum,
         ←Finset.univ_product_univ, Finset.sum_product]

abbrev_data_synth fromMatrix in f [IdxType.Fold' n] [IdxType.Fold' m] [InjectiveGetElem M (m×n)] : HasAdjoint K by
   conv => enter[3]; assign (fun A : M => toMatrix A)
   constructor
   case adjoint =>
     intros; simp[vector_to_spec,IdxType.sum_eq_finset_sum,Inner.inner,
                  ←Finset.univ_product_univ, Finset.sum_product]
   case is_linear => fun_prop

abbrev_data_synth fromMatrix in f [IdxType.Fold' n] [IdxType.Fold' m] [InjectiveGetElem M (m×n)] : HasAdjointUpdate K by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; rfl

-- reverse AD
abbrev_fun_trans fromMatrix in f [IdxType.Fold' n] [IdxType.Fold' m] [InjectiveGetElem M (m×n)] : revFDeriv K by
  unfold revFDeriv
  autodiff

abbrev_data_synth fromMatrix in f [IdxType.Fold' n] [IdxType.Fold' m] [InjectiveGetElem M (m×n)] : HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl

abbrev_data_synth fromMatrix in f [IdxType.Fold' n] [IdxType.Fold' m] [InjectiveGetElem M (m×n)] : HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl
