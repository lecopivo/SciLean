import SciLean.Data.VectorType.Operations.ToVec


namespace SciLean

open VectorType

--TODO: reformulate in terms of `setElem` and ditch `VectorType.set`

def_fun_prop VectorType.set in x v
    [InjectiveGetElem X n] :
    IsLinearMap K by
  constructor <;>
  (intros; ext j; simp[vector_to_spec,Function.update,VectorType.set]; try by_cases i=j <;> simp_all)

def_fun_prop VectorType.set in x v
    [InjectiveGetElem X n] :
    Continuous by
  have h : (fun x : X×K => VectorType.set (X:=X) x.1 i x.2)
           =
           fun x =>ₗ[K] VectorType.set x.1 i x.2 := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional


def_fun_prop VectorType.set in x v with_transitive
    [InjectiveGetElem X n] :
    IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop


-- fderiv
abbrev_fun_trans VectorType.set in x v
    [InjectiveGetElem X n] :
    fderiv K by
  autodiff

abbrev_data_synth VectorType.set in x v
    [InjectiveGetElem X n] (A₀) :
    (HasFDerivAt (𝕜:=K) · · A₀) by
  apply hasFDerivAt_from_isContinuousLinearMap (by fun_prop)

-- forward AD
abbrev_fun_trans VectorType.set in x v
    [InjectiveGetElem X n] :
    fwdFDeriv K by
  autodiff

-- adjoint
abbrev_fun_trans VectorType.set in x v
    [InjectiveGetElem X n] :
    adjoint K by
  equals (fun y : X =>
      let xi := toVec y i
      let y := VectorType.set y i 0
      (y, xi)) =>
    funext x
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec]
    sorry_proof

abbrev_data_synth VectorType.set in x v
    [InjectiveGetElem X n] :
    HasAdjoint K by
  conv => enter[3]; assign (fun y : X =>
    let xi := toVec y i
    let y := VectorType.set y i 0
    (y, xi))
  constructor
  case adjoint =>
    intros Ar B;
    simp[vector_to_spec,AdjointSpace.inner_prod_split, sum_to_finset_sum,
         ← Finset.univ_product_univ, Finset.sum_product,
         VectorType.set, Function.update]
    sorry_proof
  case is_linear => fun_prop

abbrev_data_synth VectorType.set in x v
    [InjectiveGetElem X n] :
    HasAdjointUpdate K by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intro B Ar; conv => rhs; lsimp [Prod.add_def]

-- reverse AD
abbrev_fun_trans VectorType.set in x v [InjectiveGetElem X n] : revFDeriv K by
  unfold revFDeriv
  autodiff

abbrev_data_synth VectorType.set in x v
    [InjectiveGetElem X n] :
    HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => lsimp; rfl

abbrev_data_synth VectorType.set in x v
    [InjectiveGetElem X n] :
    HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => lsimp; rfl
