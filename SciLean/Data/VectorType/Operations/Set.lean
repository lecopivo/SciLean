import SciLean.Data.VectorType.Operations.ToVec


namespace SciLean

open VectorType
#exit
def_fun_prop VectorType.set in x v
    [VectorType.Lawful X] :
    IsLinearMap K by
  constructor <;>
  (intros; ext i; simp[vector_to_spec,Function.update]; try split_ifs <;> simp)


def_fun_prop VectorType.set in x v
    [VectorType.Lawful X] :
    Continuous by
  have h : (fun x : X×K => VectorType.set (X:=X) x.1 i x.2)
           =
           fun x =>ₗ[K] VectorType.set x.1 i x.2 := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional


def_fun_prop VectorType.set in x v with_transitive
    [VectorType.Lawful X] :
    IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop


-- fderiv
abbrev_fun_trans VectorType.set in x v
    [VectorType.Lawful X] :
    fderiv K by
  autodiff

abbrev_data_synth VectorType.set in x v
    [VectorType.Lawful X] (A₀) :
    (HasFDerivAt (𝕜:=K) · · A₀) by
  apply hasFDerivAt_from_isContinuousLinearMap (by fun_prop)

-- forward AD
abbrev_fun_trans VectorType.set in x v
    [VectorType.Lawful X] :
    fwdFDeriv K by
  autodiff

-- adjoint
abbrev_fun_trans VectorType.set in x v
    [VectorType.Lawful X] :
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
    [VectorType.Lawful X] :
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

-- TODO: the result is not ideal w.r.t. memory management!!! we should first extract en element and
--       only then set the elemen to zero
abbrev_data_synth VectorType.set in x v
    [VectorType.Lawful X] :
    HasAdjointUpdate K by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intro B Ar; conv => rhs; simp [Prod.add_def]; to_ssa; lsimp

-- reverse AD
abbrev_fun_trans VectorType.set in x v [VectorType.Lawful X] : revFDeriv K by
  unfold revFDeriv
  autodiff

abbrev_data_synth VectorType.set in x v
    [VectorType.Lawful X] :
    HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => lsimp; rfl

abbrev_data_synth VectorType.set in x v
    [VectorType.Lawful X] :
    HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => lsimp; rfl
