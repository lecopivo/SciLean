module

public import SciLean.Data.DataArray.Operations.Curry
public import SciLean.Data.ArrayOperations.Operations.GetElem

@[expose] public section



namespace SciLean.DataArrayN



data_array_fun_prop uncurry X R in x : IsLinearMap R by
  have hc : IsLinearMap R (fun x : X^[I,J] => x.curry) := by fun_prop
  have h1 : ∀ x : X^[J]^[I], x.uncurry.curry = x := by simp [curry, uncurry]
  have h2 : ∀ x : X^[I,J], x.curry.uncurry = x := by simp [curry, uncurry]
  constructor
  · intro x y; rw [← h2 (_ + _), hc.map_add, h1, h1]
  · intro r x; rw [← h2 (_ • _), hc.map_smul, h1]
data_array_fun_prop uncurry X R in x : Continuous by sorry_proof
data_array_fun_prop uncurry X R in x : IsContinuousLinearMap R by constructor <;> fun_prop
data_array_fun_prop uncurry X R in x : Differentiable R by fun_prop


data_array_data_synth_abbrev uncurry X R in x (x₀) : (HasFDerivAt (𝕜:=R) · · x₀) by
  apply hasFDerivAt_from_isContinuousLinearMap
  fun_prop

data_array_data_synth_abbrev uncurry X R in x : HasFwdFDeriv R by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp; rfl

data_array_data_synth_abbrev uncurry X R in x : HasAdjoint R by
  conv => enter[3]; assign (fun x : X^[I,J] => x.curry)
  constructor
  case adjoint =>
    intro x y
    have h : HasAdjoint R (fun x : X^[I,J] => x.curry) (fun y => y.uncurry) := by data_synth
    rw [← AdjointSpace.conj_symm, ← h.adjoint, AdjointSpace.conj_symm]
  case is_linear => fun_prop

data_array_data_synth_abbrev uncurry X R in x : HasAdjointUpdate R by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; rfl

data_array_data_synth_abbrev uncurry X R in x : HasRevFDeriv R by
  apply (hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df' := fun (_ : X^[J]^[I]) (dy : X^[I,J]) => dy.curry))
  case deriv => intros; data_synth
  case adjoint =>
    intro _
    change HasAdjoint R (fun dx : X^[J]^[I] => dx.uncurry) (fun dy : X^[I,J] => dy.curry)
    data_synth
  case simp => rfl

data_array_data_synth_abbrev uncurry X R in x : HasRevFDerivUpdate R by
  apply (hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
    (df' := fun (_ : X^[J]^[I]) (dy : X^[I,J]) (dx : X^[J]^[I]) => dx + dy.curry))
  case deriv => intros; data_synth
  case adjoint =>
    intro _
    change HasAdjointUpdate R (fun dx : X^[J]^[I] => dx.uncurry)
      (fun dy : X^[I,J] => fun dx : X^[J]^[I] => dx + dy.curry)
    data_synth
  case simp => rfl
