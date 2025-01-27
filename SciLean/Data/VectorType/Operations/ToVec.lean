import SciLean.Data.VectorType.Base
import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.AdjointSpace.HasAdjoint
import SciLean.Analysis.Calculus.HasRevFDeriv
-- import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
-- import SciLean.Tactic.DataSynth.DefRevDeriv
import SciLean.Meta.GenerateFunTrans
import SciLean.Tactic.ConvAssign

namespace SciLean

def_fun_prop VectorType.toVec in x [VectorType.Lawful X] : IsLinearMap K by
  constructor <;> (intros; simp[vector_to_spec])

def_fun_prop VectorType.toVec in x
    add_suffix _real
    [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] :
    IsLinearMap R by
  apply IsLinearMap.restrictScalars (S:=K)
  fun_prop

def_fun_prop VectorType.toVec in x [VectorType.Lawful X] : Continuous by
  rename_i i _
  have h : (fun x => VectorType.toVec (X:=X) x i) = fun x =>ₗ[K] VectorType.toVec x i := rfl
  rw[h];
  apply LinearMap.continuous_of_finiteDimensional

def_fun_prop VectorType.Base.toVec in x [VectorType.Lawful X] : IsContinuousLinearMap K by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop

abbrev_data_synth VectorType.toVec in x [VectorType.Lawful X] (x₀ : X) :
    (HasFDerivAt (𝕜:=K) · · x₀) by
  exact hasFDerivAt_from_isContinuousLinearMap

theorem toVec_fderiv
    {R K} {_ : RealScalar R} {_ : Scalar R K}
    {n} {_ : IndexType n}
    {X} [VectorType.Base X n K] [VectorType.Lawful X]
    {W} [NormedAddCommGroup W] [NormedSpace K W]
    (f : W → X) (hf : Differentiable K f) (w dw : W) :
    VectorType.toVec (fderiv K f w dw)
    =
    fun i => fderiv K (fun w => VectorType.toVec (f w) i) w dw := by
  fun_trans

def_fun_prop VectorType.Base.toVec in x
    add_suffix _real
    [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] :
    IsContinuousLinearMap R by
  constructor
  · fun_prop
  · dsimp only [autoParam]; fun_prop


#generate_linear_map_simps VectorType.Base.toVec.arg_x.IsLinearMap_rule


abbrev_fun_trans VectorType.toVec in x [VectorType.Lawful X] : fderiv K by
  fun_trans

abbrev_fun_trans VectorType.toVec in x
    add_suffix _real [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] : fderiv R by
  fun_trans

abbrev_fun_trans VectorType.toVec in x [VectorType.Lawful X] : fwdFDeriv K by
  fun_trans

abbrev_fun_trans VectorType.toVec in x
    add_suffix _real
    [ScalarSMul R K] [ScalarInner R K] [VectorType.Lawful X] [VectorType.RealOp X] : fwdFDeriv R by
  fun_trans

open Classical in
abbrev_fun_trans VectorType.toVec in x [VectorType.Lawful X] [VectorType.Dense X] : adjoint K by
  tactic => rename_i i _ _
  equals (fun k => VectorType.set 0 i k) => -- todo: add specific definition for canonical basis: `VectorType.set 0 i 1`
    funext x
    apply AdjointSpace.ext_inner_left K
    intro z
    rw[← adjoint_ex _ (by fun_prop)]
    simp[vector_to_spec,Finset.sum_ite_eq']

open Classical in
abbrev_data_synth VectorType.toVec in x [VectorType.Lawful X] [VectorType.Dense X] :
    HasAdjoint K by
  conv => enter[3]; assign (fun k => VectorType.set (0:X) i k)
  constructor
  case adjoint => intro z x; simp[vector_to_spec]
  case is_linear => fun_prop

abbrev_data_synth VectorType.toVec in x [VectorType.Lawful X] [VectorType.Dense X] :
    HasAdjointUpdate K by
  conv => enter[3]; assign (fun k (x : X) => VectorType.updateElem x i (fun xi => xi + k))
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; simp

abbrev_fun_trans VectorType.toVec in x [VectorType.Lawful X] [VectorType.Dense X] : revFDeriv K by
  unfold revFDeriv
  autodiff

abbrev_data_synth VectorType.toVec in x [VectorType.Lawful X] [VectorType.Dense X] :
    HasRevFDeriv K by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl

abbrev_data_synth VectorType.toVec in x [VectorType.Lawful X] [VectorType.Dense X] :
    HasRevFDerivUpdate K by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl
