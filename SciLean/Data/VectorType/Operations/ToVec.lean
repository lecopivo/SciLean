import SciLean.Data.VectorType.Base
import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
import SciLean.Tactic.DataSynth.DefRevDeriv
import SciLean.Meta.GenerateFunTrans

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
    simp[vector_to_spec, Finset.sum_ite, Finset.filter_eq]


abbrev_fun_trans VectorType.toVec in x [VectorType.Lawful X] [VectorType.Dense X] : revFDeriv K by
  unfold revFDeriv
  autodiff

def_rev_deriv VectorType.toVec in x [VectorType.Lawful X] [VectorType.Dense X] by
  constructor
  · intros x
    conv => rhs; autodiff
  · fun_prop

def_rev_deriv' VectorType.toVec in x [VectorType.Lawful X] [VectorType.Dense X] by
  have hh : revFDeriv K x
         =
         fun w =>
           let' (y,dx) := x' w
           (y, (dx · 0)) := by simp[hx.1]; unfold revFDeriv; simp
  -- have q : ∀ w u dy dw, u + (x' w).2 dy dw = (x' w).2 dy (dw + u) := sorry
  have := hx.2
  constructor
  · intros x
    conv =>
      rhs
      autodiff
      -- lsimp -zeta [q]
  · fun_prop
