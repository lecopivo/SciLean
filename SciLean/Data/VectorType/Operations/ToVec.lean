import SciLean.Data.VectorType.Base
import SciLean.Data.VectorType.BaseSimps
import SciLean.Data.VectorType.Optimize
import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Analysis.AdjointSpace.HasAdjoint
import SciLean.Analysis.Calculus.HasRevFDeriv
-- import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
import SciLean.Tactic.DFunLikeCoeZetaDelta
import SciLean.Meta.GenerateFunTrans
import SciLean.Tactic.ConvAssign
import SciLean.Lean.ToSSA
import SciLean.Data.ArrayOperations.Operations.GetElem

namespace SciLean

namespace VectorType

-- def_fun_prop toVec in x [Lawful X] : IsLinearMap K by
--   constructor <;> (intros; simp[vector_to_spec])

variable {R : Type u} {K : Type v} [RealScalar R] [Scalar R K] {n : Type w} {nn} [IdxType n nn] {X}
  [VectorType.Base X n K] [InjectiveGetElem X n]

@[fun_prop]
theorem getElem.arg_xs.IsLinearMap_rule (i : n) :
    IsLinearMap K (fun x : X => x[i]) := by fun_prop
  -- constructor <;> (intros; simp[vector_to_spec])

#generate_linear_map_simps getElem.arg_xs.IsLinearMap_rule

@[fun_prop]
theorem getElem.arg_xs.IsLinearMap_rule_real
    [ScalarSMul R K] [ScalarInner R K] [RealOp X] (i : n) :
    IsLinearMap R (fun x : X => x[i]) := by fun_prop
  -- constructor <;> (intros; simp[vector_to_spec])

#generate_linear_map_simps getElem.arg_xs.IsLinearMap_rule_real

@[fun_prop]
theorem getElem.arg_xs.Continuous_rule (i : n) :
    Continuous (fun x : X => x[i]) := by fun_prop

@[fun_prop]
theorem getElem.arg_xs.IsContinuousLinearMap_rule (i : n) :
    IsContinuousLinearMap K (fun x : X => x[i]) := by fun_prop

@[fun_prop]
theorem getElem.arg_xs.IsContinuousLinearMap_rule_real
    [ScalarSMul R K] [ScalarInner R K] [RealOp X] (i : n) :
    IsContinuousLinearMap R (fun x : X => x[i]) := by fun_prop
  -- constructor
  -- · fun_prop
  -- · dsimp only [autoParam]; fun_prop

-- fderiv
theorem getElem_fderiv
    {W} [NormedAddCommGroup W] [NormedSpace K W]
    (f : W → X) (hf : Differentiable K f) (w dw : W) (i : n) :
    (fderiv K f w dw)[i]
    =
    fderiv K (fun w => (f w)[i]) w dw := by
  fun_trans

@[fun_trans]
theorem getElem.arg_xs.fderiv_rule (i : n) :
    fderiv K (fun x : X => x[i])
    =
    fun x => fun dx =>L[K] dx[i] := by
  fun_trans

@[fun_trans]
theorem getElem.arg_xs.fderiv_rule_real [ScalarSMul R K] [ScalarInner R K] [RealOp X] (i : n) :
    fderiv R (fun x : X => x[i])
    =
    fun x => fun dx =>L[R] dx[i] := by
  fun_trans

@[data_synth]
theorem getElem.arg_xs.HasFDerivAt_rule (i : n) (x : X) :
    HasFDerivAt (fun x : X => x[i]) (fun dx =>L[K] dx[i]) x := by
  data_synth

-- forward AD
@[fun_trans]
theorem getElem.arg_xs.fwdFDeriv_rule (i : n) :
    fwdFDeriv K (fun x : X => x[i])
    =
    fun x dx => (x[i],dx[i]) := by
  fun_trans


-- adjoint
@[fun_trans]
theorem getElem.arg_xs.adjoint_rule [Dense X] (i : n) :
    adjoint K (fun x : X => x[i])
    =
    fun k : K => setElem (0 : X) i k (by dsimp) := by
  funext x
  apply AdjointSpace.ext_inner_left K
  intro z
  rw[← adjoint_ex _ (by fun_prop)]
  simp[vector_to_spec,Finset.sum_ite_eq']
  sorry_proof

set_option pp.universes true
@[data_synth]
theorem getElem.arg_xs.HasAdjoint_rule [IdxType.Fold'.{_,v} n] [Dense X] (i : n) :
    HasAdjoint K (fun x : X => x[i])
     (fun k : K => setElem (0 : X) i k (by dsimp)) := by
  data_synth
  -- constructor
  -- case adjoint => intro z x; simp[vector_to_spec]; sorry_proof
  -- case is_linear => fun_prop

@[data_synth]
theorem getElem.arg_xs.HasAdjointUpdate_rule [IdxType.Fold'.{_,v} n] [Dense X] (i : n) :
    HasAdjointUpdate K (fun x : X => x[i])
     (fun (k : K) x => setElem x i (x[i] + k) (by dsimp)) := by
  data_synth


-- reverse AD
@[fun_trans]
theorem getElem.arg_xs.revFDeriv_rule [Dense X] (i : n) :
    revFDeriv K (fun x : X => x[i])
    =
    fun x => (x[i], fun k : K => setElem (0 : X) i k (by dsimp)) := by
  unfold revFDeriv
  fun_trans

@[data_synth]
theorem getElem.arg_xs.HasRevFDeriv_rule [IdxType.Fold'.{_,v} n] [Dense X] (i : n) :
    HasRevFDeriv K (fun x : X => x[i])
     (fun x => (x[i], fun k : K => setElem (0 : X) i k (by dsimp))) := by
  data_synth

@[data_synth]
theorem getElem.arg_xs.HasRevFDerivUpdate_rule [IdxType.Fold'.{_,v} n] [Dense X] (i : n) :
    HasRevFDerivUpdate K (fun x : X => x[i])
     (fun x => (x[i], fun (k : K) x' =>
       let xi := x'[i]
       setElem x' i (xi + k) (by dsimp))) := by
  data_synth
