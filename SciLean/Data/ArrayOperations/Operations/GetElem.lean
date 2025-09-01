import SciLean.Analysis.Calculus.HasFDeriv
import SciLean.Analysis.Calculus.HasRevFDeriv
import SciLean.Analysis.Calculus.HasFwdFDeriv
import SciLean.Data.ArrayOperations.Algebra
import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.IfPull

namespace SciLean

@[fun_prop]
theorem getElem.arg_xs.IsLinearMap_rule {𝕜 X I Y : Type*} [GetElem' X I Y]
    [Ring 𝕜] [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] (i : I) :
    IsLinearMap 𝕜 (fun x : X => x[i]) := by constructor <;> (intros; simp)

@[fun_prop]
theorem getElem.arg_xs.IsContinuousLinearMap_rule {𝕜 X I Y : Type*}
    [GetElem' X I Y] [Ring 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
    [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] (i : I) :
    IsContinuousLinearMap 𝕜 (fun x : X => x[i]) := by
  constructor; fun_prop; dsimp[autoParam]; fun_prop

@[data_synth]
theorem getElem.arg_xs.HasFDerivAt_rule {𝕜 X I Y : Type*}
    [GetElem' X I Y] [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] (i : I) (x₀ : X) :
    HasFDerivAt (fun x : X => x[i]) (fun dx : X =>L[𝕜] dx[i]) x₀ := by
  apply hasFDerivAt_from_isContinuousLinearMap

@[data_synth]
theorem getElem.arg_xs.HasFwdFDeriv_rule {𝕜 X I Y : Type*}
    [GetElem' X I Y] [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] (i : I) :
    HasFwdFDeriv 𝕜 (fun x : X => x[i]) (fun x dx => (x[i], dx[i])) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => simp

@[data_synth]
theorem getElem.arg_xs.HasAdjoint_rule_free_index {𝕜 X I Y : Type*}
    [GetElem' X I Y] [OfFn X I Y] [LawfulOfFn X I] {nI} [IndexType I nI] [Fold I] [RCLike 𝕜]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I] :
    HasAdjoint 𝕜
      (fun (x : X) (i : I) => x[i])
      (fun f =>
        let x := ofFn f
        x) := by
  constructor
  case adjoint => intro x f; simp[Inner.inner, inner_eq_sum_getElem (I:=I), IndexType.sum_eq_finset_sum]
  case is_linear => fun_prop

open Classical
@[data_synth]
theorem getElem.arg_xs.HasAdjoint_rule_applied_index {𝕜 X I Y : Type*}
    [GetElem' X I Y] [SetElem' X I Y] [LawfulSetElem X I]
    {nI} [IndexType I nI] [RCLike 𝕜]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I]  (i : I) :
    HasAdjoint 𝕜
      (fun (x : X) => x[i])
      (fun xi =>
        let x := setElem (0:X) i xi .intro
        x) := by
  constructor
  case adjoint => intro x y; simp[inner_eq_sum_getElem (I:=I),Tactic.if_pull,IndexType.sum_eq_finset_sum]
  case is_linear => fun_prop

@[data_synth]
theorem getElem.arg_xs.HasAdjointUpdate_rule_applied_index {𝕜 X I Y : Type*}
    [GetElem' X I Y] [InjectiveGetElem X I]
    [SetElem' X I Y] [LawfulSetElem X I]
    {nI} [IndexType I nI] [RCLike 𝕜]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I]  (i : I) :
    HasAdjointUpdate 𝕜
      (fun (x : X) => x[i])
      (fun xi' x =>
        let xi := x[i];
        let x :=setElem x i (xi + xi') .intro
        x) := by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp =>
    intros; simp
    apply getElem_injective (idx:=I); funext j
    by_cases (i=j) <;> simp_all


@[data_synth]
theorem getElem.arg_xs.HasRevFDeriv_rule_applied_index {𝕜 : Type u} {X : Type*} {I Y : Type*}
    [GetElem' X I Y]
    [SetElem' X I Y] [LawfulSetElem X I]
    {nI} [IndexType I nI] [RCLike 𝕜]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I]  (i : I) :
    HasRevFDeriv 𝕜
      (fun (x : X) => x[i])
      (fun x => (x[i],
        fun xi =>
          let x' := setElem (0: X) i xi .intro
          x')) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro; simp; data_synth
  case simp => rfl

@[data_synth]
theorem getElem.arg_xs.HasRevFDerivUpdate_rule_applied_index {𝕜 : Type u} {X I Y : Type*}
    [GetElem' X I Y] [InjectiveGetElem X I]
    [SetElem' X I Y] [LawfulSetElem X I]
    {nI} [IndexType I nI] [RCLike 𝕜]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I]  (i : I) :
    HasRevFDerivUpdate 𝕜
      (fun (x : X) => x[i])
      (fun x => (x[i],
        fun xi' x =>
          let xi := x[i];
          let x := setElem x i (xi + xi') .intro
          x)) := by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; data_synth
  case adjoint => intro; simp; data_synth
  case simp => rfl

----------------------------------------------------------------------------------------------------
