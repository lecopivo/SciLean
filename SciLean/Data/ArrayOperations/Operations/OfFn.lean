import SciLean.Analysis.Calculus.HasFDeriv
import SciLean.Analysis.Calculus.HasRevFDeriv
import SciLean.Analysis.Calculus.HasFwdFDeriv
import SciLean.Data.ArrayOperations.Algebra
import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.IfPull

namespace SciLean

@[fun_prop]
theorem ofFn.arg_f.IsLinearMap_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I] [OfFn X I Y] [LawfulOfFn X I]
    [Ring 𝕜] [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] :
    IsLinearMap 𝕜 (fun f : I → Y => ofFn (coll:=X) f) := by
  constructor <;> (intros; apply getElem_injective (idx:=I); funext i; simp)

-- not sure if this is provable with the current assumptions
-- if not then just make `IsContinuousGetElem` stronger
@[fun_prop]
theorem ofFn.arg_f.Continuous_rule {X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I] [OfFn X I Y] [LawfulOfFn X I]
    [TopologicalSpace X] [TopologicalSpace Y] [IsContinuousGetElem X I] :
    Continuous (fun f : I → Y => ofFn (coll:=X) f) := by sorry_proof

@[fun_prop]
theorem ofFn.arg_f.IsContinuousLinearMap_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I] [OfFn X I Y] [LawfulOfFn X I] [Ring 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
    [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] :
    IsContinuousLinearMap 𝕜 (fun f : I → Y => ofFn (coll:=X) f) := by
  constructor; fun_prop; dsimp[autoParam]; fun_prop

@[data_synth]
theorem ofFn.arg_f.HasFDerivAt_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I] [OfFn X I Y] [LawfulOfFn X I]
    [RCLike 𝕜] [Fintype I]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] (f₀ : I → Y) :
    HasFDerivAt (fun f : I → Y => ofFn (coll:=X) f) (fun df : I → Y =>L[𝕜] ofFn (coll:=X) df) f₀ := by
  apply hasFDerivAt_from_isContinuousLinearMap (𝕜:=𝕜) (x₀:=f₀)


@[data_synth]
theorem ofFn.arg_f.HasFwdFDeriv_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I] [OfFn X I Y] [LawfulOfFn X I]
    [RCLike 𝕜] [Fintype I]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] :
    HasFwdFDeriv 𝕜
      (fun f : I → Y => ofFn (coll:=X) f)
      (fun f df => (ofFn f, ofFn df)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; rfl


@[data_synth]
theorem ofFn.arg_f.HasAdjoint_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I] [OfFn X I Y] [LawfulOfFn X I]
    {nI} [IndexType I nI] [Fold I] [RCLike 𝕜]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I] :
    HasAdjoint 𝕜
      (fun (f : I → Y) => ofFn (coll:=X) f)
      (fun x i =>
         let xi := x[i]
         xi) := by
  constructor
  case adjoint => intro x f; simp[Inner.inner, inner_eq_sum_getElem (I:=I), IndexType.sum_eq_finset_sum]
  case is_linear => fun_prop

@[data_synth]
theorem ofFn.arg_f.HasAdjointUpdate_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I] [OfFn X I Y] [LawfulOfFn X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I]
    {nI} [IndexType I nI] [Fold I] [RCLike 𝕜]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I] :
    HasAdjointUpdate 𝕜
      (fun f : I → Y => ofFn (coll:=X) f)
      (fun dx f' i =>
        let dxi := f' i + dx[i]
        dxi) := by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; funext i; simp

@[data_synth]
theorem ofFn.arg_f.HasRevFDeriv_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I] [OfFn X I Y] [LawfulOfFn X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I]
    {nI} [IndexType I nI] [Fold I] [RCLike 𝕜]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I] :
    HasRevFDeriv 𝕜
      (fun f : I → Y => ofFn (coll:=X) f)
      (fun f => (ofFn f,
        fun dx i =>
          let dxi := dx[i]
          dxi)) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intro; data_synth
  case adjoint => intro; simp; data_synth
  case simp => rfl

@[data_synth]
theorem ofFn.arg_f.HasRevFDerivUpdate_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I] [OfFn X I Y] [LawfulOfFn X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I]
    {nI} [IndexType I nI] [Fold I] [RCLike 𝕜]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I] :
    HasRevFDerivUpdate 𝕜
      (fun f : I → Y => ofFn (coll:=X) f)
      (fun f => (ofFn f,
        fun dx f' i =>
          let dxi := f' i + dx[i]
          dxi)) := by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intro; apply ofFn.arg_f.HasFDerivAt_rule
  case adjoint => intro; simp; data_synth
  case simp => rfl
