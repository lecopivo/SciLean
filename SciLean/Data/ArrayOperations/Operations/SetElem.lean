import SciLean.Analysis.Calculus.HasFDeriv
import SciLean.Analysis.Calculus.HasRevFDeriv
import SciLean.Analysis.Calculus.HasFwdFDeriv
import SciLean.Data.ArrayOperations.Algebra
import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.IfPull

namespace SciLean

open Classical

@[fun_prop]
theorem setElem.arg_xsv.IsLinearMap_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I]
    [Ring 𝕜] [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] (i : I) :
    IsLinearMap 𝕜 (fun xy : X×Y => setElem xy.1 i xy.2 .intro) := by
  constructor <;>
   (intros
    apply getElem_injective (idx:=I); funext j
    by_cases i=j <;> simp_all)

-- not sure if assumptions are strong enough, if not just make `IsContinuousGetElem` stronger
@[fun_prop]
theorem setElem.arg_xsv.Continuous_rule {X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I]
    [TopologicalSpace X] [TopologicalSpace Y]
    [IsContinuousGetElem X I] (i : I) :
    Continuous (fun xy : X×Y => setElem xy.1 i xy.2 .intro) := by sorry_proof

@[fun_prop]
theorem setElem.arg_xsv.IsContinuousLinearMap_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I] [Ring 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
    [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] (i : I) :
    IsContinuousLinearMap 𝕜 (fun xy : X×Y => setElem xy.1 i xy.2 .intro) := by
  constructor <;> fun_prop

@[data_synth]
theorem setElem.arg_xsv.HasFDerivAt_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I] [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] (i : I) (xy₀ : X×Y) :
    HasFDerivAt
      (fun xy : X×Y => setElem xy.1 i xy.2 .intro)
      (fun dxy : X×Y =>L[𝕜] setElem dxy.1 i dxy.2 .intro) xy₀ := by
  apply hasFDerivAt_from_isContinuousLinearMap

-- TODO: generate automatically from `setElem.arg_xsv.HasFDerivAt_rule`
@[data_synth]
theorem setElem.arg_xs.HasFDerivAt_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I] [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] (i : I) (x₀ : X) (y : Y) :
    HasFDerivAt
      (fun x : X => setElem x i y .intro)
      (fun dx : X =>L[𝕜] setElem dx i 0 .intro) x₀ := by
  have h := setElem.arg_xsv.HasFDerivAt_rule (𝕜:=𝕜) (X:=X) (I:=I) i (x₀,y)
            |>.comp (f:=fun x : X => (x,y)) (hf:=by data_synth)
  apply h

-- TODO: generate automatically from `setElem.arg_xsv.HasFDerivAt_rule`
@[data_synth]
theorem setElem.arg_v.HasFDerivAt_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I] [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] (i : I) (x : X) (y₀ : Y) :
    HasFDerivAt
      (fun y : Y => setElem x i y .intro)
      (fun dy : Y =>L[𝕜] setElem 0 i dy .intro) y₀ := by
  have h := setElem.arg_xsv.HasFDerivAt_rule (𝕜:=𝕜) (X:=X) (I:=I) i (x,y₀)
            |>.comp (f:=fun y : Y => (x,y)) (hf:=by data_synth)
  apply h


@[data_synth]
theorem setElem.arg_xsv.HasFwdFDeriv_rule {𝕜 X I Y : Type*}
    [GetElem' X I Y] [InjectiveGetElem X I]
    [SetElem' X I Y] [LawfulSetElem X I] [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] (i : I) :
    HasFwdFDeriv 𝕜
      (fun xy : X×Y => setElem xy.1 i xy.2 .intro)
      (fun xy dxy : X×Y =>
        (setElem xy.1 i xy.2 .intro,
         setElem dxy.1 i dxy.2 .intro)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => simp

-- TODO: generate automatically from `setElem.arg_xsv.HasFwdFDeriv_rule`
@[data_synth]
theorem setElem.arg_xs.HasFwdFDeriv_rule {𝕜 X I Y : Type*}
    [GetElem' X I Y] [InjectiveGetElem X I]
    [SetElem' X I Y] [LawfulSetElem X I] [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] (i : I) (y : Y) :
    HasFwdFDeriv 𝕜
      (fun x : X => setElem x i y .intro)
      (fun x dx : X =>
        (setElem x i y .intro,
         setElem dx i 0 .intro)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => simp

-- TODO: generate automatically from `setElem.arg_xsv.HasFwdFDeriv_rule`
@[data_synth]
theorem setElem.arg_v.HasFwdFDeriv_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I] [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] (i : I) (x : X) :
    HasFwdFDeriv 𝕜
      (fun y : Y => setElem x i y .intro)
      (fun y dy : Y =>
        (setElem x i y .intro,
         setElem 0 i dy .intro)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => simp

@[data_synth]
theorem setElem.arg_xs.HasAdjoint_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I]
    [RCLike 𝕜] {nI} [IndexType I nI]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
    [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I] (i : I) :
    HasAdjoint 𝕜
      (fun (xy : X×Y) => setElem xy.1 i xy.2 True.intro)
      (fun x' =>
        let xi' := x'[i]
        let x' := setElem x' i 0 .intro
        (x', xi')) := by
  constructor
  case adjoint =>
    rintro ⟨x,y⟩ x'
    simp[inner_eq_sum_getElem (I:=I),Tactic.if_pull,AdjointSpace.inner_prod_split,
         Finset.sum_ite]
    simp only [Finset.sum_filter]
    simp; ac_rfl
  case is_linear => apply setElem.arg_xsv.IsContinuousLinearMap_rule

open Classical
@[data_synth]
theorem setElem.arg_xs.HasAdjointUpdate_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I]
    [RCLike 𝕜] {nI} [IndexType I nI]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
    [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I] (i : I) :
    HasAdjointUpdate 𝕜
      (fun (xy : X×Y) => setElem xy.1 i xy.2 True.intro)
      (fun x xy' =>
        let' (x',y') := xy'
        let xi := y' + x[i]
        let x' := x' + setElem x i 0 .intro
        (x', xi)) := by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => simp


@[data_synth]
theorem setElem.arg_xs.HasRevFDeriv_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I]
    [RCLike 𝕜] {nI} [IndexType I nI]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
    [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I] (i : I) :
    HasRevFDeriv 𝕜
      (fun (xy : X×Y) => setElem xy.1 i xy.2 True.intro)
      (fun xy =>
        (setElem xy.1 i xy.2 .intro,
         fun dx' =>
           let dxi := dx'[i]
           let dx' := setElem dx' i 0 .intro
           (dx', dxi))) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; simp; data_synth
  case simp => rfl

open Classical
@[data_synth]
theorem setElem.arg_xs.HasRevFDerivUpdate_rule {𝕜 X I Y : Type*}
    [GetElem X I Y (fun _ _ => True)] [InjectiveGetElem X I]
    [SetElem X I Y (fun _ _ => True)] [LawfulSetElem X I]
    [RCLike 𝕜] {nI} [IndexType I nI]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X]
    [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I] (i : I) :
    HasRevFDerivUpdate 𝕜
      (fun (xy : X×Y) => setElem xy.1 i xy.2 True.intro)
      (fun xy =>
        (setElem xy.1 i xy.2 .intro,
         fun x xy' =>
         let' (x',y') := xy'
         let y' := y' + x[i]
         let x' := x' + setElem x i 0 .intro
         (x', y'))) := by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv   => intros; data_synth
  case adjoint => intros; simp; data_synth
  case simp => rfl
