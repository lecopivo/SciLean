import SciLean.Analysis.Calculus.HasFDeriv
import SciLean.Analysis.Calculus.HasRevFDeriv
import SciLean.Analysis.Calculus.HasFwdFDeriv
import SciLean.Data.ArrayOperations.Algebra
import SciLean.Data.ArrayOperations.Operations
import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.IfPull

namespace SciLean.ArrayOps


set_option linter.unusedVariables false in
@[data_synth]
theorem mapIdxMonoAcc.arg_fxs.HasRevFDeriv_rule
    {𝕜 : Type u} {X : Type v} {I : Type*} {Y : Type w}
    [GetElem' X I Y] [OfFn X I Y] [LawfulOfFn X I]
    [SetElem' X I Y] [LawfulSetElem X I]
    {nI} [IndexType I nI] [Fold.{_,v} I] [RCLike 𝕜]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [NormedAddCommGroup W] [AdjointSpace 𝕜 W] [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I]
    (f : W → I → Z → Y → Y) (g : W → I → Z)  (xs : W → X) (f' g' xs' : I → _)
    (hf : ∀ (i : I), HasRevFDerivUpdate 𝕜 (fun wzy : W×Z×Y => f wzy.1 i wzy.2.1 wzy.2.2) (f' i))
    (hg : ∀ (i : I), HasRevFDerivUpdate 𝕜 (fun w => g w i) (g' i))
    (hxs : ∀ (i : I), HasRevFDerivUpdate 𝕜 (fun w => (xs w)[i]) (xs' i)) :
    HasRevFDeriv 𝕜
      (fun w => mapIdxMonoAcc (f w) (g w) (xs w))
      (fun w =>
        let xs := xs w
        let r := mapIdxMonoAcc (f w) (g w) xs
        (r, fun dy =>
          let dw := IndexType.fold .full (init:=(0:W)) (fun (i : I) dw =>
            let xi := xs[i]
            let dyi := dy[i]
            let' (zi,dz') := g' i w
            let' (dw,dzi, dxi) := (f' i (w,zi,xi)).2 dyi (dw,0)
            let dw := dz' dzi dw
            let dw := (xs' i w).2 dxi dw
            dw)
          dw)) := sorry_proof


set_option linter.unusedVariables false in
@[data_synth]
theorem mapIdxMonoAcc.arg_fxs.HasRevFDerivUpdate_rule
    {𝕜 : Type u} {X : Type v} {I : Type*} {Y : Type w}
    [GetElem' X I Y] [OfFn X I Y] [LawfulOfFn X I]
    [SetElem' X I Y] [LawfulSetElem X I]
    {nI} [IndexType I nI] [Fold.{_,v} I] [RCLike 𝕜]
    [NormedAddCommGroup X] [AdjointSpace 𝕜 X] [NormedAddCommGroup Y] [AdjointSpace 𝕜 Y]
    [NormedAddCommGroup W] [AdjointSpace 𝕜 W] [NormedAddCommGroup Z] [AdjointSpace 𝕜 Z]
    [IsModuleGetElem 𝕜 X I] [IsContinuousGetElem X I] [IsInnerGetElem 𝕜 X I]
    (f : W → I → Z → Y → Y) (g : W → I → Z)  (xs : W → X) (f' g' xs' : I → _)
    (hf : ∀ (i : I), HasRevFDerivUpdate 𝕜 (fun wzy : W×Z×Y => f wzy.1 i wzy.2.1 wzy.2.2) (f' i))
    (hg : ∀ (i : I), HasRevFDerivUpdate 𝕜 (fun w => g w i) (g' i))
    (hxs : ∀ (i : I), HasRevFDerivUpdate 𝕜 (fun w => (xs w)[i]) (xs' i)) :
    HasRevFDerivUpdate 𝕜
      (fun w => mapIdxMonoAcc (f w) (g w) (xs w))
      (fun w =>
        let xs := xs w
        let r := mapIdxMonoAcc (f w) (g w) xs
        (r, fun dy dw =>
          let dw := IndexType.fold .full (init:=dw) (fun (i : I) dw =>
            let xi := xs[i]
            let dyi := dy[i]
            let' (zi,dz') := g' i w
            let' (dw,dzi, dxi) := (f' i (w,zi,xi)).2 dyi (dw,0)
            let dw := dz' dzi dw
            let dw := (xs' i w).2 dxi dw
            dw)
          dw)) := sorry_proof
