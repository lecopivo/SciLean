import SciLean.Core.Monads.FwdDerivMonad
import SciLean.Core.Monads.RevDerivMonad

namespace SciLean

variable 
  {K : Type _} [IsROrC K]

instance [Vec K X] : Vec K (Id X) := by unfold Id; infer_instance
instance [SemiInnerProductSpace K X] : SemiInnerProductSpace K (Id X) := by unfold Id; infer_instance
-- instance [FinVec ι K X] : SemiInnerProductSpace K (Id X) := by unfold Id; infer_instance
  
noncomputable
instance : FwdDerivMonad K Id Id where
  fwdDerivM f := fwdCDeriv K f
  IsDifferentiableM f := IsDifferentiable K f
  fwdDerivM_pure f := by simp[pure]
  fwdDerivM_bind := by intros; simp; ftrans
  fwdDerivM_pair y := by intros; simp; ftrans
  IsDifferentiableM_pure := by simp[pure]
  IsDifferentiableM_bind := by simp[bind]; fprop
  IsDifferentiableM_pair y := 
    by 
      intros; simp[bind]; -- fprop something goes wrong where :(
      have h : IsDifferentiable K (fun x : _ => (x, y x)) := by fprop 
      apply h


noncomputable
instance : RevDerivMonad K Id Id where
  revDerivM f := revCDeriv K f
  HasAdjDiffM f := HasAdjDiff K f
  revDerivM_pure f := by simp[pure]
  revDerivM_bind := by intros; simp; ftrans; rfl
  revDerivM_pair y := by intros; simp; ftrans
  HasAdjDiffM_pure := by simp[pure]
  HasAdjDiffM_bind := by simp[bind]; fprop
  HasAdjDiffM_pair y := 
    by 
      intros; simp[bind]; -- fprop something goes wrong where :(
      have h : HasAdjDiff K (fun x : _ => (x, y x)) := by fprop 
      apply h


end SciLean
open SciLean


section OnVec

variable 
  {K : Type _} [IsROrC K]
  {X : Type} [Vec K X]
  {Y : Type} [Vec K Y]
  {Z : Type} [Vec K Z]
  {E : ι → Type} [∀ i, Vec K (E i)]

@[fprop]
theorem Id.run.arg_x.IsDifferentiable_rule
  (a : X → Id Y) (ha : IsDifferentiableM K a)
  : IsDifferentiable K (fun x => Id.run (a x)) := ha

@[ftrans]
theorem Id.run.arg_x.fwdCDeriv_rule (a : X → Id Y)
  : fwdCDeriv K (fun x => Id.run (a x))
    =
    fun x dx => (fwdDerivM K a x dx) := by rfl

end OnVec

section OnSemiInnerProductSpace

variable 
  {K : Type _} [IsROrC K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {E : ι → Type} [∀ i, SemiInnerProductSpace K (E i)]


@[fprop]
theorem Id.run.arg_x.HasAdjDiff_rule
  (a : X → Id Y) (ha : HasAdjDiffM K a)
  : HasAdjDiff K (fun x => Id.run (a x)) := ha

@[ftrans]
theorem Id.run.arg_x.revCDeriv_rule (a : X → Id Y)
  : revCDeriv K (fun x => Id.run (a x))
    =
    fun x => (revDerivM K a x) := by rfl

end OnSemiInnerProductSpace
