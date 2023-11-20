import SciLean.Core.Monads.FwdDerivMonad
import SciLean.Core.Monads.Id
import SciLean.Data.DataArray

set_option linter.unusedVariables false

open SciLean

variable 
  {K : Type _} [IsROrC K]


section OnVec

variable 
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {W : Type _} [Vec K W]

-- TODO: transport vec structure from Prod
instance [Vec K X] [Vec K Y] : Vec K (MProd X Y) := sorry


@[fprop]
theorem MProd.mk.arg_fstsnd.IsDifferentiable_rule 
  (f : W → X) (g : W → Y) (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : IsDifferentiable K (fun w => MProd.mk (f w) (g w)) := by sorry_proof

@[ftrans]
theorem MProd.mk.arg_fstsnd.cderiv_rule
  (f : W → X) (g : W → Y) (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : cderiv K (fun w => MProd.mk (f w) (g w))
    =
    fun w dw => 
      let dx := cderiv K f w dw
      let dy := cderiv K g w dw
      ⟨dx,dy⟩ :=
by 
  sorry_proof

@[ftrans]
theorem MProd.mk.arg_fstsnd.fwdCDeriv_rule
  (f : W → X) (g : W → Y) (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : fwdCDeriv K (fun w => MProd.mk (f w) (g w))
    =
    fun w dw => 
      let xdx := fwdCDeriv K f w dw
      let ydy := fwdCDeriv K g w dw
      (⟨xdx.1,ydy.1⟩, ⟨xdx.2,ydy.2⟩) :=
by 
  unfold fwdCDeriv; ftrans

@[fprop]
theorem MProd.fst.arg_self.IsDifferentiable_rule 
  (f : W → MProd X Y) (hf : IsDifferentiable K f)
  : IsDifferentiable K (fun w => (f w).1) := by sorry_proof

@[ftrans]
theorem MProd.fst.arg_self.fwdCDeriv_rule 
  (f : W → MProd X Y) (hf : IsDifferentiable K f)
  : fwdCDeriv K (fun w => (f w).1)
    =
    fun w dw => 
      let xydxy := fwdCDeriv K f w dw
      (xydxy.1.1, xydxy.2.1) := by sorry_proof

@[fprop]
theorem MProd.snd.arg_self.IsDifferentiable_rule 
  (f : W → MProd X Y) (hf : IsDifferentiable K f)
  : IsDifferentiable K (fun w => (f w).2) := by sorry_proof

@[ftrans]
theorem MProd.snd.arg_self.fwdCDeriv_rule 
  (f : W → MProd X Y) (hf : IsDifferentiable K f)
  : fwdCDeriv K (fun w => (f w).2)
    =
    fun w dw => 
      let xydxy := fwdCDeriv K f w dw
      (xydxy.1.2, xydxy.2.2) := by sorry_proof


end OnVec


section OnSemiInnerProductSpace

variable 
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {W : Type _} [SemiInnerProductSpace K W]

-- TODO: transport structure from Prod
instance [Inner K X] [Inner K Y] : Inner K (MProd X Y) := 
  ⟨fun ⟨x,y⟩ ⟨x',y'⟩ => Inner.inner x x' + Inner.inner y y'⟩

instance [TestFunctions X] [TestFunctions Y] : TestFunctions (MProd X Y) where
  TestFunction := fun ⟨x,y⟩ => TestFunction x ∧ TestFunction y

instance [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] : SemiInnerProductSpace K (MProd X Y) := SemiInnerProductSpace.mkSorryProofs

@[fprop]
theorem MProd.mk.arg_fstsnd.HasSemiAdjoint_rule 
  (f : W → X) (g : W → Y) (hf : HasSemiAdjoint K f) (hg : HasSemiAdjoint K g)
  : HasSemiAdjoint K (fun w => MProd.mk (f w) (g w)) := by sorry_proof


@[fprop]
theorem MProd.mk.arg_fstsnd.HasAdjDiff_rule 
  (f : W → X) (g : W → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : HasAdjDiff K (fun w => MProd.mk (f w) (g w)) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop


@[ftrans]
theorem MProd.mk.arg_fstsnd.revCDeriv_rule
  (f : W → X) (g : W → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revCDeriv K (fun w => MProd.mk (f w) (g w))
    =
    fun w => 
      let xdf' := revCDeriv K f w
      let ydg' := revCDeriv K g w
      (MProd.mk xdf'.1 ydg'.1, 
       fun dxy => 
         xdf'.2 dxy.1 + ydg'.2 dxy.2) := 
by 
  sorry_proof

@[fprop]
theorem MProd.fst.arg_self.HasAdjDiff_rule 
  (f : W → MProd X Y) (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun w => (f w).1) := by sorry_proof

@[ftrans]
theorem MProd.fst.arg_self.revCDeriv_rule 
  (f : W → MProd X Y) (hf : HasAdjDiff K f)
  : revCDeriv K (fun w => (f w).1)
    =
    fun w => 
      let xydxy := revCDeriv K f w
      (xydxy.1.1, fun dw => xydxy.2 (MProd.mk dw 0)) := by sorry_proof

@[fprop]
theorem MProd.snd.arg_self.HasAdjDiff_rule 
  (f : W → MProd X Y) (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun w => (f w).2) := by sorry_proof

@[ftrans]
theorem MProd.snd.arg_self.revCDeriv_rule 
  (f : W → MProd X Y) (hf : HasAdjDiff K f)
  : revCDeriv K (fun w => (f w).2)
    =
    fun w => 
      let xydxy := revCDeriv K f w
      (xydxy.1.2, fun dw => xydxy.2 (MProd.mk 0 dw)) := by sorry_proof


end OnSemiInnerProductSpace



