import SciLean.Core.FunctionTransformations
import SciLean.Core.Monads.FwdDerivMonad
import SciLean.Core.Monads.Id
import SciLean.Data.DataArray

set_option linter.unusedVariables false

open SciLean


instance [Add X] [Add Y] : Add (MProd X Y) := ⟨fun ⟨x,y⟩ ⟨x',y'⟩ => ⟨x+x', y+y'⟩⟩
instance [Sub X] [Sub Y] : Sub (MProd X Y) := ⟨fun ⟨x,y⟩ ⟨x',y'⟩ => ⟨x-x', y-y'⟩⟩
instance [Neg X] [Neg Y] : Neg (MProd X Y) := ⟨fun ⟨x,y⟩ => ⟨-x, -y⟩⟩
instance [SMul K X] [SMul K Y] : SMul K (MProd X Y) := ⟨fun k ⟨x,y⟩ => ⟨k•x, k•y⟩⟩
instance [Zero X] [Zero Y] : Zero (MProd X Y) := ⟨⟨0,0⟩⟩
instance [TopologicalSpace X] [TopologicalSpace Y] : TopologicalSpace (MProd X Y) := sorry

instance [IsROrC K] [Vec K X] [Vec K Y] : Vec K (MProd X Y) := Vec.mkSorryProofs


section Simps

@[simp, ftrans_simp]
theorem MProd.mk_fst (x : X) (y : Y)
  : (MProd.mk x y).1 = x := by simp

@[simp, ftrans_simp]
theorem MProd.mk_snd (x : X) (y : Y)
  : (MProd.mk x y).2 = y := by simp


@[simp, ftrans_simp]
theorem MProd.add_mk [Add X] [Add Y] (x x' : X) (y y' : Y)
  : MProd.mk x y + MProd.mk x' y'
    =
    MProd.mk (x+x') (y+y') := by rfl

@[simp, ftrans_simp]
theorem MProd.sub_mk [Sub X] [Sub Y] (x x' : X) (y y' : Y)
  : MProd.mk x y - MProd.mk x' y'
    =
    MProd.mk (x-x') (y-y') := by rfl

@[simp, ftrans_simp]
theorem MProd.smul_mk [SMul K X] [SMul K Y] (k : K) (x : X) (y : Y)
  : k • MProd.mk x y 
    =
    MProd.mk (k•x) (k•y) := by rfl

@[simp, ftrans_simp]
theorem MProd.neg_mk [Neg X] [Neg Y] (x : X) (y : Y)
  : - MProd.mk x y 
    =
    MProd.mk (-x) (-y) := by rfl


end Simps

variable 
  {K : Type _} [IsROrC K]

section OnVec

variable 
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {W : Type _} [Vec K W]


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

@[ftrans]
theorem MProd.mk.arg_fstsnd.semiAdjoint_rule
  (f : W → X) (g : W → Y) (hf : HasSemiAdjoint K f) (hg : HasSemiAdjoint K g)
  : semiAdjoint K (fun w => MProd.mk (f w) (g w))
    =
    fun xy : MProd X Y => 
      let w₁ := semiAdjoint K f xy.1
      let w₂ := semiAdjoint K g xy.2
      w₁ + w₂ := 
by 
  sorry_proof


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

@[ftrans]
theorem MProd.mk.arg_fstsnd.revDerivUpdate_rule
  (f : W → X) (g : W → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revDerivUpdate K (fun w => MProd.mk (f w) (g w))
    =
    fun w => 
      let xdf' := revDerivUpdate K f w
      let ydg' := revDerivUpdate K g w
      (MProd.mk xdf'.1 ydg'.1, 
       fun dxy dw => 
         xdf'.2 dxy.1 (ydg'.2 dxy.2 dw)) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate
  ftrans; funext x; simp
  funext dy dx
  ftrans
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


@[ftrans]
theorem MProd.fst.arg_self.revDerivUpdate_rule 
  (f : W → MProd X Y) (hf : HasAdjDiff K f)
  : revDerivUpdate K (fun w => (f w).1)
    =
    fun w => 
      let xydxy := revDerivUpdate K f w
      (xydxy.1.1, fun dx' dw => xydxy.2 (MProd.mk dx' 0) dw) := by sorry_proof


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
      (xydxy.1.2, fun dy' => xydxy.2 (MProd.mk 0 dy')) := by sorry_proof

@[ftrans]
theorem MProd.snd.arg_self.revDerivUpdate_rule 
  (f : W → MProd X Y) (hf : HasAdjDiff K f)
  : revDerivUpdate K (fun w => (f w).2)
    =
    fun w => 
      let xydxy := revDerivUpdate K f w
      (xydxy.1.2, fun dy' dw => xydxy.2 (MProd.mk 0 dy') dw) := by sorry_proof


end OnSemiInnerProductSpace



