import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.HasParamDerivWithDisc.HasParamFDerivWithDisc
-- import Mathlib.Lean.CoreM
import SciLean.Tactic.IfPull


set_option linter.unusedVariables false

open MeasureTheory

namespace SciLean

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace R W] [NormedSpace ℝ W] [CompleteSpace W]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [NormedSpace ℝ X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace R Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Y₁ : Type} [NormedAddCommGroup Y₁] [AdjointSpace R Y₁] [NormedSpace ℝ Y₁] [CompleteSpace Y₁]
  {Y₂ : Type} [NormedAddCommGroup Y₂] [AdjointSpace R Y₂] [NormedSpace ℝ Y₂] [CompleteSpace Y₂]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace R Z] [NormedSpace ℝ Z] [CompleteSpace Z]

set_default_scalar R



----------------------------------------------------------------------------------------------------

@[fun_trans]
theorem adjoint_integral (f : X → Y → Z) (μ : Measure X) :
  adjoint R (fun y => ∫ x, f x y ∂μ)
  =
  fun y' => ∫ x, adjoint R (f x) y' ∂μ := sorry_proof

@[fun_trans]
theorem adjoint_sum {ι} [IndexType ι] (f : ι → Y → Z) :
  adjoint R (fun y => ∑ i, f i y)
  =
  fun y' => ∑ i, adjoint R (f i) y' := sorry_proof

@[fun_prop]
theorem integral_IsContinuousLinearMap
  (f : X → Y → Z) (μ : Measure X) (hf : ∀ x, IsContinuousLinearMap R (f x)) :
  IsContinuousLinearMap R (fun y => ∫ x, f x y ∂μ) := sorry_proof

@[fun_prop]
theorem sum_IsContinuousLinearMap {ι} [IndexType ι]
  (f : ι → Y → Z) (hf : ∀ i, IsContinuousLinearMap R (f i)) :
  IsContinuousLinearMap R (fun y => ∑ i, f i y) := sorry_proof

-- only true over reals!!!
@[fun_prop]
theorem adjoint_IsContinuousLinearMap
  (f : X → Y → Z) (hf : ∀ x, IsContinuousLinearMap R (f x)) :
  IsContinuousLinearMap R (fun y => adjoint R (f · y)) := sorry_proof

@[fun_prop]
theorem adjoint_IsContinuousLinearMap'
  (f : X → Y) :
  IsContinuousLinearMap R (adjoint R f) := sorry_proof

attribute [fun_trans] adjoint_adjoint

----------------------------------------------------------------------------------------------------

variable (R)
open Classical in
noncomputable
def frontierGrad (Ω : W → Set X) (w : W) (x : X) : W :=
  adjoint R (fun dw => frontierSpeed R Ω w dw x) 1


variable (W X Y)
structure DiscontinuityRevData where
  vals : X → Y×Y
  speedGrad : X → W
  discontinuity : Set X

abbrev DiscontinuityRevDataList := List (DiscontinuityRevData W X Y)
variable {W X Y}


def DiscontinuityRevDataList.getDiscontinuity (d : DiscontinuityRevDataList W X Y) : Set X :=
  d.foldl (init:=∅) (fun s ⟨_,_,x⟩ => s ∪ x)

def DiscontinuityRevDataList.getDiscontinuities (d : DiscontinuityRevDataList W X Y) : List (Set X) :=
  d.map (·.discontinuity)


@[gtrans]
def HasParamRevFDerivWithDiscAt (f : W → X → Y) (w : W)
    (f' : outParam <| X → Y×(Y→W))
    (disc : outParam <| DiscontinuityRevDataList W X Y) :=
  HasParamFDerivWithDiscAt R f w
    (fun (dw : W) (x : X) => adjoint R (f' x).2 dw)
    (disc.map (fun ⟨df,s,S⟩ => ⟨df,fun dy x => ⟪s x, dy⟫,S⟩))
  ∧
  ∀ x, (f' x).1 = f w x

variable {R}

open FiniteDimensional

@[fun_trans]
theorem revFDeriv_under_integral
    (f : W → X → Y) (w : W) (μ : Measure X)
    {f' disc}
    (hf : HasParamRevFDerivWithDiscAt R f w f' disc) :
    (revFDeriv R (fun w' => ∫ x, f w' x ∂μ) w)
    =
    let val := ∫ x, f w x ∂μ
    (val, fun dy =>
      let interior := ∫ x, (f' x).2 dy ∂μ
      let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
      let shocks := disc.foldl (init:=0)
        fun sum ⟨df,s,S⟩ => sum +
          ∫ x in S,
            let vals := df x
            (⟪vals.1 - vals.2, dy⟫ * density x) • s x ∂μH[finrank R X - (1:ℕ)]
      interior + shocks) := by

  unfold revFDeriv
  simp only [fderiv_under_integral R f w _ μ hf.1]
  have hf' : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry_proof -- this should be part of hf
  fun_trans (disch:=apply hf') [adjoint_sum,adjoint_integral,adjoint_adjoint,smul_smul]

  -- ugh some nasty proof
  -- probably by induction, but we need to do proof of linearity of that fold by induction too
  sorry_proof

@[fun_trans]
theorem revFDeriv_under_integral_over_set
    (f : W → X → Y) (w : W) (μ : Measure X) (Ω : Set X)
    {f' disc}
    (hf : HasParamRevFDerivWithDiscAt R f w f' disc)
    (hA : AlmostDisjoint (frontier Ω) disc.getDiscontinuity μH[finrank ℝ X - (1:ℕ)]) :
    (revFDeriv R (fun w' => ∫ x in Ω, f w' x ∂μ) w)
    =
    let val := ∫ x in Ω, f w x ∂μ
    (val, fun dy =>
      let interior := ∫ x in Ω, (f' x).2 dy ∂μ
      let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
      let shocks := disc.foldl (init:=0)
        fun sum ⟨df,s,Γ⟩ => sum +
          ∫ x in Γ ∩ Ω,
            let vals := df x
            (⟪vals.1 - vals.2, dy⟫ * density x) • s x ∂μH[finrank R X - (1:ℕ)]
      interior + shocks) := by

  simp[revFDeriv]
  simp only [fderiv_under_integral_over_set R f w _ μ Ω hf.1 sorry_proof]
  have hf' : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry_proof -- this should be part of hf
  fun_trans (disch:=apply hf') [adjoint_sum,adjoint_integral,adjoint_adjoint,smul_smul]

  sorry_proof



----------------------------------------------------------------------------------------------------
-- Lambda rules ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

namespace HasParamRevFDerivWithDiscAt

@[gtrans]
theorem smooth_rule
    (w : W)
    (f : W → X → Y) (hf : ∀ x, DifferentiableAt R (f · x) w) :
    HasParamRevFDerivWithDiscAt R f w (fun x => revFDeriv R (f · x) w) [] := by

  unfold HasParamRevFDerivWithDiscAt
  constructor
  · convert HasParamFDerivWithDiscAt.differentiable_at_rule R w f hf
    · fun_trans [revFDeriv]
  · simp [revFDeriv]


theorem comp_differentiable_discs_rule
    (f : W → Y → Z) (g : W → X → Y) (w : W)
    {g' disc}
    (hf : Differentiable R (fun (w,y) => f w y))
    (hg : HasParamRevFDerivWithDiscAt R g w g' disc) :
    HasParamRevFDerivWithDiscAt (R:=R) (fun w x => f w (g w x)) w
      (f' := fun x =>
         let ydg := g' x
         let zdf := revFDeriv R (fun (w,y) => f w y) (w,ydg.1)
         (zdf.1,
          fun dz =>
            let dwy := zdf.2 dz
            let dw := ydg.2 dwy.2
            dwy.1 + dw))
      (disc := disc.map fun ⟨vals,s,S⟩ =>
        { vals := fun x =>
            let y := vals x
            (f w y.1, f w y.2)
          speedGrad := s
          discontinuity := S }) := by

  unfold HasParamRevFDerivWithDiscAt
  constructor
  · convert HasParamFDerivWithDiscAt.comp_differentiable_discs_rule R f g w hf hg.1
    · rename_i w x
      have hg' : IsContinuousLinearMap R (g' x).2 := by sorry_proof
      simp [revFDeriv, hg.2]
      fun_trans
      sorry_proof
    · simp[List.map_append]
  · simp [revFDeriv,hg.2]


@[gtrans]
theorem _root_.Prod.mk.arg_fstsnd.HasParamRevFDerivWithDiscAt_rule
    (f : W → X → Y) (g : W → X → Z) (w : W)
    {f' fdisc} {g' gdisc}
    (hf : HasParamRevFDerivWithDiscAt R f w f' fdisc)
    (hg : HasParamRevFDerivWithDiscAt R g w g' gdisc)
    (hdisjoint : AlmostDisjoint fdisc.getDiscontinuity gdisc.getDiscontinuity μH[finrank ℝ X - (1:ℕ)])
    /- (hIJ : DisjointDiscs R Sf Sg) -/ :
    HasParamRevFDerivWithDiscAt (R:=R) (fun w x => (f w x, g w x)) w
      (f' := fun x =>
        let ydf := f' x
        let zdg := g' x
        ((ydf.1,zdg.1), fun dyz => ydf.2 dyz.1 + zdg.2 dyz.2))
      (disc :=
        fdisc.map (fun d =>
          { d with vals := fun x =>
              let y := d.vals x
              let z := g w x
              ((y.1, z), (y.2, z)) })
        ++
        gdisc.map (fun d =>
          { d with vals := fun x =>
              let y := f w x
              let z := d.vals x
              ((y, z.1), (y, z.2)) })) := by

  unfold HasParamRevFDerivWithDiscAt
  have : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry_proof
  have : ∀ x, IsContinuousLinearMap R (g' x).2 := sorry_proof

  constructor
  · convert Prod.mk.arg_fstsnd.HasParamFDerivWithDiscAt_rule _ _ _ _ (hf.1) (hg.1) sorry_proof
    · fun_trans
    · fun_trans
    · simp[List.map_append]; rfl
  · simp [hf.2, hg.2]



theorem comp1_differentiable_discs_rule
    (f : W → Y → Z) (hf : Differentiable R (fun (w,y) => f w y))
    (g : W → X → Y) (w : W)
    {g' disc}
    (hg : HasParamRevFDerivWithDiscAt R g w g' disc) :
    HasParamRevFDerivWithDiscAt (R:=R) (fun w x => f w (g w x)) w
      (f' := fun x =>
         let ydg := g' x
         let zdf := revFDeriv R (fun (w,y) => f w y) (w,ydg.1)
         (zdf.1,
          fun dz =>
            let dwy := zdf.2 dz
            let dw := ydg.2 dwy.2
            dwy.1 + dw))
      (disc := disc.map fun ⟨vals,speedGrad,d⟩ =>
        { vals := fun x =>
            let y := vals x
            (f w y.1, f w y.2)
          speedGrad := speedGrad
          discontinuity := d }) :=

  comp_differentiable_discs_rule f g w hf hg



theorem comp2_differentiable_discs_rule
    (f : W → Y₁ → Y₂ → Z) (hf : Differentiable R (fun (w,y₁,y₂) => f w y₁ y₂))
    (g₁ : W → X → Y₁) (g₂ : W → X → Y₂) (w : W)
    {g₁' dg₁} {g₂' dg₂}
    (hg₁ : HasParamRevFDerivWithDiscAt R g₁ w g₁' dg₁)
    (hg₂ : HasParamRevFDerivWithDiscAt R g₂ w g₂' dg₂)
    (hdisjoint : AlmostDisjoint dg₁.getDiscontinuity dg₂.getDiscontinuity μH[finrank ℝ X - (1:ℕ)]) :
    HasParamRevFDerivWithDiscAt (R:=R) (fun w x => f w (g₁ w x) (g₂ w x)) w
      (f' := fun x =>
         let ydg₁ := g₁' x
         let ydg₂ := g₂' x
         let zdf := revFDeriv R (fun (w,y₁,y₂) => f w y₁ y₂) (w,ydg₁.1,ydg₂.1)
         (zdf.1, fun dz =>
           let dwy := zdf.2 dz
           let dw₁ := ydg₁.2 dwy.2.1
           let dw₂ := ydg₂.2 dwy.2.2
           dwy.1 + dw₁ + dw₂))
      (disc :=
        (dg₁.map fun d => { d with
          vals := fun x =>
           let y₁ := d.vals x
           let y₂ := g₂ w x
           (f w y₁.1 y₂, f w y₁.2 y₂) })
        ++
        (dg₂.map fun d => { d with
          vals := fun x =>
           let y₁ := g₁ w x
           let y₂ := d.vals x
           (f w y₁ y₂.1, f w y₁ y₂.2) })) := by

  convert comp_differentiable_discs_rule (R:=R) (fun w (y:Y₁×Y₂) => f w y.1 y.2) (fun w x => (g₁ w x, g₂ w x)) w
    hf (by gtrans (disch:=first | fun_prop | assumption))
  · fun_trans [hg₁.2,hg₂.2]; ac_rfl
  · simp[List.map_append]; rfl


end HasParamRevFDerivWithDiscAt
open HasParamRevFDerivWithDiscAt


@[gtrans]
def Prod.fst.arg_self.HasParamRevFDerivWithDiscAt_rule :=
  (comp1_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Y) (fun _ yz => yz.1) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def Prod.snd.arg_self.HasParamRevFDerivWithDiscAt_rule :=
  (comp1_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Z) (fun _ yz => yz.2) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def HAdd.hAdd.arg_a0a1.HasParamRevFDerivWithDiscAt_rule :=
  (comp2_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ + y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def HSub.hSub.arg_a0a1.HasParamRevFDerivWithDiscAt_rule :=
  (comp2_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ - y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def Neg.neg.arg_a0.HasParamRevFDerivWithDiscAt_rule :=
  (comp1_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y:=Y) (Z:=Y) (fun _ y => - y) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def HMul.hMul.arg_a0a1.HasParamRevFDerivWithDiscAt_rule :=
  (comp2_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=R) (Z:=R) (fun _ y₁ y₂ => y₁ * y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def HPow.hPow.arg_a0.HasParamRevFDerivWithDiscAt_rule (n:ℕ) :=
  (comp1_differentiable_discs_rule (R:=R) (X:=X) (Y:=R) (Z:=R) (fun (w : W) y => y^n) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
def HSMul.hSMul.arg_a0a1.HasParamRevFDerivWithDiscAt_rule :=
  (comp2_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ • y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[gtrans]
theorem HDiv.hDiv.arg_a0a1.HasParamRevFDerivWithDiscAt_rule
    (f g : W → X → R) (w : W)
    {f' df} {g' dg}
    (hf : HasParamRevFDerivWithDiscAt R f w f' df)
    (hg : HasParamRevFDerivWithDiscAt R g w g' dg)
    (hdisjoint : AlmostDisjoint df.getDiscontinuity dg.getDiscontinuity μH[finrank ℝ X - (1:ℕ)])
    (hg' : ∀ x, g w x ≠ 0) :
    HasParamRevFDerivWithDiscAt (R:=R) (fun w x => f w x / g w x) w
      (f' := fun x =>
        let ydf := f' x
        let zdg := g' x
        (ydf.1 / zdg.1,
         fun dy =>
           (zdg.1^2)⁻¹ • (zdg.1 • ydf.2 dy - ydf.1 • zdg.2 dy)))
      (disc :=
        df.map (fun d =>
          { d with vals := fun x =>
              let y := d.vals x
              let z := g w x
              (y.1/z, y.2/z) })
        ++
        dg.map (fun d =>
          { d with vals := fun x =>
              let y := f w x
              let z := d.vals x
              (y/z.1, y/z.2) })) := by

  unfold HasParamRevFDerivWithDiscAt
  have : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry_proof
  have : ∀ x, IsContinuousLinearMap R (g' x).2 := sorry_proof

  constructor
  · convert HDiv.hDiv.arg_a0a1.HasParamFDerivWithDiscAt_rule _ _ _ _ (hf.1) (hg.1) sorry_proof hg'
    · fun_trans [hf.2,hg.2]; ring
    · simp[List.map_append]; rfl
  · simp [hf.2, hg.2]


@[gtrans]
theorem ite.arg_te.HasParamRevFDerivWithDiscAt_rule
    (f g : W → X → Y) (w : W)
    {c : W → X → Prop} [∀ w x, Decidable (c w x)]
    {f' df} {g' dg}
    (hf : HasParamRevFDerivWithDiscAt R f w f' df)
    (hg : HasParamRevFDerivWithDiscAt R g w g' dg)
    (hdisjoint : AlmostDisjointList (frontier {x | c w x} :: df.getDiscontinuities ++ dg.getDiscontinuities) μH[finrank ℝ X - (1:ℕ)]) :
    HasParamRevFDerivWithDiscAt (R:=R) (fun w x => if c w x then f w x else g w x) w
      (f' := fun x => if c w x then f' x else g' x)
      (disc :=
        {vals := fun x => (f w x, g w x)
         speedGrad := frontierGrad R (fun w => {x | c w x}) w
         discontinuity := frontier {x | c w x}}
        ::
        df.map (fun d => {d with discontinuity := d.discontinuity ∩ {x | c w x}})
        ++
        dg.map (fun d => {d with discontinuity := d.discontinuity ∩ {x | ¬c w x}})) := by

  unfold HasParamRevFDerivWithDiscAt
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor
  · convert ite.arg_te.HasParamFDerivWithDiscAt_rule _ _ _ _ (hf.1) (hg.1) sorry_proof
    · fun_trans; simp only [hf.2, hg.2, Tactic.if_pull]
    · simp[List.map_append,simp_core]
      constructor
      · simp[frontierGrad]; simp (disch:=sorry_proof) only [adjoint_inner_left]; simp [Inner.inner]
      · rfl
  · dsimp; intros; split_ifs <;> simp [hf.2, hg.2]
