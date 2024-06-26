import SciLean.Core.FunctionTransformations.RevFDeriv
import SciLean.Core.Integral.HasParamDerivWithJumps
import SciLean.Tactic.IfPull

import Mathlib.Lean.CoreM

open MeasureTheory

namespace SciLean

variable
  {R : Type} [RealScalar R] [MeasureSpace R] [BorelSpace R]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace R W] [NormedSpace ℝ W] [CompleteSpace W]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace R Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Y₁ : Type} [NormedAddCommGroup Y₁] [AdjointSpace R Y₁] [NormedSpace ℝ Y₁] [CompleteSpace Y₁]
  {Y₂ : Type} [NormedAddCommGroup Y₂] [AdjointSpace R Y₂] [NormedSpace ℝ Y₂] [CompleteSpace Y₂]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace R Z] [NormedSpace ℝ Z] [CompleteSpace Z]

set_default_scalar R



----------------------------------------------------------------------------------------------------

theorem adjoint_integral (f : X → Y → Z) (μ : Measure X) :
  adjoint R (fun y => ∫ x, f x y ∂μ)
  =
  fun y' => ∫ x, adjoint R (f x) y' ∂μ := sorry_proof

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


----------------------------------------------------------------------------------------------------

variable (R)
open Classical in
noncomputable
def frontierGrad (A : W → Set X) (w : W) (x : X) : W :=
  adjoint R (fun dw => frontierSpeed' R A w dw x) 1


def HasParamRevFDerivWithJumpsAt (f : W → X → Y) (w : W)
    (f' : X → Y×(Y→W))
    (I : Type)
    /- Values of `f` on both sides of jump discontinuity.

    The first value is in the positive noramal direction and the second value in the negative
    normal direction.

    The orientation of the normal is arbitrary but fixed as `jumpVals` and `jumpSpeed` depend on it. -/
    (jumpVals : I → X → Y×Y)
    /- Normal speed of the jump discontinuity. -/
    (jumpGrad : I → X → W)
    /- Jump discontinuities of `f`. -/
    (jump : I → Set X)  :=
  HasParamFDerivWithJumpsAt R f w
    (fun (dw : W) (x : X) => adjoint R (fun dy => ⟪(f' x).2 dy, dw⟫) 1)
    I jumpVals
    (fun (i : I) (dw : W) (x : X) => ⟪jumpGrad i x, dw⟫)
    jump
  ∧
  ∀ x, (f' x).1 = f w x

variable {R}

open FiniteDimensional

@[fun_trans]
theorem revFDeriv_under_integral
    (f : W → X → Y) (w : W) (μ : Measure X)
    {I} [hI : IndexType I] {f' df s S}
    (hf : HasParamRevFDerivWithJumpsAt R f w f' I df s S) :
    (revFDeriv R (fun w' => ∫ x, f w' x ∂μ) w)
    =
    let val := ∫ x, f w x ∂μ
    (val, fun dy =>
      let interior := ∫ x, (f' x).2 dy ∂μ
      let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
      let shocks := ∑ i, ∫ x in S i, (⟪(df i x).1 - (df i x).2, dy⟫ * density x) • s i x ∂μH[finrank R X - (1:ℕ)]
      interior + shocks) := by

  unfold revFDeriv
  simp only [fderiv_under_integral R f w _ μ hf.1]
  have hf' : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry_proof -- this should be part of hf
  fun_trans (disch:=apply hf') [adjoint_sum,adjoint_integral,adjoint_adjoint,smul_smul]




----------------------------------------------------------------------------------------------------
-- Lambda rules ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

namespace HasParamRevFDerivWithJumpsAt

@[aesop unsafe]
theorem smooth_rule
    (w : W)
    (f : W → X → Y) (hf : ∀ x, DifferentiableAt R (f · x) w) :
    HasParamRevFDerivWithJumpsAt R f w (fun x => revFDeriv R (f · x) w) Empty 0 0 (fun _ => ∅) :=

  sorry_proof



@[aesop unsafe]
theorem comp_smooth_jumps_rule
    (f : W → Y → Z) (g : W → X → Y) (w : W)
    {I g' bg sg Sg}
    (hf : Differentiable R (fun (w,y) => f w y))
    (hg : HasParamRevFDerivWithJumpsAt R g w g' I bg sg Sg) :
    HasParamRevFDerivWithJumpsAt (R:=R) (fun w x => f w (g w x)) w
      (f' := fun x =>
         let ydg := g' x
         let zdf := revFDeriv R (fun (w,y) => f w y) (w,ydg.1)
         (zdf.1,
          fun dz =>
            let dwy := zdf.2 dz
            let dw := ydg.2 dwy.2
            dwy.1 + dw))
      (I := I)
      (jumpVals := fun i x =>
         let y := bg i x
         (f w y.1, f w y.2))
      (jumpGrad := sg)
      (jump := Sg) := by

  unfold HasParamRevFDerivWithJumpsAt
  constructor
  . convert HasParamFDerivWithJumpsAt.comp_smooth_jumps_rule R f g w hf hg.1
    rename_i w x
    have hg' : IsContinuousLinearMap R (g' x).2 := by sorry
    simp [revFDeriv, hg.2]
    fun_trans
    simp (disch:=fun_prop) [adjoint_adjoint]
    sorry
  . simp [revFDeriv,hg.2]


@[aesop safe]
theorem _root_.Prod.mk.arg_fstsnd.HasParamRevFDerivWithJumpsAt_rule
    (f : W → X → Y) (g : W → X → Z) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamRevFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamRevFDerivWithJumpsAt R g w g' J bg sg Sg)
    /- (hIJ : DisjointJumps R Sf Sg) -/ :
    HasParamRevFDerivWithJumpsAt (R:=R) (fun w x => (f w x, g w x)) w
      (f' := fun x =>
        let ydf := f' x
        let zdg := g' x
        ((ydf.1,zdg.1), fun dyz => ydf.2 dyz.1 + zdg.2 dyz.2))
      (I := I⊕J)
      (jumpVals := Sum.elim
           (fun i x =>
             let (y₁, y₂) := bf i x
             let z := g w x
             ((y₁,z), (y₂,z)))
           (fun j x =>
             let y := f w x
             let (z₁, z₂) := bg j x
             ((y,z₁), (y,z₂))))
      (jumpGrad := Sum.elim sf sg)
      (jump := Sum.elim Sf Sg) := by

  unfold HasParamRevFDerivWithJumpsAt
  have : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry
  have : ∀ x, IsContinuousLinearMap R (g' x).2 := sorry

  constructor
  . convert Prod.mk.arg_fstsnd.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1)
    . fun_trans
    . fun_trans
    . rename_i i _ _; induction i <;> simp
  . simp [hf.2, hg.2]


@[aesop unsafe]
theorem comp1_smooth_jumps_rule
    (f : W → Y → Z) (hf : Differentiable R (fun (w,y) => f w y))
    (g : W → X → Y) (w : W)
    {I g' bg sg Sg}
    (hg : HasParamRevFDerivWithJumpsAt R g w g' I bg sg Sg) :
    HasParamRevFDerivWithJumpsAt (R:=R) (fun w x => f w (g w x)) w
      (f' := fun x =>
         let ydg := g' x
         let zdf := revFDeriv R (fun (w,y) => f w y) (w,ydg.1)
         (zdf.1,
          fun dz =>
            let dwy := zdf.2 dz
            let dw := ydg.2 dwy.2
            dwy.1 + dw))
      (I := I)
      (jumpVals := fun i x =>
         let y := bg i x
         (f w y.1, f w y.2))
      (jumpGrad := sg)
      (jump := Sg) :=

  comp_smooth_jumps_rule f g w hf hg


@[aesop unsafe]
theorem comp2_smooth_jumps_rule
    (f : W → Y₁ → Y₂ → Z) (hf : Differentiable R (fun (w,y₁,y₂) => f w y₁ y₂))
    (g₁ : W → X → Y₁) (g₂ : W → X → Y₂) (w : W)
    {I₁ g₁' bg₁ sg₁ Sg₁} {I₂ g₂' bg₂ sg₂ Sg₂}
    (hg₁ : HasParamRevFDerivWithJumpsAt R g₁ w g₁' I₁ bg₁ sg₁ Sg₁)
    (hg₂ : HasParamRevFDerivWithJumpsAt R g₂ w g₂' I₂ bg₂ sg₂ Sg₂) :
    HasParamRevFDerivWithJumpsAt (R:=R) (fun w x => f w (g₁ w x) (g₂ w x)) w
      (f' := fun x =>
         let ydg₁ := g₁' x
         let ydg₂ := g₂' x
         let zdf := revFDeriv R (fun (w,y₁,y₂) => f w y₁ y₂) (w,ydg₁.1,ydg₂.1)
         (zdf.1, fun dz =>
           let dwy := zdf.2 dz
           let dw₁ := ydg₁.2 dwy.2.1
           let dw₂ := ydg₂.2 dwy.2.2
           dwy.1 + dw₁ + dw₂))
      (I := I₁⊕I₂)
      (jumpVals := Sum.elim
        (fun i₁ x =>
           let y₁ := bg₁ i₁ x
           let y₂ := g₂ w x
           (f w y₁.1 y₂, f w y₁.2 y₂))
        (fun i₂ x =>
           let y₁ := g₁ w x
           let y₂ := bg₂ i₂ x
           (f w y₁ y₂.1, f w y₁ y₂.2)))
      (jumpGrad := Sum.elim sg₁ sg₂)
      (jump := Sum.elim Sg₁ Sg₂) := by

  convert comp_smooth_jumps_rule (R:=R) (fun w (y:Y₁×Y₂) => f w y.1 y.2) (fun w x => (g₁ w x, g₂ w x)) w
    hf (by  aesop (config := {enableSimp := false}))
  . fun_trans [hg₁.2,hg₂.2]; ac_rfl
  . rename_i i x; induction i <;> simp


end HasParamRevFDerivWithJumpsAt
open HasParamRevFDerivWithJumpsAt


@[aesop safe]
def Prod.fst.arg_self.HasParamRevFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Y) (fun _ yz => yz.1) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
def Prod.snd.arg_self.HasParamRevFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Z) (fun _ yz => yz.2) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
def HAdd.hAdd.arg_a0a1.HasParamRevFDerivWithJumpsAt_rule :=
  (comp2_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ + y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
def HSub.hSub.arg_a0a1.HasParamRevFDerivWithJumpsAt_rule :=
  (comp2_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ - y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
def Neg.neg.arg_a0.HasParamRevFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=Y) (Z:=Y) (fun _ y => - y) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
def HMul.hMul.arg_a0a1.HasParamRevFDerivWithJumpsAt_rule :=
  (comp2_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=R) (Z:=R) (fun _ y₁ y₂ => y₁ * y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
def HSMul.hSMul.arg_a0a1.HasParamRevFDerivWithJumpsAt_rule :=
  (comp2_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ • y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
theorem HDiv.hDiv.arg_a0a1.HasParamRevFDerivWithJumpsAt_rule
    (f g : W → X → R) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamRevFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamRevFDerivWithJumpsAt R g w g' J bg sg Sg) :
    HasParamRevFDerivWithJumpsAt (R:=R) (fun w x => f w x / g w x) w
      (f' := fun x =>
        let ydf := f' x
        let zdg := g' x
        (ydf.1 / zdg.1,
         fun dy =>
           (zdg.1^2)⁻¹ • (zdg.1 • ydf.2 dy - ydf.1 • zdg.2 dy)))
      (I:=I⊕J)
      (jumpVals := Sum.elim
        (fun i x =>
          let y := bf i x
          let z := g w x
          ((y.1/z), (y.2/z)))
        (fun j x =>
          let y := f w x
          let z := bg j x
          ((y/z.1), (y/z.2))))
      (jumpGrad := Sum.elim sf sg)
      (jump := Sum.elim Sf Sg) := by

  unfold HasParamRevFDerivWithJumpsAt
  have : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry
  have : ∀ x, IsContinuousLinearMap R (g' x).2 := sorry

  constructor
  . convert HDiv.hDiv.arg_a0a1.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1) sorry
    . fun_trans [hf.2,hg.2]; ring
    . rename_i i _ _; induction i <;> simp
  . simp [hf.2, hg.2]


@[aesop safe]
theorem ite.arg_te.HasParamRevFDerivWithJumpsAt_rule
    (f g : W → X → Y) (w : W)
    {c : W → X → Prop} [∀ w x, Decidable (c w x)]
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamRevFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamRevFDerivWithJumpsAt R g w g' J bg sg Sg) :
    HasParamRevFDerivWithJumpsAt (R:=R) (fun w x => if c w x then f w x else g w x) w
      (f' := fun x => if c w x then f' x else g' x)
      (I:=Unit⊕I⊕J)
      (jumpVals :=
        Sum.elim
         (fun _ x => (f w x, g w x)) <|
        Sum.elim bf bg)
      (jumpGrad := Sum.elim (fun _ => frontierGrad R (fun w => {x | ¬c w x}) w) (Sum.elim sf sg))
      (jump := Sum.elim (fun _ => frontier {x | c w x}) <|
               Sum.elim
                 (fun i => Sf i ∩ {x | c w x})
                 (fun j => Sg j ∩ {x | ¬c w x})) := by

  unfold HasParamRevFDerivWithJumpsAt
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor
  . convert ite.arg_te.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1)
    . fun_trans; simp only [hf.2, hg.2, Tactic.if_pull]
    . rename_i i w x
      induction i
      case inl i => simp[frontierGrad]; simp (disch:=sorry) only [adjoint_inner_left]; simp [Inner.inner]
      case inr j => induction j <;> simp
  . simp [hf.2, hg.2,Tactic.if_pull]



----------------------------------------------------------------------------------------------------
-- Trigonometric functions -------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open Scalar in
@[aesop safe]
def Scalar.sin.arg_a0.HasParamRevFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=R) (Z:=R) (fun _ y => sin y) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff


open Scalar in
@[aesop safe]
def Scalar.cos.arg_a0.HasParamRevFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=R) (Z:=R) (fun _ y => cos y) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff
