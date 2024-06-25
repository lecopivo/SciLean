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
  adjoint R (fun dw => frontierSpeed R A w dw x) 1


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
      let shocks := ∑ i, ∫ x in S i, (⟪(df i x).1 - (df i x).2, dy⟫ * density x) • s i x ∂μH[finrank R X - 1]
      interior + shocks) := by

  unfold revFDeriv
  simp only [fderiv_under_integral R f w μ hf.1]
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


end HasParamRevFDerivWithJumpsAt
open HasParamRevFDerivWithJumpsAt



@[aesop safe]
theorem Prod.mk.arg_fstsnd.HasParamRevFDerivWithJumpsAt_rule
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


@[aesop safe]
theorem Prod.fst.arg_self.HasParamRevFDerivWithJumpsAt_rule
    (f : W → X → Y×Z) (w : W)
    {I f' bf sf Sf}
    (hf : HasParamRevFDerivWithJumpsAt R f w f' I bf sf Sf) :
    HasParamRevFDerivWithJumpsAt (R:=R) (fun w x => (f w x).1) w
      (f':= fun x =>
         let ydf := f' x
         (ydf.1.1, fun dy => ydf.2 (dy,0)))
      (I := I)
      (jumpVals := fun i x => let y := bf i x; (y.1.1, y.2.1))
      (jumpGrad := sf)
      (jump := Sf) := by

  unfold HasParamRevFDerivWithJumpsAt
  have : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry

  constructor
  . convert Prod.fst.arg_self.HasParamFDerivWithJumpsAt_rule _ _  _ (hf.1)
    . fun_trans
  . simp [hf.2]


@[aesop safe]
theorem Prod.snd.arg_self.HasParamRevFDerivWithJumpsAt_rule
    (f : W → X → Y×Z) (w : W)
    {I f' bf sf Sf}
    (hf : HasParamRevFDerivWithJumpsAt R f w f' I bf sf Sf) :
    HasParamRevFDerivWithJumpsAt (R:=R) (fun w x => (f w x).2) w
      (f':= fun x =>
         let ydf := f' x
         (ydf.1.2, fun dz => ydf.2 (0,dz)))
      (I := I)
      (jumpVals := fun i x => let y := bf i x; (y.1.2, y.2.2))
      (jumpGrad := sf)
      (jump := Sf) := by

  unfold HasParamRevFDerivWithJumpsAt
  have : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry

  constructor
  . convert Prod.snd.arg_self.HasParamFDerivWithJumpsAt_rule _ _  _ (hf.1)
    . fun_trans
  . simp [hf.2]


@[aesop safe]
theorem HAdd.hAdd.arg_a0a1.HasParamRevFDerivWithJumpsAt_rule
    (f g : W → X → Y) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamRevFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamRevFDerivWithJumpsAt R g w g' J bg sg Sg) :
    HasParamRevFDerivWithJumpsAt (R:=R) (fun w x => f w x + g w x) w
      (f' := fun x =>
        let ydf := f' x
        let zdg := g' x
        (ydf.1 + zdg.1,
         fun dy =>
           ydf.2 dy + zdg.2 dy))
      (I:=I⊕J)
      (jumpVals := Sum.elim
        (fun i x =>
          let (y₁, y₂) := bf i x
          let z := g w x
          ((y₁+z), (y₂+z)))
        (fun j x =>
          let y := f w x
          let (z₁, z₂) := bg j x
          ((y+z₁), (y+z₂))))
      (jumpGrad := Sum.elim sf sg)
      (jump := Sum.elim Sf Sg) := by

  unfold HasParamRevFDerivWithJumpsAt
  have : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry
  have : ∀ x, IsContinuousLinearMap R (g' x).2 := sorry

  constructor
  . convert HAdd.hAdd.arg_a0a1.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1)
    . fun_trans
    . rename_i i _ _; induction i <;> simp
  . simp [hf.2, hg.2]



@[aesop safe]
theorem HSub.hSub.arg_a0a1.HasParamRevFDerivWithJumpsAt_rule
    (f g : W → X → Y) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamRevFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamRevFDerivWithJumpsAt R g w g' J bg sg Sg) :
    HasParamRevFDerivWithJumpsAt (R:=R) (fun w x => f w x - g w x) w
      (f' := fun x =>
        let ydf := f' x
        let zdg := g' x
        (ydf.1 - zdg.1,
         fun dy =>
           ydf.2 dy - zdg.2 dy))
      (I:=I⊕J)
      (jumpVals := Sum.elim
        (fun i x =>
          let (y₁, y₂) := bf i x
          let z := g w x
          ((y₁-z), (y₂-z)))
        (fun j x =>
          let y := f w x
          let (z₁, z₂) := bg j x
          ((y-z₁), (y-z₂))))
      (jumpGrad := Sum.elim sf sg)
      (jump := Sum.elim Sf Sg) := by

  unfold HasParamRevFDerivWithJumpsAt
  have : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry
  have : ∀ x, IsContinuousLinearMap R (g' x).2 := sorry

  constructor
  . convert HSub.hSub.arg_a0a1.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1)
    . fun_trans
    . rename_i i _ _; induction i <;> simp
  . simp [hf.2, hg.2]



@[aesop safe]
theorem Neg.neg.arg_a0.HasParamRevFDerivWithJumpsAt_rule
    (f : W → X → Y) (w : W)
    {I f' bf sf Sf}
    (hf : HasParamRevFDerivWithJumpsAt R f w f' I bf sf Sf) :
    HasParamRevFDerivWithJumpsAt (R:=R) (fun w x => -f w x) w
      (f':= fun x =>
         let ydf := f' x
         (-ydf.1, fun dy => - ydf.2 dy))
      (I := I)
      (jumpVals := fun i x => -bf i x)
      (jumpGrad := sf)
      (jump := Sf) := by

  unfold HasParamRevFDerivWithJumpsAt
  have : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry

  constructor
  . convert Neg.neg.arg_a0.HasParamFDerivWithJumpsAt_rule _ _  _ (hf.1)
    . fun_trans
  . simp [hf.2]


@[aesop safe]
theorem HMul.hMul.arg_a0a1.HasParamRevFDerivWithJumpsAt_rule
    (f g : W → X → R) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamRevFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamRevFDerivWithJumpsAt R g w g' J bg sg Sg) :
    HasParamRevFDerivWithJumpsAt (R:=R) (fun w x => f w x * g w x) w
      (f' := fun x =>
        let ydf := f' x
        let zdg := g' x
        (ydf.1 * zdg.1,
         fun dy =>
           zdg.1 • ydf.2 dy + ydf.1 • zdg.2 dy))
      (I:=I⊕J)
      (jumpVals := Sum.elim
        (fun i x =>
          let y := bf i x
          let z := g w x
          ((y.1*z), (y.2*z)))
        (fun j x =>
          let y := f w x
          let z := bg j x
          ((y*z.1), (y*z.2))))
      (jumpGrad := Sum.elim sf sg)
      (jump := Sum.elim Sf Sg) := by

  unfold HasParamRevFDerivWithJumpsAt
  have : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry
  have : ∀ x, IsContinuousLinearMap R (g' x).2 := sorry

  constructor
  . convert HMul.hMul.arg_a0a1.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1)
    . fun_trans [hf.2,hg.2]; ac_rfl
    . rename_i i _ _; induction i <;> simp
  . simp [hf.2, hg.2]


@[aesop safe]
theorem HSMul.hSMul.arg_a0a1.HasParamRevFDerivWithJumpsAt_rule
    (f : W → X → R) (g : W → X → Y) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamRevFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamRevFDerivWithJumpsAt R g w g' J bg sg Sg) :
    HasParamRevFDerivWithJumpsAt (R:=R) (fun w x => f w x • g w x) w
      (f' := fun x =>
        let ydf := f' x
        let zdg := g' x
        (ydf.1 • zdg.1,
         fun dy =>
           ydf.2 ⟪zdg.1,dy⟫ + ydf.1 • zdg.2 dy))
      (I:=I⊕J)
      (jumpVals := Sum.elim
        (fun i x =>
          let y := bf i x
          let z := g w x
          ((y.1•z), (y.2•z)))
        (fun j x =>
          let y := f w x
          let z := bg j x
          ((y•z.1), (y•z.2))))
      (jumpGrad := Sum.elim sf sg)
      (jump := Sum.elim Sf Sg) := by

  unfold HasParamRevFDerivWithJumpsAt
  have : ∀ x, IsContinuousLinearMap R (f' x).2 := sorry
  have : ∀ x, IsContinuousLinearMap R (g' x).2 := sorry

  constructor
  . convert HSMul.hSMul.arg_a0a1.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1)
    . fun_trans [hf.2,hg.2]
    . rename_i i _ _; induction i <;> simp
  . simp [hf.2, hg.2]


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
