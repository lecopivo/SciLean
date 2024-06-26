import SciLean.Core.FunctionTransformations.FwdFDeriv
import SciLean.Core.Integral.HasParamDerivWithJumps
import SciLean.Tactic.IfPull

set_option linter.unusedVariables false

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R] [MeasureSpace R]
  {W} [NormedAddCommGroup W] [NormedSpace R W]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Y₁} [NormedAddCommGroup Y₁] [NormedSpace R Y₁] [NormedSpace ℝ Y₁]
  {Y₂} [NormedAddCommGroup Y₂] [NormedSpace R Y₂] [NormedSpace ℝ Y₂]
  {Z} [NormedAddCommGroup Z] [NormedSpace R Z] [NormedSpace ℝ Z] [CompleteSpace Z]

set_default_scalar R


variable (R)
def HasParamFwdFDerivWithJumpsAt (f : W → X → Y) (w : W)
    (f' : W → X → Y×Y)
    (I : Type)
    /- Values of `f` on both sides of jump discontinuity.

    The first value is in the positive noramal direction and the second value in the negative
    normal direction.

    The orientation of the normal is arbitrary but fixed as `jumpVals` and `jumpSpeed` depend on it. -/
    (jumpVals : I → X → Y×Y)
    /- Normal speed of the jump discontinuity. -/
    (jumpSpeed : I → W → X → R)
    /- Jump discontinuities of `f`. -/
    (jump : I → Set X) : Prop :=
  HasParamFDerivWithJumpsAt R f w (fun w x => (f' w x).2) I jumpVals jumpSpeed jump
  ∧
  ∀ dw x, (f' dw x).1 = f w x


def HasParamFwdFDerivWithJumps (f : W → X → Y)
    (f' : W → W → X → Y×Y)
    (I : Type)
    (jumpVals : I → W → X → Y×Y)
    (jumpSpeed : I → W → W → X → R)
    (jump : I → W → Set X) := ∀ w : W, HasParamFwdFDerivWithJumpsAt R f w (f' w) I (jumpVals · w) (jumpSpeed · w) (jump · w)

variable {R}



open FiniteDimensional
@[fun_trans]
theorem fwdFDeriv_under_integral
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  (f : W → X → Y) (w : W) (μ : Measure X)
  {I} [hI : IndexType I] {f' df s S}
  (hf : HasParamFwdFDerivWithJumpsAt R f w f' I df s S)
  /- (hμ : μ ≪ volume) -/ :
  (fwdFDeriv R (fun w' => ∫ x, f w' x ∂μ) w)
  =
  fun dw =>
    let interior := ∫ x, f' dw x ∂μ
    let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
    let shocks := ∑ i, ∫ x in S i, (s i dw x * density x) • ((df i x).1 - (df i x).2) ∂μH[finrank R X - (1:ℕ)]
    (interior.1, interior.2 + shocks) := by

  unfold fwdFDeriv
  funext dw; ext
  . simp only [fst_integral (hf := sorry_proof), hf.2]
  . simp only [fderiv_under_integral R f w dw μ hf.1, add_left_inj, snd_integral (hf:=sorry_proof)]



----------------------------------------------------------------------------------------------------
-- Lambda rules ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

namespace HasParamFwdDerivWithJumps

@[aesop unsafe]
theorem smooth_rule
    (f : W → X → Y) (w : W) (hf : ∀ x, DifferentiableAt R (f · x) w) :
    HasParamFwdFDerivWithJumpsAt (R:=R) f w
      (f' := fun dw x => fwdFDeriv R (f · x) w dw)
      (I := Empty)
      (jumpVals := 0)
      (jumpSpeed := 0)
      (jump := fun _ => ∅) := by

  unfold HasParamFwdFDerivWithJumpsAt
  constructor
  . apply HasParamFDerivWithJumpsAt.smooth_rule R w f hf
  . simp only [fwdFDeriv, implies_true]


@[aesop unsafe]
theorem comp_smooth_jumps_rule
    (f : W → Y → Z) (g : W → X → Y) (w : W)
    {I g' bg sg Sg}
    (hf : Differentiable R (fun (w,y) => f w y))
    (hg : HasParamFwdFDerivWithJumpsAt R g w g' I bg sg Sg) :
    HasParamFwdFDerivWithJumpsAt (R:=R) (fun w x => f w (g w x)) w
      (f' := fun dw x =>
         let ydy := g' dw x
         let zdz := fwdFDeriv R (fun (w,y) => f w y) (w,ydy.1) (dw,ydy.2)
         zdz)
      (I := I)
      (jumpVals := fun i x =>
         let y := bg i x
         (f w y.1, f w y.2))
      (jumpSpeed := sg)
      (jump := Sg) := by

  unfold HasParamFwdFDerivWithJumpsAt
  constructor
  . convert HasParamFDerivWithJumpsAt.comp_smooth_jumps_rule R f g w hf hg.1
    simp [fwdFDeriv, hg.2]
  . simp [fwdFDeriv,hg.2]



@[aesop safe]
theorem _root_.Prod.mk.arg_fstsnd.HasParamFwdFDerivWithJumpsAt_rule
    (f : W → X → Y) (g : W → X → Z) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamFwdFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamFwdFDerivWithJumpsAt R g w g' J bg sg Sg)
    /- (hIJ : DisjointJumps R Sf Sg) -/ :
    HasParamFwdFDerivWithJumpsAt (R:=R) (fun w x => (f w x, g w x)) w
      (f' := fun dw x =>
        let ydy := f' dw x
        let zdz := g' dw x
        ((ydy.1,zdz.1), (ydy.2, zdz.2)))
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
      (jumpSpeed := Sum.elim sf sg)
      (jump := Sum.elim Sf Sg) := by

  unfold HasParamFwdFDerivWithJumpsAt
  constructor
  . exact Prod.mk.arg_fstsnd.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1)
  . simp [hf.2, hg.2]




@[aesop unsafe]
theorem comp1_smooth_jumps_rule
    (f : W → Y → Z) (hf : Differentiable R (fun (w,y) => f w y))
    (g : W → X → Y) (w : W)
    {I g' bg sg Sg}
    (hg : HasParamFwdFDerivWithJumpsAt R g w g' I bg sg Sg) :
    HasParamFwdFDerivWithJumpsAt (R:=R) (fun w x => f w (g w x)) w
      (f' := fun dw x =>
         let ydy := g' dw x
         let zdz := fwdFDeriv R (fun (w,y) => f w y) (w,ydy.1) (dw,ydy.2)
         zdz)
      (I := I)
      (jumpVals := fun i x =>
         let y := bg i x
         (f w y.1, f w y.2))
      (jumpSpeed := sg)
      (jump := Sg) :=

  comp_smooth_jumps_rule f g w hf hg


@[aesop unsafe]
theorem comp2_smooth_jumps_rule
    (f : W → Y₁ → Y₂ → Z) (hf : Differentiable R (fun (w,y₁,y₂) => f w y₁ y₂))
    (g₁ : W → X → Y₁) (g₂ : W → X → Y₂) (w : W)
    {I₁ g₁' bg₁ sg₁ Sg₁} {I₂ g₂' bg₂ sg₂ Sg₂}
    (hg₁ : HasParamFwdFDerivWithJumpsAt R g₁ w g₁' I₁ bg₁ sg₁ Sg₁)
    (hg₂ : HasParamFwdFDerivWithJumpsAt R g₂ w g₂' I₂ bg₂ sg₂ Sg₂) :
    HasParamFwdFDerivWithJumpsAt (R:=R) (fun w x => f w (g₁ w x) (g₂ w x)) w
      (f' := fun dw x =>
         let ydy₁ := g₁' dw x
         let ydy₂ := g₂' dw x
         let zdz := fwdFDeriv R (fun (w,y₁,y₂) => f w y₁ y₂) (w,ydy₁.1,ydy₂.1) (dw,ydy₁.2,ydy₂.2)
         zdz)
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
      (jumpSpeed := Sum.elim sg₁ sg₂)
      (jump := Sum.elim Sg₁ Sg₂) := by

  convert comp_smooth_jumps_rule (R:=R) (fun w (y:Y₁×Y₂) => f w y.1 y.2) (fun w x => (g₁ w x, g₂ w x)) w
    hf (by  aesop (config := {enableSimp := false}))
  . rename_i i x; induction i <;> simp


end HasParamFwdDerivWithJumps
open HasParamFwdDerivWithJumps


@[aesop safe]
def Prod.fst.arg_self.HasParamFwdFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Y) (fun _ yz => yz.1) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
def Prod.snd.arg_self.HasParamFwdFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Z) (fun _ yz => yz.2) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
def HAdd.hAdd.arg_a0a1.HasParamFwdFDerivWithJumpsAt_rule :=
  (comp2_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ + y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
def HSub.hSub.arg_a0a1.HasParamFwdFDerivWithJumpsAt_rule :=
  (comp2_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ - y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
def Neg.neg.arg_a0.HasParamFwdFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (X:=X) (Y:=Y) (Z:=Y) (fun (w : W) y => - y) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
def HMul.hMul.arg_a0a1.HasParamFwdFDerivWithJumpsAt_rule :=
  (comp2_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=R) (Z:=R) (fun _ y₁ y₂ => y₁ * y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
def HSMul.hSMul.arg_a0a1.HasParamFwdFDerivWithJumpsAt_rule :=
  (comp2_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ • y₂) (by fun_prop))
  rewrite_type_by (repeat ext); autodiff

@[aesop safe]
theorem HDiv.hDiv.arg_a0a1.HasParamFwdFDerivWithJumpsAt_rule
    (f g : W → X → R) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamFwdFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamFwdFDerivWithJumpsAt R g w g' J bg sg Sg)
    (hg' : ∀ x, g w x ≠ 0) :
    HasParamFwdFDerivWithJumpsAt (R:=R) (fun w x => f w x / g w x) w
      (f' := fun (dw : W) x =>
         let ydy := f' dw x
         let zdz := g' dw x
         (ydy.1/zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / (zdz.1^2)))
      (I:=I⊕J)
      (jumpVals := Sum.elim
        (fun i x =>
          let (y₁, y₂) := bf i x
          let z := g w x
          ((y₁/z), (y₂/z)))
        (fun j x =>
          let y := f w x
          let (z₁, z₂) := bg j x
          ((y/z₁), (y/z₂))))
      (jumpSpeed := Sum.elim sf sg)
      (jump := Sum.elim Sf Sg) := by

  unfold HasParamFwdFDerivWithJumpsAt
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor
  . convert HDiv.hDiv.arg_a0a1.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1) hg'
    . simp only [hf.2, hg.2]
  . simp [hf.2, hg.2]


@[aesop safe]
theorem ite.arg_te.HasParamFwdFDerivWithJumpsAt_rule
    (f g : W → X → Y) (w : W)
    {c : W → X → Prop} [∀ w x, Decidable (c w x)]
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamFwdFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamFwdFDerivWithJumpsAt R g w g' J bg sg Sg) :
    HasParamFwdFDerivWithJumpsAt (R:=R) (fun w x => if c w x then f w x else g w x) w
      (f' := fun dw x => if c w x then f' dw x else g' dw x)
      (I:=Unit⊕I⊕J)
      (jumpVals :=
        Sum.elim
         (fun _ x => (f w x, g w x)) <|
        Sum.elim bf bg)
      (jumpSpeed := Sum.elim (fun _ => frontierSpeed' R (fun w => {x | ¬c w x}) w) (Sum.elim sf sg))
      (jump := Sum.elim (fun _ => frontier {x | c w x}) <|
               Sum.elim
                 (fun i => Sf i ∩ {x | c w x})
                 (fun j => Sg j ∩ {x | ¬c w x})) := by


  unfold HasParamFwdFDerivWithJumpsAt
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor
  . convert ite.arg_te.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1)
    . simp only [hf.2, hg.2, Tactic.if_pull]
  . simp [hf.2, hg.2,Tactic.if_pull]




----------------------------------------------------------------------------------------------------
-- Trigonometric functions -------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open Scalar in
@[aesop safe]
def Scalar.sin.arg_a0.HasParamFwdFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=R) (Z:=R) (fun _ y => sin y) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff


open Scalar in
@[aesop safe]
def Scalar.cos.arg_a0.HasParamFwdFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=R) (Z:=R) (fun _ y => cos y) (by simp; fun_prop))
  rewrite_type_by (repeat ext); autodiff
