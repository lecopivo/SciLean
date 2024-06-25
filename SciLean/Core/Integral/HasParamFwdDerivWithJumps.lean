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
  {I} [IndexType I] {f' df s S}
  (hf : HasParamFwdFDerivWithJumpsAt R f w f' I df s S)
  /- (hμ : μ ≪ volume) -/ :
  (fwdFDeriv R (fun w' => ∫ x, f w' x ∂μ) w)
  =
  fun dw =>
    let interior := ∫ x, f' dw x ∂μ
    let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
    let shocks := ∑ i, ∫ x in S i, (s i dw x * density x) • ((df i x).1 - (df i x).2) ∂μH[finrank R X - 1]
    (interior.1, interior.2 + shocks) := by

  unfold fwdFDeriv
  funext dw; ext
  . simp only [fst_integral (hf := sorry_proof), hf.2]
  . simp only [fderiv_under_integral R f w μ hf.1, add_left_inj, snd_integral (hf:=sorry_proof)]



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


end HasParamFwdDerivWithJumps
open HasParamFwdDerivWithJumps



@[aesop safe]
theorem Prod.mk.arg_fstsnd.HasParamFwdFDerivWithJumpsAt_rule
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



@[aesop safe]
theorem Prod.fst.arg_self.HasParamFwdFDerivWithJumpsAt_rule
    (f : W → X → Y×Z) (w : W)
    {I f' bf sf Sf}
    (hf : HasParamFwdFDerivWithJumpsAt R f w f' I bf sf Sf) :
    HasParamFwdFDerivWithJumpsAt (R:=R) (fun w x => (f w x).1) w
      (f':= fun dw x =>
         let ydy := f' dw x
         (ydy.1.1, ydy.2.1))
      (I := I)
      (jumpVals := fun i x => let y := bf i x; (y.1.1, y.2.1))
      (jumpSpeed := sf)
      (jump := Sf) := by

  unfold HasParamFwdFDerivWithJumpsAt
  constructor
  . exact Prod.fst.arg_self.HasParamFDerivWithJumpsAt_rule _ _  _ (hf.1)
  . simp [hf.2]


@[aesop safe]
theorem Prod.snd.arg_self.HasParamFwdFDerivWithJumpsAt_rule
    (f : W → X → Y×Z) (w : W)
    {I f' bf sf Sf}
    (hf : HasParamFwdFDerivWithJumpsAt R f w f' I bf sf Sf) :
    HasParamFwdFDerivWithJumpsAt (R:=R) (fun w x => (f w x).2) w
      (f':= fun dw x =>
         let ydy := f' dw x
         (ydy.1.2, ydy.2.2))
      (I := I)
      (jumpVals := fun i x => let y := bf i x; (y.1.2, y.2.2))
      (jumpSpeed := sf)
      (jump := Sf) := by

  unfold HasParamFwdFDerivWithJumpsAt
  constructor
  . exact Prod.snd.arg_self.HasParamFDerivWithJumpsAt_rule _ _  _ (hf.1)
  . simp [hf.2]


@[aesop safe]
theorem HAdd.hAdd.arg_a0a1.HasParamFwdFDerivWithJumpsAt_rule
    (f g : W → X → Y) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamFwdFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamFwdFDerivWithJumpsAt R g w g' J bg sg Sg) :
    HasParamFwdFDerivWithJumpsAt (R:=R) (fun w x => f w x + g w x) w
      (f' := fun (dw : W) x =>
        f' dw x + g' dw x)
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
      (jumpSpeed := Sum.elim sf sg)
      (jump := Sum.elim Sf Sg) := by

  unfold HasParamFwdFDerivWithJumpsAt
  constructor
  . exact HAdd.hAdd.arg_a0a1.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1)
  . simp [hf.2, hg.2]


@[aesop safe]
theorem HSub.hSub.arg_a0a1.HasParamFwdFDerivWithJumpsAt_rule
    (f g : W → X → Y) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamFwdFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamFwdFDerivWithJumpsAt R g w g' J bg sg Sg) :
    HasParamFwdFDerivWithJumpsAt (R:=R) (fun w x => f w x - g w x) w
      (f' := fun (dw : W) x =>
        f' dw x - g' dw x)
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
      (jumpSpeed := Sum.elim sf sg)
      (jump := Sum.elim Sf Sg) := by

  unfold HasParamFwdFDerivWithJumpsAt
  constructor
  . exact HSub.hSub.arg_a0a1.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1)
  . simp [hf.2, hg.2]

@[aesop safe]
theorem Neg.neg.arg_a0.HasParamFwdFDerivWithJumpsAt_rule
    (f : W → X → Y) (w : W)
    {I f' bf sf Sf}
    (hf : HasParamFwdFDerivWithJumpsAt R f w f' I bf sf Sf) :
    HasParamFwdFDerivWithJumpsAt (R:=R) (fun w x => - f w x) w
      (f':=fun dw x => - f' dw x)
      (I := I)
      (jumpVals := fun i x => - bf i x)
      (jumpSpeed := sf)
      (jump := Sf) := by

  unfold HasParamFwdFDerivWithJumpsAt
  constructor
  . exact Neg.neg.arg_a0.HasParamFDerivWithJumpsAt_rule _ _  _ (hf.1)
  . simp [hf.2]


@[aesop safe]
theorem HMul.hMul.arg_a0a1.HasParamFwdFDerivWithJumpsAt_rule
    (f g : W → X → R) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamFwdFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamFwdFDerivWithJumpsAt R g w g' J bg sg Sg) :
    HasParamFwdFDerivWithJumpsAt (R:=R) (fun w x => f w x * g w x) w
      (f' := fun (dw : W) x =>
         let ydy := f' dw x
         let zdz := g' dw x
         (ydy.1 * zdz.1, ydy.2 * zdz.1 + ydy.1 * zdz.2))
      (I:=I⊕J)
      (jumpVals := Sum.elim
        (fun i x =>
          let (y₁, y₂) := bf i x
          let z := g w x
          ((y₁*z), (y₂*z)))
        (fun j x =>
          let y := f w x
          let (z₁, z₂) := bg j x
          ((y*z₁), (y*z₂))))
      (jumpSpeed := Sum.elim sf sg)
      (jump := Sum.elim Sf Sg) := by

  unfold HasParamFwdFDerivWithJumpsAt
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor
  . convert HMul.hMul.arg_a0a1.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1)
    . simp only [hf.2, hg.2]
  . simp [hf.2, hg.2]


@[aesop safe]
theorem HSMul.hSMul.arg_a0a1.HasParamFwdFDerivWithJumpsAt_rule
    (f : W → X → R) (g : W → X → Y) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamFwdFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamFwdFDerivWithJumpsAt R g w g' J bg sg Sg) :
    HasParamFwdFDerivWithJumpsAt (R:=R) (fun w x => f w x • g w x) w
      (f' := fun (dw : W) x =>
         let ydy := f' dw x
         let zdz := g' dw x
         (ydy.1 • zdz.1, ydy.2 • zdz.1 + ydy.1 • zdz.2))
      (I:=I⊕J)
      (jumpVals := Sum.elim
        (fun i x =>
          let (y₁, y₂) := bf i x
          let z := g w x
          ((y₁•z), (y₂•z)))
        (fun j x =>
          let y := f w x
          let (z₁, z₂) := bg j x
          ((y•z₁), (y•z₂))))
      (jumpSpeed := Sum.elim sf sg)
      (jump := Sum.elim Sf Sg) := by

  unfold HasParamFwdFDerivWithJumpsAt
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor
  . convert HSMul.hSMul.arg_a0a1.HasParamFDerivWithJumpsAt_rule _ _ _ _ (hf.1) (hg.1)
    . simp only [hf.2, hg.2]
  . simp [hf.2, hg.2]


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
      (jumpSpeed := Sum.elim (fun _ => frontierSpeed R (fun w => {x | ¬c w x}) w) (Sum.elim sf sg))
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
