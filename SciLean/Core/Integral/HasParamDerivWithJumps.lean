import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Erased
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Hausdorff

import SciLean.Core.NotationOverField
import SciLean.Core.Functions.Trigonometric
import SciLean.Core.Functions.Gaussian
import SciLean.Core.FunctionTransformations.RevFDeriv

import SciLean.Tactic.Autodiff
import SciLean.Tactic.GTrans

set_option linter.unusedVariables false

open MeasureTheory Topology Filter

namespace SciLean

variable
  {R} [RealScalar R] [MeasureSpace R]
  {W} [NormedAddCommGroup W] [NormedSpace R W]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y] [NormedSpace ℝ Y]
  {Y₁} [NormedAddCommGroup Y₁] [NormedSpace R Y₁] [NormedSpace ℝ Y₁]
  {Y₂} [NormedAddCommGroup Y₂] [NormedSpace R Y₂] [NormedSpace ℝ Y₂]
  {Z} [NormedAddCommGroup Z] [NormedSpace R Z] [NormedSpace ℝ Z]

set_default_scalar R


variable (R)
open Classical in
noncomputable
def frontierSpeed' (A : W → Set X) (w dw : W) (x : X) : R :=
  match Classical.dec (∃ (φ : W → X → R), (∀ w, A w = {x | φ w x = 0})) with
  | .isTrue h =>
    let φ := Classical.choose h
    (-(fderiv R (φ · x) w dw)/‖fgradient (φ w ·) x‖₂)
  | .isFalse _ => 0


structure HasParamFDerivWithJumpsAtImpl (f : W → X → Y) (w : W)
    (f' : W → X → Y)
    /- Index set for jump discontinuities -/
    (I : Type)
    /- Index set for domains. -/
    (J : Type)
    /- Given to domain indices `i` and `j` return the index `k` of the interface `Γₖ = Ωᵢ ∩ Ωⱼ`. -/
    (ι : J → J → Option I)
    /- Domains on which `f` is differentiable w.r.t. `w`.  -/
    (Ω : J → W → Set X)
    /- Values of `f` on both sides of jump discontinuity.

    The first value is in the positive noramal direction and the second value in the negative
    normal direction.

    The orientation of the normal is arbitrary but fixed as `jumpVals` and `jumpSpeed` depend on it. -/
    (jumpVals : I → X → Y×Y)
    /- Normal speed of the jump discontinuity. -/
    (jumpSpeed : I → W → X → R)
    /- Jump discontinuities of `f`. -/
    (jump : I → Set X) : Prop where

  -- todo: some of there statements should hold on neighbourhoods of `w`
  diff :  ∀ j x, x ∈ Ω j w → DifferentiableAt R (f · x) w
  deriv : ∀ j x dw, x ∈ Ω j w → fderiv R (f · x) w dw = f' dw x

  jumpValsLimit :
    ∀ p n : J, match ι p n with
      | none => True
      | some i => ∀ x ∈ jump i,
        /- lim x' → x, x ∈ Ω p, f w x' = (jumpVals i x).1 -/
        (𝓝 x ⊓ 𝓟 (Ω p w)).Tendsto (fun x' => f w x') (𝓝 (jumpVals i x).1)
        ∧
        /- lim x' → x, x ∈ Ω n, f w x' = (jumpVals i x).2 -/
        (𝓝 x ⊓ 𝓟 (Ω n w)).Tendsto (fun x' => f w x') (𝓝 (jumpVals i x).2)

  jumpSpeedEq :
    ∀ p n : J, match ι p n with
      | none => True
      | some i => ∀ x ∈ jump i,
        frontierSpeed' R (Ω n) w dw x = jumpSpeed i dw x

@[gtrans]
def HasParamFDerivWithJumpsAt (f : W → X → Y) (w : W)
    (f' : outParam <| W → X → Y)
    (I : outParam <| Type)
    /- Values of `f` on both sides of jump discontinuity.

    The first value is in the positive noramal direction and the second value in the negative
    normal direction.

    The orientation of the normal is arbitrary but fixed as `jumpVals` and `jumpSpeed` depend on it. -/
    (jumpVals : outParam <| I → X → Y×Y)
    /- Normal speed of the jump discontinuity. -/
    (jumpSpeed : outParam <| I → W → X → R)
    /- Jump discontinuities of `f`. -/
    (jump : outParam <| I → Set X) : Prop := ∃ J Ω ι, HasParamFDerivWithJumpsAtImpl R f w f' I J ι Ω jumpVals jumpSpeed jump

variable (W X Y)
structure DiscontinuityData where
  vals : X → Y×Y
  speed : W → X → R
  discontinuity : Set X
variable {W X Y}

@[gtrans]
def HasParamFDerivWithJumpsAt' (f : W → X → Y) (w : W)
    (f' : outParam <| W → X → Y)
    (disc : outParam <| List (DiscontinuityData R W X Y))
    : Prop := ∃ J Ω ι, HasParamFDerivWithJumpsAtImpl R f w f' sorry J ι Ω sorry sorry sorry


def HasParamFDerivWithJumps (f : W → X → Y)
    (f' : W → W → X → Y)
    (I : Type)
    (jumpVals : I → W → X → Y×Y)
    (jumpSpeed : I → W → W → X → R)
    (jump : I → W → Set X) := ∀ w, HasParamFDerivWithJumpsAt R f w (f' w) I (jumpVals · w) (jumpSpeed · w) (jump · w)


open FiniteDimensional
-- @[fun_trans]
theorem fderiv_under_integral
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  (f : W → X → Y) (w dw : W) (μ : Measure X)
  {I} [hI:IndexType I] {f' df s S}
  (hf : HasParamFDerivWithJumpsAt R f w f' I df s S)
  /- todo: add some integrability conditions -/ :
  (fderiv R (fun w' => ∫ x, f w' x ∂μ) w dw)
  =
  let interior := ∫ x, f' dw x ∂μ
  let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
  let shocks := ∑ i, ∫ x in S i, (s i dw x * density x) • ((df i x).1 - (df i x).2) ∂μH[finrank R X - (1:ℕ)]
  interior + shocks := sorry_proof


open FiniteDimensional
-- @[fun_trans]
theorem fderiv_under_integral_over_set
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  (f : W → X → Y) (w dw : W) (μ : Measure X) (A : Set X)
  {I} [hI:IndexType I] {f' df s S}
  (hf : HasParamFDerivWithJumpsAt R f w f' I df s S)
  /- todo: add some integrability conditions -/ :
  (fderiv R (fun w' => ∫ x in A, f w' x ∂μ) w dw)
  =
  let interior := ∫ x in A, f' dw x ∂μ
  let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
  let shocks := ∑ i, ∫ x in S i ∩ A, (s i dw x * density x) • ((df i x).1 - (df i x).2) ∂μH[finrank R X - (1:ℕ)]
  interior + shocks := sorry_proof


variable (l : List ℕ)

#check l.foldl (init:=0) (fun s n => s + n)

open FiniteDimensional
-- @[fun_trans]
theorem fderiv_under_integral'
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  (f : W → X → Y) (w dw : W) (μ : Measure X)
  {f' disc}
  (hf : HasParamFDerivWithJumpsAt' R f w f' disc)
  /- todo: add some integrability conditions -/ :
  (fderiv R (fun w' => ∫ x, f w' x ∂μ) w dw)
  =
  let interior := ∫ x, f' dw x ∂μ
  let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
  let shocks := disc.foldl (init:=0)
    fun sum ⟨df,s,S⟩ => sum + ∫ x in S,
      let vals := df x
      (s dw x * density x) • (vals.1 - vals.2) ∂μH[finrank R X - (1:ℕ)]
  interior + shocks := sorry_proof


----------------------------------------------------------------------------------------------------
-- Lambda rules ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

namespace HasParamFDerivWithJumpsAt


@[gtrans high]
theorem smooth_rule
    (w : W)
    (f : W → X → Y) (hf : ∀ x, DifferentiableAt R (f · x) w) :
    HasParamFDerivWithJumpsAt R f w (fun dw x => fderiv R (f · x) w dw) Empty 0 0 (fun _ => ∅) :=

  sorry_proof


@[gtrans high]
theorem smooth_rule'
    (w : W)
    (f : W → X → Y) (hf : ∀ x, DifferentiableAt R (f · x) w) :
    HasParamFDerivWithJumpsAt' R f w
      (fun dw x => fderiv R (f · x) w dw)
      [{ vals := 0, speed := 0, discontinuity := ∅ }] :=

  sorry_proof


theorem comp_smooth_jumps_rule
    (f : W → Y → Z) (g : W → X → Y) (w : W)
    {I g' bg sg Sg}
    (hf : Differentiable R (fun (w,y) => f w y))
    (hg : HasParamFDerivWithJumpsAt R g w g' I bg sg Sg) :
    HasParamFDerivWithJumpsAt (R:=R) (fun w x => f w (g w x)) w
      (f' := fun dw x =>
         let y := g w x
         let dy := g' dw x
         let dz := fderiv R (fun (w,y) => f w y) (w,y) (dw,dy)
         dz)
      (I := I)
      (jumpVals := fun i x =>
         let y := bg i x
         (f w y.1, f w y.2))
      (jumpSpeed := sg)
      (jump := Sg) := sorry_proof


attribute [ftrans_simp] List.cons_append  List.nil_append List.singleton_append
attribute [ftrans_simp ↓] List.cons_append  List.nil_append List.singleton_append


theorem comp_smooth_jumps_rule'
    (f : W → Y → Z) (g : W → X → Y) (w : W)
    {g' disc}
    (hf : Differentiable R (fun (w,y) => f w y))
    (hg : HasParamFDerivWithJumpsAt' R g w g' disc) :
    HasParamFDerivWithJumpsAt' (R:=R) (fun w x => f w (g w x)) w
      (f' := fun dw x =>
         let y := g w x
         let dy := g' dw x
         let dz := fderiv R (fun (w,y) => f w y) (w,y) (dw,dy)
         dz)
      (disc := disc.map fun ⟨vals,speed,d⟩ =>
        { vals := fun x =>
            let y := vals x
            (f w y.1, f w y.2)
          speed := speed
          discontinuity := d })
       := sorry_proof


theorem comp_smooth_jumps_rule_at
    (f : W → Y → Z) (g : W → X → Y) (w : W)
    {I g' bg sg Sg}
    (hf : ∀ x, DifferentiableAt R (fun (w,y) => f w y) (w,g w x))
    (hg : HasParamFDerivWithJumpsAt R g w g' I bg sg Sg) :
    HasParamFDerivWithJumpsAt R (fun w x => f w (g w x)) w
      /- f' -/
      (fun dw x =>
         let y := g w x
         let dy := g' dw x
         let dz := fderiv R (fun (w,y) => f w y) (w,y) (dw,dy)
         dz)
      (I)
      /- jumpVals -/
      (fun i x =>
         let y := bg i x
         (f w y.1, f w y.2))
      /- jumpSpeed -/
      (sg)
      /- jump -/
      (Sg) := sorry_proof


theorem comp1_smooth_jumps_rule
    (f : W → Y → Z) (hf : Differentiable R (fun (w,y) => f w y))
    (g : W → X → Y) (w : W)
    {I g' bg sg Sg}
    (hg : HasParamFDerivWithJumpsAt R g w g' I bg sg Sg) :
    HasParamFDerivWithJumpsAt (R:=R) (fun w x => f w (g w x)) w
      /- f' -/
      (fun dw x =>
         let y := g w x
         let dy := g' dw x
         let dz := fderiv R (fun (w,y) => f w y) (w,y) (dw,dy)
         dz)
      (I)
      /- jumpVals -/
      (fun i x =>
         let y := bg i x
         (f w y.1, f w y.2))
      /- jumpSpeed -/
      (sg)
      /- jump -/
      (Sg) :=

    comp_smooth_jumps_rule R f g w hf hg


theorem comp1_smooth_jumps_rule'
    (f : W → Y → Z) (hf : Differentiable R (fun (w,y) => f w y))
    (g : W → X → Y) (w : W)
    {g' disc}
    (hg : HasParamFDerivWithJumpsAt' R g w g' disc) :
    HasParamFDerivWithJumpsAt' (R:=R) (fun w x => f w (g w x)) w
      /- f' -/
      (fun dw x =>
         let y := g w x
         let dy := g' dw x
         let dz := fderiv R (fun (w,y) => f w y) (w,y) (dw,dy)
         dz)
      (disc := disc.map fun ⟨vals,speed,d⟩ =>
        { vals := fun x =>
            let y := vals x
            (f w y.1, f w y.2)
          speed := speed
          discontinuity := d }) :=

    comp_smooth_jumps_rule' R f g w hf hg


@[gtrans]
theorem _root_.Prod.mk.arg_fstsnd.HasParamFDerivWithJumpsAt_rule
    (f : W → X → Y) (g : W → X → Z) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamFDerivWithJumpsAt R g w g' J bg sg Sg)
    /- (hIJ : DisjointJumps R Sf Sg) -/ :
    HasParamFDerivWithJumpsAt (R:=R) (fun w x => (f w x, g w x)) w
      (f' := fun dw x => (f' dw x, g' dw x))
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
      (jump := Sum.elim Sf Sg) := sorry_proof


@[gtrans]
theorem _root_.Prod.mk.arg_fstsnd.HasParamFDerivWithJumpsAt_rule'
    (f : W → X → Y) (g : W → X → Z) (w : W)
    {f' fdisc} {g' gdisc}
    (hf : HasParamFDerivWithJumpsAt' R f w f' fdisc)
    (hg : HasParamFDerivWithJumpsAt' R g w g' gdisc)
    /- (hIJ : DisjointJumps R Sf Sg) -/ :
    HasParamFDerivWithJumpsAt' (R:=R) (fun w x => (f w x, g w x)) w
      (f' := fun dw x => (f' dw x, g' dw x))
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
              ((y, z.1), (y, z.2)) })) := sorry_proof


theorem comp2_smooth_jumps_rule
    (f : W → Y₁ → Y₂ → Z) (hf : Differentiable R (fun (w,y₁,y₂) => f w y₁ y₂))
    (g₁ : W → X → Y₁) (g₂ : W → X → Y₂) (w : W)
    {I₁ g₁' bg₁ sg₁ Sg₁} {I₂ g₂' bg₂ sg₂ Sg₂}
    (hg₁ : HasParamFDerivWithJumpsAt R g₁ w g₁' I₁ bg₁ sg₁ Sg₁)
    (hg₂ : HasParamFDerivWithJumpsAt R g₂ w g₂' I₂ bg₂ sg₂ Sg₂) :
    HasParamFDerivWithJumpsAt (R:=R) (fun w x => f w (g₁ w x) (g₂ w x)) w
      (f' := fun dw x =>
         let y₁ := g₁ w x
         let dy₁ := g₁' dw x
         let y₂ := g₂ w x
         let dy₂ := g₂' dw x
         let dz := fderiv R (fun (w,y₁,y₂) => f w y₁ y₂) (w,y₁,y₂) (dw,dy₁,dy₂)
         dz)
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


  convert comp_smooth_jumps_rule R (fun (w:W) (y:Y₁×Y₂) => f w y.1 y.2) (fun w x => (g₁ w x, g₂ w x)) w
    (hf) (Prod.mk.arg_fstsnd.HasParamFDerivWithJumpsAt_rule R g₁ g₂ w hg₁ hg₂)

  . rename_i i x; induction i <;> simp


theorem comp2_smooth_jumps_rule'
    (f : W → Y₁ → Y₂ → Z) (hf : Differentiable R (fun (w,y₁,y₂) => f w y₁ y₂))
    (g₁ : W → X → Y₁) (g₂ : W → X → Y₂) (w : W)
    {g₁' dg₁} {g₂' dg₂}
    (hg₁ : HasParamFDerivWithJumpsAt' R g₁ w g₁' dg₁)
    (hg₂ : HasParamFDerivWithJumpsAt' R g₂ w g₂' dg₂) :
    HasParamFDerivWithJumpsAt' (R:=R) (fun w x => f w (g₁ w x) (g₂ w x)) w
      (f' := fun dw x =>
         let y₁ := g₁ w x
         let dy₁ := g₁' dw x
         let y₂ := g₂ w x
         let dy₂ := g₂' dw x
         let dz := fderiv R (fun (w,y₁,y₂) => f w y₁ y₂) (w,y₁,y₂) (dw,dy₁,dy₂)
         dz)
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

  convert comp_smooth_jumps_rule' R (fun (w:W) (y:Y₁×Y₂) => f w y.1 y.2) (fun w x => (g₁ w x, g₂ w x)) w
    (hf) (Prod.mk.arg_fstsnd.HasParamFDerivWithJumpsAt_rule' R g₁ g₂ w hg₁ hg₂)

  . simp[Function.comp]


end HasParamFDerivWithJumpsAt
open HasParamFDerivWithJumpsAt


----------------------------------------------------------------------------------------------------
-- Function Rules ----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open FiniteDimensional in
/--
Proposition stating that intersection of two jump discontinuities is empty up to
(n-1)-dimensional measure. -/
def DisjointJumps {X} [NormedAddCommGroup X] [NormedSpace R X] [MeasureSpace X] [BorelSpace X]
  {I J} (S : I → Set X) (P : J → Set X) :=
  μH[finrank R X - 1] (⋃ i, S i ∩ ⋃ j, P j) = 0


@[gtrans]
def Prod.fst.arg_self.HasParamFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Y) (fun _ yz => yz.1) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def Prod.snd.arg_self.HasParamFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Z) (fun _ yz => yz.2) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HAdd.hAdd.arg_a0a1.HasParamFDerivWithJumpsAt_rule :=
  (comp2_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ + y₂) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HSub.hSub.arg_a0a1.HasParamFDerivWithJumpsAt_rule :=
  (comp2_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ - y₂) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def Neg.neg.arg_a0.HasParamFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (X:=X) (Y:=Y) (Z:=Y) (fun (w : W) y => - y) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HMul.hMul.arg_a0a1.HasParamFDerivWithJumpsAt_rule :=
  (comp2_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=R) (Z:=R) (fun _ y₁ y₂ => y₁ * y₂) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HPow.hPow.arg_a0.HasParamFDerivWithJumpsAt_rule (n:ℕ) :=
  (comp1_smooth_jumps_rule (R:=R) (X:=X) (Y:=R) (Z:=R) (fun (w : W) y => y^n) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HSMul.hSMul.arg_a0a1.HasParamFDerivWithJumpsAt_rule :=
  (comp2_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ • y₂) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
theorem HDiv.hDiv.arg_a0a1.HasParamFDerivWithJumpsAt_rule
    (f g : W → X → R) (w : W)
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamFDerivWithJumpsAt R g w g' J bg sg Sg)
    (hg' : ∀ x, g w x ≠ 0) :
    HasParamFDerivWithJumpsAt (R:=R) (fun w x => f w x / g w x) w
      (f' := fun (dw : W) x =>
         let y := f w x
         let dy := f' dw x
         let z := g w x
         let dz := g' dw x
         (dy * z - y * dz) / (z^2))
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

  convert HasParamFDerivWithJumpsAt.comp_smooth_jumps_rule_at (R:=R)
          (f:=fun _ (y:R×R) => y.1 / y.2) (g:=fun w x => (f w x, g w x)) (w:=w)
          (hf:=by simp; sorry_proof)
          (hg:= Prod.mk.arg_fstsnd.HasParamFDerivWithJumpsAt_rule R f g w hf hg)
  . fun_trans (disch:=apply hg')
  . rename_i i x
    induction i
    . simp
    . simp


@[gtrans]
theorem ite.arg_te.HasParamFDerivWithJumpsAt_rule
    (f g : W → X → Y) (w : W)
    {c : W → X → Prop} [∀ w x, Decidable (c w x)]
    {f' I bf sf Sf} {g' J bg sg Sg}
    (hf : HasParamFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamFDerivWithJumpsAt R g w g' J bg sg Sg) :
    HasParamFDerivWithJumpsAt (R:=R) (fun w x => if c w x then f w x else g w x) w
      (f' := fun dw x => if c w x then f' dw x else g' dw x)
      (I:=Unit⊕I⊕J)
      (jumpVals :=
        Sum.elim
         (fun _ x => (f w x, g w x)) <|
        Sum.elim bf bg)
      (jumpSpeed := Sum.elim (fun _ => frontierSpeed' R (fun w => {x | ¬c w x}) w) (Sum.elim sf sg))
      (jump := Sum.elim
                 (fun _ => frontier {x | c w x}) <|
               Sum.elim
                 (fun i => Sf i ∩ {x | c w x})
                 (fun j => Sg j ∩ {x | ¬c w x})) := by

  sorry_proof


----------------------------------------------------------------------------------------------------
-- Trigonometric functions -------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open Scalar in
@[gtrans]
def Scalar.sin.arg_a0.HasParamFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=R) (Z:=R) (fun _ y => sin y) (by simp; fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


open Scalar in
@[gtrans]
def Scalar.cos.arg_a0.HasParamFDerivWithJumpsAt_rule :=
  (comp1_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y:=R) (Z:=R) (fun _ y => cos y) (by simp; fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def gaussian.arg_a0.HasParamFDerivWithJumpsAt_rule (σ : R) :=
  (comp2_smooth_jumps_rule (R:=R) (W:=W) (X:=X) (Y₁:=X) (Y₂:=X) (Z:=R) (fun _ μ x => gaussian μ σ x) (by simp; fun_prop))
  -- rewrite_type_by (repeat ext); autodiff



----------------------------------------------------------------------------------------------------


@[gtrans]
def Prod.fst.arg_self.HasParamFDerivWithJumpsAt_rule' :=
  (comp1_smooth_jumps_rule' (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Y) (fun _ yz => yz.1) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def Prod.snd.arg_self.HasParamFDerivWithJumpsAt_rule' :=
  (comp1_smooth_jumps_rule' (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Z) (fun _ yz => yz.2) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HAdd.hAdd.arg_a0a1.HasParamFDerivWithJumpsAt_rule' :=
  (comp2_smooth_jumps_rule' (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ + y₂) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HSub.hSub.arg_a0a1.HasParamFDerivWithJumpsAt_rule' :=
  (comp2_smooth_jumps_rule' (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ - y₂) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def Neg.neg.arg_a0.HasParamFDerivWithJumpsAt_rule' :=
  (comp1_smooth_jumps_rule' (R:=R) (X:=X) (Y:=Y) (Z:=Y) (fun (w : W) y => - y) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HMul.hMul.arg_a0a1.HasParamFDerivWithJumpsAt_rule' :=
  (comp2_smooth_jumps_rule' (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=R) (Z:=R) (fun _ y₁ y₂ => y₁ * y₂) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HPow.hPow.arg_a0.HasParamFDerivWithJumpsAt_rule' (n:ℕ) :=
  (comp1_smooth_jumps_rule' (R:=R) (X:=X) (Y:=R) (Z:=R) (fun (w : W) y => y^n) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HSMul.hSMul.arg_a0a1.HasParamFDerivWithJumpsAt_rule' :=
  (comp2_smooth_jumps_rule' (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ • y₂) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
theorem ite.arg_te.HasParamFDerivWithJumpsAt_rule'
    (f g : W → X → Y) (w : W)
    {c : W → X → Prop} [∀ w x, Decidable (c w x)]
    {f' df} {g' dg}
    (hf : HasParamFDerivWithJumpsAt' R f w f' df)
    (hg : HasParamFDerivWithJumpsAt' R g w g' dg) :
    HasParamFDerivWithJumpsAt' (R:=R) (fun w x => if c w x then f w x else g w x) w
      (f' := fun dw x => if c w x then f' dw x else g' dw x)
      (disc :=
        {vals := fun x => (f w x, g w x)
         speed := frontierSpeed' R (fun w => {x | ¬c w x}) w
         discontinuity := frontier {x | c w x}}
        ::
        df.map (fun d => {d with discontinuity := d.discontinuity ∩ {x | c w x}})
        ++
        dg.map (fun d => {d with discontinuity := d.discontinuity ∩ {x | ¬c w x}})) := by

  sorry_proof


attribute [ftrans_simp] List.append_assoc List.map_cons List.map_nil
attribute [ftrans_simp ↓] List.append_assoc List.map_cons List.map_nil

set_option trace.Meta.Tactic.simp.rewrite true in
#check (([1] ++ [2,3] ++ [5,6]) ++ ([1] ++ [2,3] ++ [5,6])  ) rewrite_by
  simp (config:={singlePass:=true}) only [ftrans_simp]
  simp (config:={singlePass:=true}) only [ftrans_simp]
