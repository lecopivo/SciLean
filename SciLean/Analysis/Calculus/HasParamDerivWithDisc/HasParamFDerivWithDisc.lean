import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Hausdorff

import SciLean.Analysis.Calculus.RevFDeriv

import SciLean.Tactic.Autodiff
import SciLean.Tactic.GTrans

set_option linter.unusedVariables false

open MeasureTheory Topology Filter FiniteDimensional

namespace SciLean

variable
  {R} [RealScalar R] [MeasureSpace R]
  {W} [NormedAddCommGroup W] [NormedSpace R W]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [NormedSpace ℝ X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y] [NormedSpace ℝ Y]
  {Y₁} [NormedAddCommGroup Y₁] [NormedSpace R Y₁] [NormedSpace ℝ Y₁]
  {Y₂} [NormedAddCommGroup Y₂] [NormedSpace R Y₂] [NormedSpace ℝ Y₂]
  {Z} [NormedAddCommGroup Z] [NormedSpace R Z] [NormedSpace ℝ Z]

set_default_scalar R


variable (R)
open Classical in
noncomputable
def frontierSpeed (A : W → Set X) (w dw : W) (x : X) : R :=
  match Classical.dec (∃ (φ : W → X → R), (∀ w, closure (A w) = {x | φ w x ≤ 0})) with
  | .isTrue h =>
    let φ := Classical.choose h
    (-(fderiv R (φ · x) w dw)/‖fgradient (φ w ·) x‖₂)
  | .isFalse _ => 0


structure HasParamFDerivWithDiscAtImpl (f : W → X → Y) (w : W)
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

    The first value is in the negative noramal direction and the second value in the positive
    normal direction.

    The orientation of the normal is arbitrary but fixed as `discVals` and `discSpeed` depend on it. -/
    (discVals : I → X → Y×Y)
    /- Normal speed of the jump discontinuity. -/
    (discSpeed : I → W → X → R)
    /- Jump discontinuities of `f`. It is assumed that they are all almost disjoint. -/
    (disc : I → Set X) : Prop where

  -- todo: some of there statements should hold on neighbourhoods of `w`
  diff :  ∀ j x, x ∈ Ω j w → DifferentiableAt R (f · x) w
  deriv : ∀ j x dw, x ∈ Ω j w → fderiv R (f · x) w dw = f' dw x

  discValsLimit :
    ∀ p n : J, match ι p n with
      | none => True
      | some i => ∀ x ∈ disc i,
        /- lim x' → x, x ∈ Ω p, f w x' = (discVals i x).1 -/
        (𝓝 x ⊓ 𝓟 (Ω p w)).Tendsto (fun x' => f w x') (𝓝 (discVals i x).1)
        ∧
        /- lim x' → x, x ∈ Ω n, f w x' = (discVals i x).2 -/
        (𝓝 x ⊓ 𝓟 (Ω n w)).Tendsto (fun x' => f w x') (𝓝 (discVals i x).2)

  discSpeedEq :
    ∀ p n : J, match ι p n with
      | none => True
      | some i => ∀ x ∈ disc i,
        frontierSpeed R (Ω n) w dw x = discSpeed i dw x
variable {R}

variable (R W X Y)
structure DiscontinuityData (R W X Y : Type) where
  vals : X → Y×Y
  speed : W → X → R
  discontinuity : Set X

abbrev DiscontinuityDataList := List (DiscontinuityData R W X Y)

variable {R W X Y}


def DiscontinuityDataList.getDiscontinuity (d : DiscontinuityDataList R W X Y) : Set X :=
  d.foldl (init:=∅) (fun s ⟨_,_,x⟩ => s ∪ x)

def DiscontinuityDataList.getDiscontinuities (d : DiscontinuityDataList R W X Y) : List (Set X) :=
  d.map (·.discontinuity)


/-- Set `A` and `B` are disjoint up to a set of zero (n-1)-dimensional measure.

For example, in two dimensions two circles are almost disjoint unless they are the same.
This is because their intersection consist up to two points which have zero 1-dimensional measure.
 -/
def AlmostDisjoint {X} [MeasurableSpace X] (A B : Set X) (μ : Measure X := by volume_tac) : Prop :=
  μ (A ∩ B) = 0

def AlmostDisjointList {X} [MeasurableSpace X]
    (As : List (Set X)) (μ : Measure X := by volume_tac) : Prop :=
  ∀ i j : Fin As.length, i ≠ j → AlmostDisjoint As[i] As[j] μ

variable (R)
@[gtrans]
opaque HasParamFDerivWithDiscAt (f : W → X → Y) (w : W)
    (f' : outParam <| W → X → Y)
    (disc : outParam <| DiscontinuityDataList R W X Y)
    : Prop  -- := ∃ J Ω ι, HasParamFDerivWithDiscAtImpl R f w f' sorry J ι Ω sorry sorry sorry


-- def HasParamFDerivWithDisc (f : W → X → Y)
--     (f' : W → W → X → Y)
--     (I : Type)
--     (discVals : I → W → X → Y×Y)
--     (discSpeed : I → W → W → X → R)
--     (disc : I → W → Set X) := ∀ w, HasParamFDerivWithDiscAt R f w (f' w) I (discVals · w) (discSpeed · w) (disc · w)




-- @[fun_trans]
theorem fderiv_under_integral
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  (f : W → X → Y) (w dw : W) (μ : Measure X)
  {f' disc}
  (hf : HasParamFDerivWithDiscAt R f w f' disc)
  /- todo: add some integrability conditions -/ :
  (fderiv R (fun w' => ∫ x, f w' x ∂μ) w dw)
  =
  let interior := ∫ x, f' dw x ∂μ
  let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
  let shocks := disc.foldl (init:=0) fun sum ⟨df,s,Γ⟩ => sum +
      ∫ x in Γ,
        let vals := df x
        (s dw x * density x) • (vals.1 - vals.2) ∂μH[finrank R X - (1:ℕ)]
  interior + shocks := sorry_proof


-- @[fun_trans]
theorem fderiv_under_integral_over_set
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [NormedSpace ℝ X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  (f : W → X → Y) (w dw : W) (μ : Measure X) (Ω : Set X)
  {f' disc}
  (hf : HasParamFDerivWithDiscAt R f w f' disc)
  (hA : AlmostDisjoint (frontier Ω) disc.getDiscontinuity μH[finrank ℝ X - (1:ℕ)])
  /- todo: add some integrability conditions -/ :
  (fderiv R (fun w' => ∫ x in Ω, f w' x ∂μ) w dw)
  =
  let interior := ∫ x in Ω, f' dw x ∂μ
  let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
  let shocks := disc.foldl (init:=0)
    fun sum ⟨df,s,Γ⟩ => sum +
      ∫ x in Γ ∩ Ω,
        let vals := df x
        (s dw x * density x) • (vals.1 - vals.2) ∂μH[finrank R X - (1:ℕ)]
  interior + shocks := sorry_proof



----------------------------------------------------------------------------------------------------
-- Lambda rules ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

namespace HasParamFDerivWithDiscAt


@[gtrans high]
theorem differentiable_at_rule
    (w : W)
    (f : W → X → Y) (hf : ∀ x, DifferentiableAt R (f · x) w) :
    HasParamFDerivWithDiscAt R f w
      (fun dw x => fderiv R (f · x) w dw)
      [] :=

  sorry_proof

theorem comp_differentiable_discs_rule_at
    (f : W → Y → Z) (g : W → X → Y) (w : W)
    {g' disc}
    (hf : ∀ x, DifferentiableAt R (fun (w,y) => f w y) (w,g w x))
    (hg : HasParamFDerivWithDiscAt R g w g' disc) :
    HasParamFDerivWithDiscAt (R:=R) (fun w x => f w (g w x)) w
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



theorem comp_differentiable_discs_rule
    (f : W → Y → Z) (g : W → X → Y) (w : W)
    {g' disc}
    (hf : Differentiable R (fun (w,y) => f w y))
    (hg : HasParamFDerivWithDiscAt R g w g' disc) :
    HasParamFDerivWithDiscAt (R:=R) (fun w x => f w (g w x)) w
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



theorem comp1_differentiable_discs_rule
    (f : W → Y → Z) (hf : Differentiable R (fun (w,y) => f w y))
    (g : W → X → Y) (w : W)
    {g' disc}
    (hg : HasParamFDerivWithDiscAt R g w g' disc) :
    HasParamFDerivWithDiscAt (R:=R) (fun w x => f w (g w x)) w
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

    comp_differentiable_discs_rule R f g w hf hg


@[gtrans]
theorem _root_.Prod.mk.arg_fstsnd.HasParamFDerivWithDiscAt_rule
    (f : W → X → Y) (g : W → X → Z) (w : W)
    {f' fdisc} {g' gdisc}
    (hf : HasParamFDerivWithDiscAt R f w f' fdisc)
    (hg : HasParamFDerivWithDiscAt R g w g' gdisc)
    (hdisjoint : AlmostDisjoint fdisc.getDiscontinuity gdisc.getDiscontinuity μH[finrank ℝ X - (1:ℕ)])
    /- (hIJ : DisjointDiscs R Sf Sg) -/ :
    HasParamFDerivWithDiscAt (R:=R) (fun w x => (f w x, g w x)) w
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



theorem comp2_differentiable_discs_rule
    (f : W → Y₁ → Y₂ → Z) (hf : Differentiable R (fun (w,y₁,y₂) => f w y₁ y₂))
    (g₁ : W → X → Y₁) (g₂ : W → X → Y₂) (w : W)
    {g₁' dg₁} {g₂' dg₂}
    (hg₁ : HasParamFDerivWithDiscAt R g₁ w g₁' dg₁)
    (hg₂ : HasParamFDerivWithDiscAt R g₂ w g₂' dg₂)
    (hdisjoint : AlmostDisjoint dg₁.getDiscontinuity dg₂.getDiscontinuity μH[finrank ℝ X - (1:ℕ)]) :
    HasParamFDerivWithDiscAt (R:=R) (fun w x => f w (g₁ w x) (g₂ w x)) w
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

  convert comp_differentiable_discs_rule R (fun (w:W) (y:Y₁×Y₂) => f w y.1 y.2) (fun w x => (g₁ w x, g₂ w x)) w
    (hf) (Prod.mk.arg_fstsnd.HasParamFDerivWithDiscAt_rule R g₁ g₂ w hg₁ hg₂ hdisjoint)

  · simp[Function.comp]


end HasParamFDerivWithDiscAt
open HasParamFDerivWithDiscAt


----------------------------------------------------------------------------------------------------
-- Function Rules ----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open FiniteDimensional in
/--
Proposition stating that intersection of two disc discontinuities is empty up to
(n-1)-dimensional measure. -/
def DisjointDiscs {X} [NormedAddCommGroup X] [NormedSpace R X] [MeasureSpace X] [BorelSpace X]
  {I J} (S : I → Set X) (P : J → Set X) :=
  μH[finrank R X - 1] (⋃ i, S i ∩ ⋃ j, P j) = 0


@[gtrans]
def Prod.fst.arg_self.HasParamFDerivWithDiscAt_rule :=
  (comp1_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Y) (fun _ yz => yz.1) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def Prod.snd.arg_self.HasParamFDerivWithDiscAt_rule :=
  (comp1_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y:=Y×Z) (Z:=Z) (fun _ yz => yz.2) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HAdd.hAdd.arg_a0a1.HasParamFDerivWithDiscAt_rule :=
  (comp2_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ + y₂) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HSub.hSub.arg_a0a1.HasParamFDerivWithDiscAt_rule :=
  (comp2_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y₁:=Y) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ - y₂) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def Neg.neg.arg_a0.HasParamFDerivWithDiscAt_rule :=
  (comp1_differentiable_discs_rule (R:=R) (X:=X) (Y:=Y) (Z:=Y) (fun (w : W) y => - y) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HMul.hMul.arg_a0a1.HasParamFDerivWithDiscAt_rule :=
  (comp2_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=R) (Z:=R) (fun _ y₁ y₂ => y₁ * y₂) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HPow.hPow.arg_a0.HasParamFDerivWithDiscAt_rule (n:ℕ) :=
  (comp1_differentiable_discs_rule (R:=R) (X:=X) (Y:=R) (Z:=R) (fun (w : W) y => y^n) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
def HSMul.hSMul.arg_a0a1.HasParamFDerivWithDiscAt_rule :=
  (comp2_differentiable_discs_rule (R:=R) (W:=W) (X:=X) (Y₁:=R) (Y₂:=Y) (Z:=Y) (fun _ y₁ y₂ => y₁ • y₂) (by fun_prop))
  -- rewrite_type_by (repeat ext); autodiff


@[gtrans]
theorem HDiv.hDiv.arg_a0a1.HasParamFDerivWithDiscAt_rule
    (f g : W → X → R) (w : W)
    {f' fdisc} {g' gdisc}
    (hf : HasParamFDerivWithDiscAt R f w f' fdisc)
    (hg : HasParamFDerivWithDiscAt R g w g' gdisc)
    (hdisjoint : AlmostDisjoint fdisc.getDiscontinuity gdisc.getDiscontinuity μH[finrank ℝ X - (1:ℕ)])
    (hg' : ∀ x, g w x ≠ 0) :
    HasParamFDerivWithDiscAt (R:=R) (fun w x => f w x / g w x) w
      (f' := fun (dw : W) x =>
         let y := f w x
         let dy := f' dw x
         let z := g w x
         let dz := g' dw x
         (dy * z - y * dz) / (z^2))
      (disc :=
        fdisc.map (fun d =>
          { d with vals := fun x =>
              let y := d.vals x
              let z := g w x
              (y.1/z, y.2/z) })
        ++
        gdisc.map (fun d =>
          { d with vals := fun x =>
              let y := f w x
              let z := d.vals x
              (y/z.1, y/z.2) })) := by

  convert comp_differentiable_discs_rule_at (R:=R)
          (f:=fun _ (y:R×R) => y.1 / y.2) (g:=fun w x => (f w x, g w x)) (w:=w)
          (hf:=by simp; sorry_proof)
          (hg:= Prod.mk.arg_fstsnd.HasParamFDerivWithDiscAt_rule R f g w hf hg hdisjoint)
  · fun_trans (disch:=apply hg')
  · simp[List.map_append]; congr


@[gtrans]
theorem ite.arg_te.HasParamFDerivWithDiscAt_rule
    (f g : W → X → Y) (w : W)
    {c : W → X → Prop} [∀ w x, Decidable (c w x)]
    {f' df} {g' dg}
    (hf : HasParamFDerivWithDiscAt R f w f' df)
    (hg : HasParamFDerivWithDiscAt R g w g' dg)
    (hdisjoint : AlmostDisjointList (frontier {x | c w x} :: df.getDiscontinuities ++ dg.getDiscontinuities) μH[finrank ℝ X - (1:ℕ)]) :
    HasParamFDerivWithDiscAt (R:=R) (fun w x => if c w x then f w x else g w x) w
      (f' := fun dw x => if c w x then f' dw x else g' dw x)
      (disc :=
        {vals := fun x => (f w x, g w x)
         speed := frontierSpeed R (fun w => {x | c w x}) w
         discontinuity := frontier {x | c w x}}
        ::
        df.map (fun d => {d with discontinuity := d.discontinuity ∩ {x | c w x}})
        ++
        dg.map (fun d => {d with discontinuity := d.discontinuity ∩ {x | ¬c w x}})) := by

  sorry_proof
