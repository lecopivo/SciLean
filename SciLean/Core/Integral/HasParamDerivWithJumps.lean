import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Erased
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Hausdorff

import SciLean.Core.NotationOverField
import SciLean.Mathlib.Analysis.AdjointSpace.Adjoint
-- import SciLean.Core.Integral.MovingDomain

import SciLean.Core.FunctionTransformations.RevFDeriv

open MeasureTheory Topology Filter

namespace SciLean

variable
  {R} [RealScalar R] [MeasureSpace R]
  {W} [NormedAddCommGroup W] [NormedSpace R W]
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y] [NormedSpace ℝ Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace R Z] [NormedSpace ℝ Z]

set_default_scalar R


variable (R)
open Classical in
noncomputable
def frontierSpeed (A : W → Set X) (w dw : W) (x : X) : R :=
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
        frontierSpeed R (Ω n) w dw x = jumpSpeed i dw x


def HasParamFDerivWithJumpsAt (f : W → X → Y) (w : W)
    (f' : W → X → Y)
    (I : Type)
    /- Values of `f` on both sides of jump discontinuity.

    The first value is in the positive noramal direction and the second value in the negative
    normal direction.

    The orientation of the normal is arbitrary but fixed as `jumpVals` and `jumpSpeed` depend on it. -/
    (jumpVals : I → X → Y×Y)
    /- Normal speed of the jump discontinuity. -/
    (jumpSpeed : I → W → X → R)
    /- Jump discontinuities of `f`. -/
    (jump : I → Set X) : Prop := ∃ J Ω ι, HasParamFDerivWithJumpsAtImpl R f w f' I J ι Ω jumpVals jumpSpeed jump


structure HasParamFDerivWithJumpsAt' (f : W → X → Y) (w : W) where
    I : Type
    f' : W → X → Y
    jumpVals : I → X → Y×Y
    jumpSpeed : I → W → X → R
    jump : I → Set X
    -- we do not keep track of the domains only of their interfaces
    proof : ∃ J Ω ι, HasParamFDerivWithJumpsAtImpl R f w f' I J ι Ω jumpVals jumpSpeed jump


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
  (f : W → X → Y) (w : W) (μ : Measure X)
  (I) [IndexType I]
  (hf : Σ' f' df s S, HasParamFDerivWithJumpsAt R f w f' I df s S) (dw : W)
  /- todo: add some integrability conditions -/ :
  (fderiv R (fun w' => ∫ x, f w' x ∂μ) w dw)
  =
  let ⟨f', df, s, S, _⟩ := hf
  let interior := ∫ x, f' dw x ∂μ
  let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
  let shocks := ∑ i, ∫ x in S i, (s i dw x * density x) • ((df i x).1 - (df i x).2) ∂μH[finrank R X - 1]
  interior + shocks := sorry_proof


open FiniteDimensional
-- @[fun_trans]
theorem fderiv_under_integral'
  {X} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X] [MeasureSpace X] [BorelSpace X]
  (f : W → X → Y) (w : W) (μ : Measure X)
  (I) [IndexType I]
  (hf : HasParamFDerivWithJumpsAt' R f w) (dw : W)
  [IndexType hf.I]
  /- todo: add some integrability conditions -/ :
  (fderiv R (fun w' => ∫ x, f w' x ∂μ) w dw)
  =
  let f' := hf.f'
  let df := hf.jumpVals
  let s := hf.jumpSpeed
  let S := hf.jump
  let interior := ∫ x, f' dw x ∂μ
  let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
  let shocks := ∑ i, ∫ x in S i, (s i dw x * density x) • ((df i x).1 - (df i x).2) ∂μH[finrank R X - 1]
  interior + shocks := sorry_proof



----------------------------------------------------------------------------------------------------
-- Lambda rules ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

namespace HasParamFDerivWithJumpsAt

@[aesop unsafe]
noncomputable
def smooth_rule
    (w : W)
    (f : W → X → Y) (hf : ∀ x, DifferentiableAt R (f · x) w) :
    Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R f w f' I bf sf Sf :=

  ⟨fun dw x => fderiv R (f · x) w dw,
   0, 0, fun _ => ∅, sorry_proof⟩



@[aesop unsafe]
noncomputable
def comp_smooth_jumps_rule
    (f : W → Y → Z) (g : W → X → Y) (w : W)
    (I)
    (hf : Differentiable R (fun (w,y) => f w y))
    (hg : Σ' g' bg sg Sg, HasParamFDerivWithJumpsAt R g w g' I bg sg Sg) :
     Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R (fun w x => f w (g w x)) w f' I bf sf Sf :=

  let ⟨g',bg,sg,Sg,_⟩ := hg
  ⟨fun dw x =>
     let y := g w x
     let dy := g' dw x
     let dz := fderiv R (fun (w,y) => f w y) (w,y) (dw,dy)
     dz,
   fun i x =>
     let (y₁, y₂) := bg i x
     (f w y₁, f w y₂),
   sg, Sg, sorry_proof⟩


@[aesop unsafe]
noncomputable
def comp_smooth_jumps_rule'
    (f : W → Y → Z) (g : W → X → Y) (w : W)
    (hf : Differentiable R (fun (w,y) => f w y))
    (hg : HasParamFDerivWithJumpsAt' R g w) :
    HasParamFDerivWithJumpsAt' R (fun w x => f w (g w x)) w :=

  let ⟨I,g',bg,sg,Sg,_⟩ := hg
  {
    I := I

    f' := fun dw x =>
      let y := g w x
      let dy := g' dw x
      let dz := fderiv R (fun (w,y) => f w y) (w,y) (dw,dy)
      dz

    jumpVals := fun i x =>
      let (y₁, y₂) := bg i x
      (f w y₁, f w y₂)

    jumpSpeed := sg
    jump := Sg

    proof := sorry_proof
  }


end HasParamFDerivWithJumpsAt


----------------------------------------------------------------------------------------------------
-- Function Rules ----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- TODO: Add condition that the intersection of `⋃ i, Sf i` and `⋃ i, Sg i` has zero (n-1)-measure
def Prod.mk.arg_self.HasParamFDerivWithJumpsAt_rule
    (f g : W → X → Y) (w : W)
    (I J)
    (hf : Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : Σ' g' bg sg Sg, HasParamFDerivWithJumpsAt R g w g' J bg sg Sg) :
    Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R (fun w x => (f w x, g w x)) w f' (I⊕J) bf sf Sf :=

  let ⟨f', bf, sf, Sf, _⟩ := hf
  let ⟨g', bg, sg, Sg, _⟩ := hg
  ⟨fun dw x => (f' dw x, g' dw x),
   fun i =>
     match i with
     | .inl i =>
       fun x =>
         let (y₁, y₂) := bf i x
         let z := g w x
         ((y₁,z), (y₂,z))
     | .inr j =>
       fun x =>
         let y := f w x
         let (z₁, z₂) := bg j x
         ((y,z₁), (y,z₂)),
   fun i =>
     match i with
     | .inl i => (sf i ·)
     | .inr j => (sg j ·),
   fun i =>
     match i with
     | .inl i => Sf i
     | .inr j => Sg j,
   sorry_proof⟩


-- An alternative way to formulate this
-- This is probably preferable by default if we do not need to share some precomputed data among output parameters
theorem Prod.mk.arg_self.HasParamFDerivWithJumpsAt_rule'
    (f g : W → X → Y) (w : W)
    (f' I bf sf Sf) (g' J bg sg Sg)
    (hf : HasParamFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : HasParamFDerivWithJumpsAt R g w g' J bg sg Sg) :
    HasParamFDerivWithJumpsAt R (fun w x => (f w x, g w x)) w
      (fun dw x => (f' dw x, g' dw x))
      (I⊕J)
      /- jumpVals-/
      (fun i =>
         match i with
         | .inl i =>
           fun x =>
             let (y₁, y₂) := bf i x
             let z := g w x
             ((y₁,z), (y₂,z))
         | .inr j =>
           fun x =>
             let y := f w x
             let (z₁, z₂) := bg j x
             ((y,z₁), (y,z₂)))
      /- jumpSpeed -/
      (fun i =>
         match i with
         | .inl i => (sf i ·)
         | .inr j => (sg j ·))
      /- jump -/
      (fun i =>
         match i with
         | .inl i => Sf i
         | .inr j => Sg j) := sorry_proof

-- An alternative way to formulate this
-- This is probably preferable by default if we do not need to share some precomputed data among output parameters
abbrev Prod.mk.arg_self.HasParamFDerivWithJumpsAt_rule''
    (f g : W → X → Y) (w : W)
    (hf : HasParamFDerivWithJumpsAt' R f w)
    (hg : HasParamFDerivWithJumpsAt' R g w) :
    HasParamFDerivWithJumpsAt' R (fun w x => (f w x, g w x)) w :=

  let ⟨I, f', bf, sf, Sf, _⟩ := hf
  let ⟨J, g', bg, sg, Sg, _⟩ := hg
  {
    I :=I⊕J
    f' := fun dw x =>
      (f' dw x, g' dw x)

    jumpVals := Sum.elim
        (fun i x =>
          let (y₁, y₂) := bf i x
          let z := g w x
          ((y₁,z), (y₂,z)))
        (fun j x =>
          let y := f w x
          let (z₁, z₂) := bg j x
          ((y,z₁), (y,z₂)))

    jumpSpeed := Sum.elim sf sg

    jump := Sum.elim Sf Sg

    proof := sorry_proof
  }


def Prod.fst.arg_self.HasParamFDerivWithJumpsAt_rule
    (f : W → X → Y×Z) (w : W)
    (I)
    (hf : Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R f w f' I bf sf Sf) :
    Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R (fun w x => (f w x).1) w f' I bf sf Sf :=

  let ⟨f', bf, sf, Sf, _⟩ := hf
  ⟨fun dw x => (f' dw x).1,
   fun i x =>
       let (y₁, y₂) := bf i x
       (y₁.1, y₂.1),
   sf, Sf,
   sorry_proof⟩


def Prod.snd.arg_self.HasParamFDerivWithJumpsAt_rule
    (f : W → X → Y×Z) (w : W)
    (I)
    (hf : Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R f w f' I bf sf Sf) :
    Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R (fun w x => (f w x).2) w f' I bf sf Sf :=

  let ⟨f', bf, sf, Sf, _⟩ := hf
  ⟨fun dw x => (f' dw x).2,
   fun i x =>
       let (y₁, y₂) := bf i x
       (y₁.2, y₂.2),
   sf, Sf,
   sorry_proof⟩


-- TODO: Add condition that the intersection of `⋃ i, Sf i` and `⋃ i, Sg i` has zero (n-1)-measure
def HAdd.hAdd.arg_a0a1.HasParamFDerivWithJumpsAt_rule
    (f g : W → X → Y) (w : W)
    (I J)
    (hf : Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : Σ' g' bg sg Sg, HasParamFDerivWithJumpsAt R g w g' J bg sg Sg) :
    Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R (fun w x => f w x + g w x) w f' (I⊕J) bf sf Sf :=

  let ⟨f', bf, sf, Sf, _⟩ := hf
  let ⟨g', bg, sg, Sg, _⟩ := hg
  ⟨fun dw x => (f' dw x + g' dw x),
   fun i =>
     match i with
     | .inl i =>
       fun x =>
         let (y₁, y₂) := bf i x
         let z := g w x
         ((y₁+z), (y₂+z))
     | .inr j =>
       fun x =>
         let y := f w x
         let (z₁, z₂) := bg j x
         ((y+z₁), (y+z₂)),
   fun i =>
     match i with
     | .inl i => (sf i ·)
     | .inr j => (sg j ·),
   fun i =>
     match i with
     | .inl i => Sf i
     | .inr j => Sg j,
   sorry_proof⟩

-- An alternative way to formulate this
-- This is probably preferable by default if we do not need to share some precomputed data among output parameters
abbrev HAdd.hAdd.arg_self.HasParamFDerivWithJumpsAt_rule''
    (f g : W → X → Y) (w : W)
    (hf : HasParamFDerivWithJumpsAt' R f w)
    (hg : HasParamFDerivWithJumpsAt' R g w) :
    HasParamFDerivWithJumpsAt' R (fun w x => f w x + g w x) w :=

  let ⟨I, f', bf, sf, Sf, _⟩ := hf
  let ⟨J, g', bg, sg, Sg, _⟩ := hg
  {
    I :=I⊕J

    f' := fun dw x =>
      (f' dw x + g' dw x)

    jumpVals := Sum.elim
        (fun i x =>
          let (y₁, y₂) := bf i x
          let z := g w x
          ((y₁+z), (y₂+z)))
        (fun j x =>
          let y := f w x
          let (z₁, z₂) := bg j x
          ((y+z₁), (y+z₂)))

    jumpSpeed := Sum.elim sf sg

    jump := Sum.elim Sf Sg

    proof := sorry_proof
  }


-- An alternative way to formulate this
-- This is probably preferable by default if we do not need to share some precomputed data among output parameters
abbrev HSub.hSub.arg_self.HasParamFDerivWithJumpsAt_rule''
    (f g : W → X → Y) (w : W)
    (hf : HasParamFDerivWithJumpsAt' R f w)
    (hg : HasParamFDerivWithJumpsAt' R g w) :
    HasParamFDerivWithJumpsAt' R (fun w x => f w x - g w x) w :=

  let ⟨I, f', bf, sf, Sf, _⟩ := hf
  let ⟨J, g', bg, sg, Sg, _⟩ := hg
  {
    I :=I⊕J

    f' := fun dw x =>
      (f' dw x - g' dw x)

    jumpVals := Sum.elim
        (fun i x =>
          let (y₁, y₂) := bf i x
          let z := g w x
          ((y₁-z), (y₂-z)))
        (fun j x =>
          let y := f w x
          let (z₁, z₂) := bg j x
          ((y-z₁), (y-z₂)))

    jumpSpeed := Sum.elim sf sg

    jump := Sum.elim Sf Sg

    proof := sorry_proof
  }




-- TODO: Add condition that the intersection of `⋃ i, Sf i` and `⋃ i, Sg i` has zero (n-1)-measure
def HSub.hSub.arg_a0a1.HasParamFDerivWithJumpsAt_rule
    (f g : W → X → Y) (w : W)
    (I J)
    (hf : Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : Σ' g' bg sg Sg, HasParamFDerivWithJumpsAt R g w g' J bg sg Sg) :
    Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R (fun w x => f w x - g w x) w f' (I⊕J) bf sf Sf :=

  let ⟨f', bf, sf, Sf, _⟩ := hf
  let ⟨g', bg, sg, Sg, _⟩ := hg
  ⟨fun dw x => (f' dw x - g' dw x),
   fun i =>
     match i with
     | .inl i =>
       fun x =>
         let (y₁, y₂) := bf i x
         let z := g w x
         ((y₁-z), (y₂-z))
     | .inr j =>
       fun x =>
         let y := f w x
         let (z₁, z₂) := bg j x
         ((y-z₁), (y-z₂)),
   fun i =>
     match i with
     | .inl i => (sf i ·)
     | .inr j => (sg j ·),
   fun i =>
     match i with
     | .inl i => Sf i
     | .inr j => Sg j,
   sorry_proof⟩


def Neg.neg.arg_a0a1.HasParamFDerivWithJumpsAt_rule
    (f : W → X → Y) (w : W)
    (I)
    (hf : Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R f w f' I bf sf Sf) :
    Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R (fun w x => - f w x) w f' I bf sf Sf :=

  let ⟨f', bf, sf, Sf, _⟩ := hf
  ⟨fun dw x => - f' dw x,
   fun i x => - bf i x,
   sf, Sf,
   sorry_proof⟩


-- TODO: Mul condition that the intersection of `⋃ i, Sf i` and `⋃ i, Sg i` has zero (n-1)-measure
def HMul.hMul.arg_a0a1.HasParamFDerivWithJumpsAt_rule
    (f g : W → X → R) (w : W)
    (I J)
    (hf : Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : Σ' g' bg sg Sg, HasParamFDerivWithJumpsAt R g w g' J bg sg Sg) :
    Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R (fun w x => f w x * g w x) w f' (I⊕J) bf sf Sf :=

  let ⟨f', bf, sf, Sf, _⟩ := hf
  let ⟨g', bg, sg, Sg, _⟩ := hg
  ⟨fun dw x =>
     let y := f w x
     let dy := f' dw x
     let z := g w x
     let dz := g' dw x
     dy * z + y * dz,
   fun i =>
     match i with
     | .inl i =>
       fun x =>
         let (y₁, y₂) := bf i x
         let z := g w x
         ((y₁*z), (y₂*z))
     | .inr j =>
       fun x =>
         let y := f w x
         let (z₁, z₂) := bg j x
         ((y*z₁), (y*z₂)),
   fun i =>
     match i with
     | .inl i => (sf i ·)
     | .inr j => (sg j ·),
   fun i =>
     match i with
     | .inl i => Sf i
     | .inr j => Sg j,
   sorry_proof⟩


-- TODO: Mul condition that the intersection of `⋃ i, Sf i` and `⋃ i, Sg i` has zero (n-1)-measure
def HSMul.hSMul.arg_a0a1.HasParamFDerivWithJumpsAt_rule
    (f : W → X → R) (g : W → X → Y) (w : W)
    (I J)
    (hf : Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : Σ' g' bg sg Sg, HasParamFDerivWithJumpsAt R g w g' J bg sg Sg) :
    Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R (fun w x => f w x • g w x) w f' (I⊕J) bf sf Sf :=

  let ⟨f', bf, sf, Sf, _⟩ := hf
  let ⟨g', bg, sg, Sg, _⟩ := hg
  ⟨fun dw x =>
     let y := f w x
     let dy := f' dw x
     let z := g w x
     let dz := g' dw x
     dy • z + y • dz,
   fun i =>
     match i with
     | .inl i =>
       fun x =>
         let (y₁, y₂) := bf i x
         let z := g w x
         ((y₁•z), (y₂•z))
     | .inr j =>
       fun x =>
         let y := f w x
         let (z₁, z₂) := bg j x
         ((y•z₁), (y•z₂)),
   fun i =>
     match i with
     | .inl i => (sf i ·)
     | .inr j => (sg j ·),
   fun i =>
     match i with
     | .inl i => Sf i
     | .inr j => Sg j,
   sorry_proof⟩


-- TODO: Div condition that the intersection of `⋃ i, Sf i` and `⋃ i, Sg i` has zero (n-1)-measure
def HDiv.hDiv.arg_a0a1.HasParamFDerivWithJumpsAt_rule
    (f g : W → X → R) (w : W)
    (I J)
    (hf : Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R f w f' I bf sf Sf)
    (hg : Σ' g' bg sg Sg, HasParamFDerivWithJumpsAt R g w g' J bg sg Sg)
    (hg' : ∀ x, g w x ≠ 0) :
    Σ' f' bf sf Sf, HasParamFDerivWithJumpsAt R (fun w x => f w x / g w x) w f' (I⊕J) bf sf Sf :=

  let ⟨f', bf, sf, Sf, _⟩ := hf
  let ⟨g', bg, sg, Sg, _⟩ := hg
  ⟨fun dw x =>
     let y := f w x
     let dy := f' dw x
     let z := g w x
     let dz := g' dw x
     (z^2)⁻¹ * (dy * z - y * dz),
   fun i =>
     match i with
     | .inl i =>
       fun x =>
         let (y₁, y₂) := bf i x
         let z := g w x
         ((y₁/z), (y₂/z))
     | .inr j =>
       fun x =>
         let y := f w x
         let (z₁, z₂) := bg j x
         ((y/z₁), (y/z₂)),
   fun i =>
     match i with
     | .inl i => (sf i ·)
     | .inr j => (sg j ·),
   fun i =>
     match i with
     | .inl i => Sf i
     | .inr j => Sg j,
   sorry_proof⟩
