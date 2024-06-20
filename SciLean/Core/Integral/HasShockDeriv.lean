import SciLean.Notation
import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation
import SciLean.Core.Functions.Trigonometric

import SciLean.Tactic.LetUtils
import SciLean.Tactic.LetEnter
import SciLean.Tactic.TimeTactic
import SciLean.Tactic.LSimp

import SciLean.Core.Integral.CIntegral
import SciLean.Core.Integral.Surface
import SciLean.Core.Integral.RestrictToLevelSet
import SciLean.Core.Integral.VectorIntegral
import SciLean.Core.Integral.Common

import SciLean.Tactic.GTrans

import Mathlib.MeasureTheory.Decomposition.Lebesgue

open MeasureTheory FiniteDimensional

namespace SciLean

variable
  {R} [RealScalar R] [MeasureSpace R]
  {W} [Vec R W] [Module ℝ W]
  {S} [Vec R S]
  {W'} [Vec R W']
  {X} [SemiHilbert R X] [MeasurableSpace X]
  {Y} [Vec R Y] [Module ℝ Y]
  {Z} [Vec R Z] [Module ℝ Z]
  {U} [Vec R U] [Module ℝ U]
  {V} [Vec R V] [Module ℝ V]


set_default_scalar R

open Topology

variable (R)


-- @[data_synth]
/-- Function `f` as derivative almost everywhere in `x` except at finite collection of
(n-1)-dimensional surfaces(discontinuities/shocks).

Output parameters:
- `I` set indexing shocks
- `fderiv` derivative of `f` in `w` at point `w` and direction `dw` away from shocks
- `fshockvals i x` value of `f` on both sides
- `shockspeed i x` speed of `shock i` (has valid value only if `x ∈ shock i`)
- `shock i` set definig a shock, should be (n-1)-dimensional surface
-/
structure HasShockDeriv
    (f : W → X → Y) (w dw : W)
    (I : outParam Type) -- set indexing shock interfaces
    (fderiv : outParam (X → Y))                    -- derivative away from shock interfaces
    (fshockvals : outParam (I → X → Y×Y))         -- function values on both sides of shock
    (shockspeed : outParam (I → X → R))           -- shock speed in normal direction, well defined only on shock inteface
    (shock : outParam (I → Set X))                 -- shock interfaces - should be (n-1)-dimensional surfaces
    : Prop where


instance : IndexType Empty := sorry


@[aesop unsafe]
noncomputable
def shock_deriv_empty {X} [SemiHilbert R X] [MeasureSpace X]
    (w dw : W)
    (f : W → X → Y) (hf : ∀ x, CDifferentiableAt R (f · x) w)
    /- some integrability condition -/ :
    Σ' f' bf sf Sf, HasShockDeriv R f w dw Empty f' bf sf Sf :=

  ⟨fun x => ∂ (w':=w;dw), f w' x,
   0, 0, fun _ => ∅, sorry_proof⟩


noncomputable
example {X} [SemiHilbert R X] [MeasureSpace X]
    (w dw : W)
    (f : W → X → Y) (hf : ∀ x, CDifferentiableAt R (f · x) w)
    /- some integrability condition -/ :
    Σ' f' bf sf Sf, HasShockDeriv R f w dw Empty f' bf sf Sf := by aesop



noncomputable
def shock_deriv_comp {X} [SemiHilbert R X] [MeasureSpace X]
    (w dw : W)
    (f : W → Y → Z) (g : W → X → Y)
    (I)
    (hf : CDifferentiable R (fun (w,y) => f w y))
    (hg : Σ' g' bg sg Sg, HasShockDeriv R g w dw I g' bg sg Sg) :
     Σ' f' bf sf Sf, HasShockDeriv R (fun w x => f w (g w x)) w dw I f' bf sf Sf :=

  let ⟨g',bg,sg,Sg,_⟩ := hg
  ⟨fun x =>
    let y := g w x
    let dy := g' x
    let dz := ∂ (wy':=(w,y);(dw,dy)), f wy'.1 wy'.2
    dz,
   fun i x =>
     let (y₁, y₂):= bg i x
     (f w y₁, f w y₂),
   sg,
   Sg,
   sorry_proof⟩


@[aesop safe]
noncomputable
def shock_deriv_sin {X} [SemiHilbert R X] [MeasureSpace X]
    (w dw : W)
    (g : W → X → R)
    (I)
    (hg : Σ' g' bg sg Sg, HasShockDeriv R g w dw I g' bg sg Sg) :
     Σ' f' bf sf Sf, HasShockDeriv R (fun w x => Scalar.sin (g w x)) w dw I f' bf sf Sf :=

  let ⟨g',bg,sg,Sg,_⟩ := hg
  ⟨fun x =>
    let y := g w x
    let dy := g' x
    let dz := dy * Scalar.cos y
    dz,
   fun i x =>
     let (y₁, y₂):= bg i x
     (Scalar.sin y₁, Scalar.sin y₂),
   sg,
   Sg,
   sorry_proof⟩

@[aesop safe]
noncomputable
def shock_deriv_pow {X} [SemiHilbert R X] [MeasureSpace X]
    (w dw : W)
    (g : W → X → R) (n : ℕ)
    (I)
    (hg : Σ' g' bg sg Sg, HasShockDeriv R g w dw I g' bg sg Sg) :
     Σ' f' bf sf Sf, HasShockDeriv R (fun w x => (g w x)^n) w dw I f' bf sf Sf :=

  let ⟨g',bg,sg,Sg,_⟩ := hg
  ⟨fun x =>
    let y  := g w x
    let dy := g' x
    let dz := dy * n * y^(n-1)
    dz,
   fun i x =>
     let (y₁, y₂) := bg i x
     (y₁^n, y₂^n),
   sg,
   Sg,
   sorry_proof⟩



@[aesop safe]
noncomputable
def shock_deriv_mul {X} [SemiHilbert R X] [MeasureSpace X]
    (w dw : W)
    (f g : W → X → R)
    (I J)
    (hf : Σ' f' bf sf Sf, HasShockDeriv R f w dw I f' bf sf Sf)
    (hg : Σ' g' bg sg Sg, HasShockDeriv R g w dw J g' bg sg Sg) :
    Σ' f' bf sf Sf, HasShockDeriv R (fun w x => f w x * g w x) w dw (I⊕J) f' bf sf Sf :=

  let ⟨f', bf, sf, Sf, _⟩ := hf
  let ⟨g', bg, sg, Sg, _⟩ := hg
  ⟨fun x =>
     let y := f w x
     let dy := f' x
     let z := g w x
     let dz := g' x
     dy * z + y * dz,
   fun i =>
     match i with
     | .inl i =>
       fun x =>
         let (y₁, y₂) := bf i x
         let z := g w x
         (y₁ * z, y₂ * z)
     | .inr j =>
       fun x =>
         let y := f w x
         let (z₁, z₂) := bg j x
         (y * z₁, y * z₂),
   fun i =>
     match i with
     | .inl i => (sf i ·)
     | .inr j => (sg j ·),
   fun i =>
     match i with
     | .inl i => Sf i
     | .inr j => Sg j,
   sorry_proof⟩


@[aesop safe]
noncomputable
def shock_deriv_add {X} [SemiHilbert R X] [MeasureSpace X]
    (w dw : W)
    (f g : W → X → R)
    (I J)
    (hf : Σ' f' bf sf Sf, HasShockDeriv R f w dw I f' bf sf Sf)
    (hg : Σ' g' bg sg Sg, HasShockDeriv R g w dw J g' bg sg Sg) :
    Σ' f' bf sf Sf, HasShockDeriv R (fun w x => f w x + g w x) w dw (I⊕J) f' bf sf Sf :=

  let ⟨f', bf, sf, Sf, _⟩ := hf
  let ⟨g', bg, sg, Sg, _⟩ := hg
  ⟨fun x =>
     let dy := f' x
     let dz := g' x
     dy + dz,
   fun i =>
     match i with
     | .inl i =>
       fun x =>
         let (y₁, y₂) := bf i x
         let z := g w x
         (y₁ + z, y₂ + z)
     | .inr j =>
       fun x =>
         let y := f w x
         let (z₁, z₂) := bg j x
         (y + z₁, y + z₂),
   fun i =>
     match i with
     | .inl i => (sf i ·)
     | .inr j => (sg j ·),
   fun i =>
     match i with
     | .inl i => Sf i
     | .inr j => Sg j,
   sorry_proof⟩


@[aesop safe]
noncomputable
def shock_deriv_sub {X} [SemiHilbert R X] [MeasureSpace X]
    (w dw : W)
    (f g : W → X → R)
    (I J)
    (hf : Σ' f' bf sf Sf, HasShockDeriv R f w dw I f' bf sf Sf)
    (hg : Σ' g' bg sg Sg, HasShockDeriv R g w dw J g' bg sg Sg) :
    Σ' f' bf sf Sf, HasShockDeriv R (fun w x => f w x - g w x) w dw (I⊕J) f' bf sf Sf :=

  let ⟨f', bf, sf, Sf, _⟩ := hf
  let ⟨g', bg, sg, Sg, _⟩ := hg
  ⟨fun x =>
     let dy := f' x
     let dz := g' x
     dy - dz,
   fun i =>
     match i with
     | .inl i =>
       fun x =>
         let (y₁, y₂) := bf i x
         let z := g w x
         (y₁ - z, y₂ - z)
     | .inr j =>
       fun x =>
         let y := f w x
         let (z₁, z₂) := bg j x
         (y - z₁, y - z₂),
   fun i =>
     match i with
     | .inl i => (sf i ·)
     | .inr j => (sg j ·),
   fun i =>
     match i with
     | .inl i => Sf i
     | .inr j => Sg j,
   sorry_proof⟩



@[aesop safe]
noncomputable
def shock_deriv_prod_mk {X} [SemiHilbert R X] [MeasureSpace X]
    (w dw : W)
    (f g : W → X → Y)
    (I J)
    (hf : Σ' f' bf sf Sf, HasShockDeriv R f w dw I f' bf sf Sf)
    (hg : Σ' g' bg sg Sg, HasShockDeriv R g w dw J g' bg sg Sg) :
    Σ' f' bf sf Sf, HasShockDeriv R (fun w x => (f w x, g w x)) w dw (I⊕J) f' bf sf Sf :=

  let ⟨f', bf, sf, Sf, _⟩ := hf
  let ⟨g', bg, sg, Sg, _⟩ := hg
  ⟨fun x => (f' x, g' x),
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


-- TODO: double check that the sign of the `shockvals` are aligned with shock speed `sf`
-- @[data_synth]
@[aesop safe]
noncomputable
def shock_deriv_ite {X} [SemiHilbert R X] [MeasureSpace X]
  (w dw : W)
  (f g : W → X → Y) (c : W → X → Prop) [∀ w x, Decidable (c w x)]
  (I J)
  (hf : Σ' f' bf sf Sf, HasShockDeriv R f w dw I f' bf sf Sf)
  (hg : Σ' g' bg sg Sg, HasShockDeriv R g w dw J g' bg sg Sg) :
   Σ' f' bf sf Sf, HasShockDeriv R (fun w x => if c w x then f w x else g w x) w dw (Unit⊕I⊕J) f' bf sf Sf :=
  let ⟨f',bf,sf,Sf,_⟩ := hf
  let ⟨g',bg,sg,Sg,_⟩ := hg
  ⟨fun x => if c w x then f' x else g' x,
   fun i =>
     match i with
     | .inl _ => fun x => (f w x, g w x)
     | .inr (.inl i) => (bf i ·)
     | .inr (.inr j) => (bg j ·),
   fun i =>
     match i with
     | .inl _ => frontierSpeed R (fun w => {x | c w x}) w dw
     | .inr (.inl i) => (sf i ·)
     | .inr (.inr j) => (sg j ·),
   fun i =>
     match i with
     | .inl _ => frontier {x | c w x}
     | .inr (.inl i) => Sf i ∩ interior {x | c w x}
     | .inr (.inr j) => Sg j ∩ interior {x | ¬ c w x},
   sorry_proof⟩


open FiniteDimensional
@[fun_trans]
theorem shock_deriv_under_integral {X} [AddCommGroup X] [Module R X] [MeasureSpace X]
  (f : W → X → Y) (μ : Measure X)
  (I) [hI : IndexType I]
  (hf : Σ' f' df s S, HasShockDeriv R f w dw I f' df s S) :
  (∂ (w':=w;dw), ∫' x, f w' x ∂μ)
  =
  let ⟨f', df, s, S, _⟩ := hf
  let interior := ∫' x, f' x ∂μ
  let density := fun x => Scalar.ofENNReal (R:=R) (μ.rnDeriv volume x)
  let shocks := ∑ i, ∫' x in S i, (s i x * density x) • ((df i x).1 - (df i x).2) ∂(surfaceMeasure (finrank R X - 1))
  interior + shocks := sorry_proof



@[ftrans_simp]
theorem sum_over_Sum {X} [AddCommMonoid X] {I J} [IndexType I] [IndexType J]
    (f : I ⊕ J → X) :
    ∑ i, f i
    =
    let s₁ := ∑ i, f (.inl i)
    let s₂ := ∑ j, f (.inr j)
    s₁ + s₂ := sorry_proof


@[ftrans_simp]
theorem sum_over_Unit {X} [AddCommMonoid X]
    (f : Unit → X) :
    ∑ i, f i
    =
    f () := sorry_proof


@[ftrans_simp]
theorem sum_over_Empty {X} [AddCommMonoid X]
    (f : Empty → X) :
    ∑ i, f i
    =
    0 := sorry_proof


macro "shock_deriv" : conv =>
  `(conv| (
    rw[shock_deriv_under_integral (R:=_) (f:=_) (μ:=_) (I:=_) (hI:=_)
       (hf:= by
         aesop (config := {enableSimp := false}) (add safe (by fun_prop)))]

    simp  (config:={zeta:=false}) only [shock_deriv_mul,shock_deriv_ite,shock_deriv_empty,shock_deriv_sin,shock_deriv_pow,shock_deriv_sub,shock_deriv_add]

    lsimp (config := {zeta:=false}) only [ftrans_simp]

    autodiff
    autodiff ))


#check
  (∂ (t : R), ∫' x, if x ≤ t then (1:R) else 0)
  rewrite_by

    unfold scalarCDeriv
    enter[t]

    shock_deriv


#check
  (∂ (t : R), ∫' x, Scalar.sin (if x ≤ t then t*x else t+x))
  rewrite_by

    unfold scalarCDeriv
    enter[t]

    shock_deriv


#check
  (∂ (t : R), ∫' x, (if x ≤ t then t*x else t+x) * (if x + 1 ≤ t then t-x else t*x))
  rewrite_by

    unfold scalarCDeriv
    enter[t]

    shock_deriv



#check
  (∂ (t : R), ∫' (x : R), let y := x*x*t; if x ≤ t then y + x*t*t + t else y * x)
  rewrite_by

    unfold scalarCDeriv
    enter[t]

    shock_deriv



#check (∂ fun ((a,b,μ) : R×R×R) => ∫' x,
          (gaussian μ (5:R) x * (if a ≤ x ∧ x ≤ b then 1 else 0) - gaussian 2 5 x)^2)
       rewrite_by
         enter[θ,dθ]
         shock_deriv



#check
  (∂ (t : R), ∫' x, (if x ≤ t then t*x else t+x) * (if x + 1 ≤ t then t-x else t*x) * (if x + 2 ≤ t then t*t*x else t*x))
  rewrite_by

    unfold scalarCDeriv
    enter[t]

    shock_deriv
