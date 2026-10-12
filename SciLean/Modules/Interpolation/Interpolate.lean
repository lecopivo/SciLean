module

public import SciLean.Core

@[expose] public section


namespace SciLean

open Lean Meta Elab Tactic Conv

-- abbrev Interpolation (α β : Type) := ∀ {X : Type} [Vec X], (α → X) → (β → X)

@[inline]
def linearInterpolate1D {X} [Vec X] (f : Int → X) (x : ℝ) : X :=
  let ix := x.floor
  let w := x - ix
  let ix := ix.toInt
  let f₀ := f ix
  let f₁ := f (ix+1)
  f₀ + w • (f₁-f₀)

#exit
function_properties SciLean.linearInterpolate1D {X : Type} [Vec X] (f : Int → X) (x : ℝ)
argument f
  IsSmooth,
  abbrev ∂ := λ df => linearInterpolate1D df x
    by unfold linearInterpolate1D; simp; fun_trans,
  abbrev 𝒯 := λ df => (linearInterpolate1D f x, linearInterpolate1D df x)
    by unfold tangentMap; simp; fun_trans

argument x [UnsafeAD]
  IsSmooth := sorry_proof,
  def ∂ :=
    λ dx =>
      let ix := x.floorI
      let f₀ := f ix
      let f₁ := f (ix+1)
      dx • (f₁ - f₀)
    by sorry_proof,
  def 𝒯 :=
    λ dx => (linearInterpolate1D f x, ∂ x':=x;dx, linearInterpolate1D f x')
    rewrite_by
      fun_trans
      unfold linearInterpolate1D
      unfold linearInterpolate1D.arg_x.differential
      -- can we simplify this somehow and reuse computation?
    by
      unfold tangentMap;
      fun_trans
      simp [linearInterpolate1D,
            linearInterpolate1D.arg_x.differential]

function_properties SciLean.linearInterpolate1D {X : Type} [Hilbert X] (f : Int → X) (x : ℝ)
argument x [UnsafeAD]
  def ∂† :=
    let ix := x.floorI
    let f₀ := f ix
    let f₁ := f (ix+1)
    λ dx' => ⟪dx', (f₀ - f₁)⟫
    by
      ignore_fun_prop
      unfold adjointDifferential
      -- fun_trans -- FIX
      sorry_proof,
  abbrev ℛ :=
    (linearInterpolate1D f x, ∂† x':=x, linearInterpolate1D f x')
    rewrite_by
      fun_trans
      unfold linearInterpolate1D.arg_x.adjointDifferential
      unfold linearInterpolate1D
      -- can we simplify this somehow? and reuse some computations?
    by
      unfold reverseDifferential
      fun_trans
      simp[linearInterpolate1D,
           linearInterpolate1D.arg_x.adjointDifferential,
           Real.floorI]
