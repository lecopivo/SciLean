import SciLean.Categories

namespace SciLean

open Mathlib Convenient in
noncomputable
def integral {X} [Vec X] (f : ℝ ⟿ X) (ab : ℝ × ℝ) : X 
  :=
    integrate ab.1 ab.2 (λ t => f t) f.2.1

open Mathlib Convenient in
noncomputable
def integral! {X} [Vec X] (f : ℝ → X) (ab : ℝ × ℝ) : X 
  :=
    match Classical.propDecidable (IsSmooth f) with
      | isTrue  h => integral ⟨f, h⟩ ab
      | _ => 0

macro "∫!" xs:Lean.explicitBinders ", " b:term : term 
  => Lean.expandExplicitBinders `SciLean.integral! xs b

noncomputable
abbrev mkIntegral {X} [Vec X] (f : ℝ → X) [IsSmooth f] := integral ⟨f, by infer_instance⟩ 

macro "∫" xs:Lean.explicitBinders ", " b:term : term 
  => Lean.expandExplicitBinders `SciLean.mkIntegral xs b

-- variable (f : ℝ → ℝ → ℝ)

-- #check (∫! x y, f x y) (0,1) (0,1)

variable (f : ℝ ⟿ ℝ ⟿ ℝ)

instance {X} [Vec X] : IsLin (integral : (ℝ ⟿ X) → ℝ × ℝ → X) := sorry
instance {X} [Vec X] : IsLin (λ f : (ℝ ⟿ X) => ∫ t, f t) := sorry

-- instance {X} [Vec X] : IsLin (integral! : (ℝ → X) → ℝ × ℝ → X) := sorry
instance {X} [Vec X] : IsLin (λ f : (ℝ ⟿ X) => ∫! t, f t) := sorry

example : IsSmooth (λ x y => f y x) := by infer_instance
example : IsSmooth (λ x y : ℝ => f (y + x) y) := by infer_instance

-- #check ∫ y, (∫ x, λ y ⟿ f x y)

#check ∫ x, f x


--  δ δ!  |  ∇ ∇!  |  ∫ ∫!  |  † †!

namespace Integral
  
  -- @[simp]
  -- theorem integral_to_inner {X S} [Vec S.R] [SemiHilbert' X S] (f : ℝ ⟿ ℝ)
  --   : 
  --     ∫ t, f t = ⟪f,  ⟫




