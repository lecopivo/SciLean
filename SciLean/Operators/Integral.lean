import SciLean.Categories

namespace SciLean

open Mathlib Convenient in
noncomputable
def integral {X} [Vec X] (f : ℝ → X) (ab : ℝ × ℝ) : X 
  :=
    match Classical.propDecidable (IsSmooth f) with
      | isTrue  h => integrate ab.1 ab.2 (λ t => f t) h.1
      | _ => 0

macro "∫" xs:Lean.explicitBinders ", " b:term : term 
  => Lean.expandExplicitBinders `SciLean.integral xs b

variable (f : ℝ → ℝ → ℝ)

#check (∫ x y, f x y)




