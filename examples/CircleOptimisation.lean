/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

Riemannian Gradient Descent on S1.
-/

import SciLean
open Lean
open SciLean



/-- choose a particular A -/
-- I want to build the function (x, y) -> (x + y, x - y)
-- Can I multiply it with the [1 1; -1 1] matrix? how do I do this in a way that SciLean
-- sees that it is manifestly smooth?
-- I took a look at `Pendulum2D.lean` which seems to not compile anymore.
def A (x : ℝ^{2}) : ℝ^{2} := 
  ⊞ i, 
    let x₀ := x.get 0
    let x₁ := x.get 1
    let x' := #[x₀ + x₁, x₀ - x₁];
    have H : x'.size = 2 := by simp;
    let x' := x'.get (H ▸ i.toFin)
    x'
/--
failed to synthesize instance
  IsSmooth fun x => A x
-/
function_properties A (x : ℝ^{2})
argument x
  IsLin := sorry_proof,
  HasAdjoint := sorry_proof,
  IsSmooth,
  abbrev ∂ := λ dx => A dx by sorry_proof,
  noncomputable abbrev † := λ x' => A† x' by sorry_proof,
  HasAdjDiff,
  noncomputable abbrev ∂† := λ dx' => A† dx' by sorry_proof

variable {n : USize}

set_option trace.Meta.Tactic.fun_trans.rewrite true in
#check (∇ x : ℝ^{n}, ⟪x, A x⟫)
           rewrite_by
             unfold gradient
             fun_trans
             simp
