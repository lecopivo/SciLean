import SciLean.Core.Vec
import SciLean.Core.Hilbert

namespace SciLean.Mathlib.Convenient

  variable {X Y Z} [Vec X] [Vec Y] [Vec Z]

  opaque is_smooth (f : X → Y) : Prop

  noncomputable 
  opaque derivative (f : X → Y) (h : is_smooth f) (x dx : X) : Y

  opaque is_smooth_at (f : X → Y) (x : X) : Prop

  opaque integrate [Vec X] (a b : ℝ) (f : ℝ → X) (h : is_smooth f) : X


  -- Maybe that the adjoint `f'` also preserves test functions? Or can we conclude that?
  structure has_adjoint {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) : Prop where
    preserve_test_functions : ∀ x, TestFun x → TestFun (f x)
    has_adjoint : ∃ f' : Y → X, ∀ (ϕ : X) (ψ : Y), (TestFun ϕ ∨ TestFun ψ) → ⟪f ϕ, ψ⟫ = ⟪ϕ, f' ψ⟫

 
end SciLean.Mathlib.Convenient
