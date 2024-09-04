import Mathlib.Data.Fintype.Quotient

/-!

This files contains missing API for `Quotient`.

Hopefully this PR gets merged to mathlib and this file won't be necessary
https://github.com/leanprover-community/mathlib4/pull/5576

-/

namespace Quotient

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [S : ∀ i, Setoid (α i)] {β : Sort*}

/-- Lift a function on `∀ i, α i` to a function on `∀ i, Quotient (S i)`. -/
def finLiftOn (q : ∀ i, Quotient (S i)) (f : (∀ i, α i) → β)
    (h : ∀ (a b : ∀ i, α i), (∀ i, a i ≈ b i) → f a = f b) : β :=
  (Quotient.finChoice q).liftOn (β:=β) f h
