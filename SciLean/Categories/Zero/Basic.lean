import SciLean.Algebra

namespace SciLean

class IsZero {X} [Vec X] (x : X) : Prop where
  is_zero : x = 0

class NonZero {X} [Vec X] (x : X) : Prop where
  non_zero : x ≠ 0

class NonNeg (x : ℝ) : Prop where
  non_neg : 0 ≤ x

class IsPos (x : ℝ) extends NonZero x, NonNeg x

instance {X} [Vec X] : IsZero (0 : X) := ⟨by rfl⟩
