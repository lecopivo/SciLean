import Mathlib

open MeasureTheory

variable
  {R} [IsROrC R]
  {X} [MeasureSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace R Y]

variable (f : X → Y)

/-
failed to synthesize instance
  NormedSpace ℝ Y
-/
#check ∫ x, f x

variable [NormedSpace ℝ Y]

#check ∫ x, f x -- works
