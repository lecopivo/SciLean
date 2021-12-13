import SciLean.Algebra

namespace SciLean.Mathlib.Convenient

  variable {X Y} [Vec X] [Vec Y]

  def is_smooth (f : X → Y) : Prop := sorry

  def integrate [Vec X] (a b : ℝ) (f : ℝ → X) (h : is_smooth f) : X := sorry
  
end SciLean.Mathlib.Convenient
