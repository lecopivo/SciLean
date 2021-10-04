import SciLean.Prelude

namespace Math

  def exp : ℝ → ℝ := Float.exp

  instance : IsDiff exp := sorry
  @[simp] def exp.differentail (x dx : ℝ) : δ exp x dx = dx * exp x := sorry

end Math
