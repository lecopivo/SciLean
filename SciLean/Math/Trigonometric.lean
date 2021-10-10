import SciLean.Prelude

namespace Math

  instance : IsDiff sin := sorry
  @[simp] def sin.differentail (x dx : ℝ) : δ sin x dx = dx * cos x := sorry

  instance : IsDiff cos := sorry
  @[simp] def cos.differentail (x dx : ℝ) : δ cos x dx = -dx * sin x := sorry

end Math

@[simp] theorem cos_sin_unit (α : ℝ) : (Math.cos α) * (Math.cos α) + (Math.sin α) * (Math.sin α) = 1 := sorry
@[simp] theorem sin_cos_unit (α : ℝ) : (Math.sin α) * (Math.sin α) + (Math.cos α) * (Math.cos α) = 1 := sorry
