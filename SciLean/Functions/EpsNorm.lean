import SciLean.Core.Functions.Operations

namespace SciLean

  variable {X} [Hilbert X]

  def εnorm (ε : ℝ) (x : X) : ℝ := Math.sqrt (∥x∥² + ε^2)
  argument x [Fact (ε≠0)]
    isSmooth     := sorry,
    diff_simp    := ⟪dx, x⟫ / εnorm ε x by sorry,
    hasAdjDiff   := by constructor; infer_instance; simp[diff]; intro; infer_instance done,
    adjDiff_simp := (dx' / εnorm ε x) * x by (simp[adjDiff]; unfold hold; simp done)

  notation "∥" x "∥{" ε "}" => εnorm ε x

  @[simp]
  theorem εnorm.is_norm_at_zero (x : X) : ∥x∥{0} = ∥x∥ := sorry

  instance normεp.isNonNegative           (x : X) (p : ℝ) : Fact (∥x∥{ε} ≥ 0) := sorry
  instance normεp.isPositive [Fact (ε≠0)] (x : X) (p : ℝ) : Fact (∥x∥{ε} > 0) := sorry
