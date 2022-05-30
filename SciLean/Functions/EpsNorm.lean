import SciLean.Core

namespace SciLean

  variable {X} [Hilbert X]

  def εnorm (ε : ℝ) (x : X) : ℝ := Math.sqrt (∥x∥² + ε^2)
  argument x [Fact (ε≠0)]
    isSmooth     := sorry,
    diff_simp    := ⟪dx, x⟫ / εnorm ε x by sorry,
    hasAdjDiff   := by constructor; infer_instance; simp; intro; infer_instance done,
    adjDiff_simp := (dx' / εnorm ε x) * x by (simp[adjDiff]; unfold hold; simp done)

  notation "∥" x "∥{" ε "}" => εnorm ε x

  @[simp]
  theorem εnorm.is_norm_at_zero (x : X) : ∥x∥{0} = ∥x∥ := sorry

  instance εnorm.isNonNegative           (x : X) : Fact (∥x∥{ε} ≥ 0) := sorry
  instance εnorm.isPositive [Fact (ε≠0)] (x : X) : Fact (∥x∥{ε} > 0) := sorry
  
  instance εnorm.pow.arg_x.isSmooth   [Fact (ε≠0)] : IsSmooth λ (x : X) (y : ℝ) => ∥x∥{ε}^y := sorry
  instance εnorm.pow.arg_x.hasAdjDiff [Fact (ε≠0)] (y : ℝ) : IsSmooth λ (x : X) => ∥x∥{ε}^y := sorry
  @[simp] theorem εnorm.pow.arg_x.diff_simp [Fact (ε≠0)] 
    : (δ λ (x : X) (y : ℝ) => ∥x∥{ε}^y) = λ x dx y => (y * ⟪dx,x⟫) * ∥x∥{ε}^(y-(2:ℝ)) := sorry
  @[simp] theorem εnorm.pow.arg_x.fwdDiff_simp [Fact (ε≠0)] (y : ℝ) 
    : (δ† λ (x : X) => ∥x∥{ε}^y) = λ (x : X) dx' => (y * dx' * ∥x∥{ε}^(y-(2:ℝ))) * x := sorry
