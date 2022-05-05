import SciLean.Core.Diff
import SciLean.Core.Adjoint
import SciLean.Core.AdjDiff
import SciLean.Core.Inv

import SciLean.Core.Functions.Operations

namespace SciLean

  variable {X} [Hilbert X]

  def normεp (ε : ℝ) (x : X) (p : ℝ) : ℝ := (∥x∥² + ε^2)^(p/2)
  argument x [Fact (ε≠0)]
    isSmooth     := sorry,
    diff_simp    := p/2 * ⟪dx, x⟫ * normεp ε x (p-2) by sorry,
    hasAdjDiff   := by constructor; infer_instance; simp[diff]; intro; infer_instance done,
    adjDiff_simp := p/2 * (dx' * normεp ε x (p-2)) * x by simp[adjDiff]; unfold hold; simp done

  notation "∥" x "∥{" ε "," p "}"  => normεp ε x p
  notation "∥" x "∥{" ε "}" => normεp ε x 1

  @[simp]
  theorem normεp.is_norm_at_zero (x : X) : ∥x∥{0} = ∥x∥ := sorry

  @[simp]
  theorem normεp.is_pow_at_zero (x : ℝ) (p : ℝ) [Fact (x > 0)] : ∥x∥{0,p} = x^p := sorry

  @[simp]
  theorem normεp.of_pow (x : X) (q p : ℝ) : ∥x∥{ε, q}^p = ∥x∥{ε, q * p} := sorry

  @[simp]
  theorem normεp.mul_is_add (x : X) (q p : ℝ) : ∥x∥{ε, q} * ∥x∥{ε, p} = ∥x∥{ε, q + p} := sorry

  -- Maybe this one needs `(ε ≠ 0) ???
  @[simp]
  theorem normεp.div_is_neg (r : ℝ) (x : X) (p : ℝ) : r / ∥x∥{ε, p} = r * ∥x∥{ε, - p} := sorry

  instance normεp.isNonNegative           (x : X) (p : ℝ) : Fact (∥x∥{ε,p} ≥ 0) := sorry
  instance normεp.isPositive [Fact (ε≠0)] (x : X) (p : ℝ) : Fact (∥x∥{ε,p} > 0) := sorry
