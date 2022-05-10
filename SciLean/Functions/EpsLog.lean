import SciLean.Core
import SciLean.Functions.EpsNorm
import SciLean.Functions.EpsPow

namespace SciLean

  variable {X} [Hilbert X]

  def εlog (ε : ℝ) (x : X) : ℝ := (Math.log (∥x∥² + ε^2))/2
  argument x [Fact (ε≠0)]
    isSmooth     := sorry,
    diff_simp    := ⟪dx,x⟫ * ∥x∥^{(-2:ℝ),ε}  by sorry,
    hasAdjDiff   := by constructor; infer_instance; simp[diff]; intro; infer_instance done,
    adjDiff_simp := (dx' * εpow ε x (-2)) * x by (simp[adjDiff]; unfold hold; simp; done)

  function_properties εpow (ε : ℝ) (x : X) (y : ℝ) : ℝ
  argument y [Fact (ε≠0)]
    isSmooth := sorry,
    diff_simp := dy * (εlog ε x) * εpow ε x y by sorry,
    hasAdjDiff := by constructor; infer_instance; simp[diff]; intro; infer_instance done,
    adjDiff_simp := dy' * εpow ε x y * (εlog ε x) by (simp[adjDiff]; unfold hold; simp)

  notation  "log{" ε "}" x:max => εlog ε x

  @[simp]
  theorem εlog.is_log_at_zero (x : X)  : log{0} x = Math.log ∥x∥ := sorry

