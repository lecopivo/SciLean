import SciLean.Core
import SciLean.Functions.EpsNorm

namespace SciLean

  variable {X} [Hilbert X]

  def εpow (ε : ℝ) (x : X) (y : ℝ) : ℝ := Math.pow (∥x∥² + ε^2) (y/2)
  argument x [Fact (ε≠0)]
    isSmooth     := sorry,
    diff_simp    := y * ⟪dx, x⟫ * εpow ε x (y-2) by sorry,
    hasAdjDiff   := by constructor; infer_instance; simp; intro; infer_instance done,
    adjDiff_simp := (y * (dx' * εpow ε x (y-2))) * x by (simp[adjDiff]; unfold hold; simp; unfold hold; simp done)
  -- Defined in EpsLog.lean 
  -- argument y [Fact (ε≠0)]
  --   isSmooth := sorry,
  --   diff_simp := dy * (εlog ε x) * εpow ε x y by sorry

  notation  "∥" x "∥^{" y "," ε "}" => εpow ε x y

  @[simp]
  theorem εpow.is_εnorm_at_one (x : X) (ε : ℝ) : ∥x∥^{1,ε} = ∥x∥{ε} := sorry

  @[simp]
  theorem εpow.is_pow_at_zero (x : X) (y : ℝ)  : ∥x∥^{y,0} = ∥x∥^y := sorry

  theorem εpow.is_normSqr_at_two (x : X) (y : ℝ)  : ∥x∥^{(2:ℝ),ε} = ∥x∥² + ε^2 := sorry

  @[simp]
  theorem εpow.recip_εnorm_is_εpow (x : X) (ε : ℝ) (c : ℝ) : c/∥x∥{ε} = c * ∥x∥^{-1,ε} := sorry

  instance εpow.isNonNegative           (x : X) (y : ℝ) : Fact (∥x∥^{y,ε} ≥ 0) := sorry
  instance εpow.isPositive [Fact (ε≠0)] (x : X) (y : ℝ) : Fact (∥x∥^{y,ε} > 0) := sorry

  @[simp]
  theorem εpow.is_pow_of_εnorm (ε : ℝ) [Fact (ε≠0)] (x : X) (y : ℝ) : ∥x∥{ε}^y = ∥x∥^{y,ε} := sorry
  
