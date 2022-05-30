import SciLean.Core
import SciLean.Data.PowType
import SciLean.Functions.EpsPow
import SciLean.Functions.CrossProduct
import SciLean.Functions.Trigonometric

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 500000

namespace SciLean

  variable {X} [Hilbert X]

  def εsinr1Sqrt (ε : ℝ) (x : ℝ) : ℝ := ∥x∥^{-1/2, ε} * Math.sin ∥x∥^{1/2,ε}
  argument x [Fact (ε≠0)]
    isSmooth, diff, hasAdjDiff, adjDiff

  function_properties εsinr1Sqrt.arg_x.diff (ε : ℝ) [Fact (ε≠0)] (x : ℝ) (dx : ℝ) : ℝ
  argument x 
    isSmooth, diff, hasAdjDiff, adjDiff
  argument dx
    isLin := by simp[diff]; infer_instance done, 
    isSmooth, diff_simp, hasAdjDiff, adjDiff_simp


  def εcosr2Sqrt (ε :ℝ) (x : ℝ) : ℝ := (Math.cos ∥x∥^{1/2,ε} - 1) * ∥x∥^{-1, ε}
  argument x [Fact (ε≠0)]
    isSmooth, diff, hasAdjDiff, adjDiff

  function_properties εcosr2Sqrt.arg_x.diff (ε : ℝ) [Fact (ε≠0)] (x : ℝ) (dx : ℝ) : ℝ
  argument x 
    isSmooth, diff, hasAdjDiff, adjDiff
  argument dx
    isLin := by simp[diff]; infer_instance done, 
    isSmooth, diff_simp, hasAdjDiff, adjDiff_simp


  def εrotate (ε : ℝ) (ω x : ℝ^(3:ℕ)) : ℝ^(3:ℕ) := 
    x + εsinr1Sqrt ε ∥ω∥² * cross ω x - εcosr2Sqrt ε ∥ω∥² * cross ω (cross ω x)
  argument x
    isLin, isSmooth, diff_simp := εrotate ε ω dx by simp[εrotate],
    hasAdjoint, adj_simp := εrotate ε (-ω) x' by sorry,
    hasAdjDiff, adjDiff_simp := εrotate ε (-ω) dx' by simp[εrotate] admit
  argument ω [Fact (ε≠0)]
    isSmooth, diff, hasAdjDiff, adjDiff

  function_properties εrotate.arg_ω.diff (ε : ℝ) [Fact (ε≠0)] (ω dω x : ℝ^(3:ℕ)) : ℝ^(3:ℕ)
  argument x
    isLin := by simp[εrotate.arg_ω.diff]; infer_instance; done,
    isSmooth, diff_simp := εrotate.arg_ω.diff ε ω dω dx by simp[diff] done,
    hasAdjDiff, adjDiff
  argument ω
    isSmooth, diff, hasAdjDiff, adjDiff
  argument dω
    isLin := by simp[diff]; infer_instance; done,
    isSmooth, 
    diff_simp := εrotate.arg_ω.diff ε ω ddω x by simp[diff]; done,
    hasAdjoint := sorry, 
    adj_simp := εrotate.arg_ω.adjDiff ε ω dω' x by admit,
    hasAdjDiff, 
    adjDiff_simp := εrotate.arg_ω.adjDiff ε ω ddω' x by simp[SciLean.adjDiff]; unfold hold; simp done

