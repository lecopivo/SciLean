import SciLean.Core

namespace SciLean

  function_properties Math.exp (x : ℝ) : ℝ
  argument x
    isSmooth   := sorry, 
    diff_simp  := dx * Math.exp x by sorry,
    hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
    adjDiff_simp := dx' * Math.exp x by simp[adjDiff] done
