import SciLean.Core

namespace SciLean

  function_properties Math.sin (x : ℝ) : ℝ
  argument x
    isSmooth   := sorry, 
    diff_simp  := dx * Math.cos x by sorry,
    hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
    adjDiff_simp := dx' * Math.cos x by simp[adjDiff] done

  function_properties Math.cos (x : ℝ) : ℝ
  argument x
    isSmooth   := sorry, 
    diff_simp  := -dx * Math.sin x by sorry,
    hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
    adjDiff_simp := -dx' * Math.sin x by simp[adjDiff]; unfold hold; simp; admit
  
  
