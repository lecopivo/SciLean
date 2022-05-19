import SciLean.Core

namespace SciLean

  def π : ℝ := 3.14159265359

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

  -- These are related to Spherical Bessle functions
  -- Also these are just sin and cos that are slowly pealing of terms in Taylor series
  def Math.sinr1 (x : ℝ) : ℝ := if x = 0 then 1     else Math.sin x / x
  def Math.sinr3 (x : ℝ) : ℝ := if x = 0 then -1/6  else (Math.sinr1 x - 1)   / (x*x)
  def Math.sinr5 (x : ℝ) : ℝ := if x = 0 then 1/120 else (Math.sinr3 x + 1/6) / (x*x)

  def Math.cosr2 (x : ℝ) : ℝ := if x = 0 then -1/2 else (Math.cos x   - 1)   / (x*x)
  def Math.cosr4 (x : ℝ) : ℝ := if x = 0 then 1/24 else (Math.cosr2 x + 1/2) / (x*x)

  abbrev Math.sinc := Math.sinr1

  function_properties Math.sinr1 (x : ℝ) : ℝ
  argument x 
    isSmooth := sorry,
    diff_simp := dx * (- x * Math.sinr3 x + x * Math.cosr2 x) by sorry,
    hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
    adjDiff_simp by simp[adjDiff]

  function_properties Math.cosr2 (x : ℝ) : ℝ
  argument x
    isSmooth := sorry,
    diff_simp := dx * (- x * Math.sinr3 x - 2 * x * Math.cosr4 x) by sorry,
    hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
    adjDiff_simp by simp[adjDiff]


  --------------------------------------------------------------------
  -- Sin and Cos with halfed powers

  def Math.sinr1Sqrt (x : ℝ) : ℝ := 
    if x = 0 then 1 else
    if x > 0 then Math.sinr1 (Math.sqrt x) 
    else panic! "Implement sinr1Sqrt for negative values!"
  def Math.sinr3Sqrt (x : ℝ) : ℝ := if x = 0 then -1/6  else (Math.sinr1Sqrt x - 1) / x
  def Math.sinr5Sqrt (x : ℝ) : ℝ := if x = 0 then 1/120 else (Math.sinr3Sqrt x + 1/6) / x

  def Math.cosSqrt (x : ℝ) : ℝ :=
    if (x≥0) then Math.cos (Math.sqrt x) else panic! "Implement cosSqrt for negative values!"
  def Math.cosr2Sqrt (x : ℝ) : ℝ := if x = 0 then -1/2 else (Math.cosSqrt x - 1)   / x
  def Math.cosr4Sqrt (x : ℝ) : ℝ := if x = 0 then 1/24 else (Math.cosr2Sqrt x + 1/2) / x

  function_properties Math.sinr1Sqrt (x : ℝ) : ℝ
  argument x
    isSmooth   := sorry,
    diff_simp  := dx/2 * (cosr2Sqrt x - sinr3Sqrt x) by sorry,
    hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
    adjDiff_simp by simp[adjDiff]; unfold hold; simp

  function_properties Math.cosSqrt (x : ℝ) : ℝ
  argument x
    isSmooth   := sorry,
    diff_simp  := -dx/2 * Math.sinr1Sqrt x by sorry,
    hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
    adjDiff_simp by simp[adjDiff]; unfold hold; simp

  function_properties Math.cosr2Sqrt (x : ℝ) : ℝ
  argument x 
    isSmooth  := sorry,
    diff_simp := -dx/2 * (sinr3Sqrt x + 2 * cosr4Sqrt x) by sorry,
    hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
    adjDiff_simp by simp[adjDiff]; unfold hold; simp

  @[simp]
  theorem Math.cos.of_norm_is_cosSqrt {X} [Hilbert X] (x : X) : Math.cos ∥x∥ = Math.cosSqrt ∥x∥² := sorry

  @[simp]
  theorem Math.sinc.of_norm_is_sinr1Sqrt {X} [Hilbert X] (x : X) : Math.sinc ∥x∥ = Math.sinr1Sqrt ∥x∥² := sorry

