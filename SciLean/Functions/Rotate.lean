import SciLean.Core
import SciLean.Data.PowType
import SciLean.Functions.CrossProduct
import SciLean.Functions.Trigonometric

set_option synthInstance.maxSize 2048

namespace SciLean

  def rotate2d (θ : ℝ) (x : ℝ^(2:ℕ)) : ℝ^(2:ℕ) := 
    let c := Math.cos θ
    let s := Math.sin θ
    ⟨c * x.x - s * x.y, s * x.x + c * x.y⟩
  argument θ
    isSmooth, 
    diff_simp := dθ * rotate2d (θ - π/2) x by sorry,
    hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
    adjDiff_simp by simp[adjDiff]
  argument x 
    isLin := sorry, isSmooth, diff_simp,
    hasAdjoint := sorry,
    adj_simp := rotate2d (-θ) x' by sorry,
    hasAdjDiff := by constructor; infer_instance; simp; infer_instance done, 
    adjDiff_simp := rotate2d (-θ) dx' by sorry,
    isInv := sorry,
    inv_simp := rotate2d (-θ) x' by sorry

  def rotate3d (ω x : ℝ^(3:ℕ)) : ℝ^(3:ℕ) := 
    x + Math.sinr1Sqrt ∥ω∥² * (cross ω x) - Math.cosr2Sqrt ∥ω∥² * cross ω (cross ω x)
  argument ω
    isSmooth, diff, hasAdjDiff, adjDiff
  argument x 
    isSmooth, 
    diff_simp := rotate3d ω dx by simp[rotate3d] done,
    hasAdjoint := sorry,
    adj_simp := rotate3d (-ω) x' by sorry,
    hasAdjDiff, 
    adjDiff_simp := rotate3d (-ω) dx' by simp[SciLean.adjDiff] done,
    isInv := sorry,
    inv_simp := rotate3d (-ω) x' by sorry


  def rotate3d' (ω x : ℝ^(3:ℕ)) : ℝ^(3:ℕ) := 
    x + Math.sinr1Sqrt ∥ω∥² * (cross ω x) - Math.cosr2Sqrt ∥ω∥² * cross ω (cross ω x)
  argument x 
    isSmooth, 
    diff_simp := rotate3d' ω dx by simp[rotate3d'] done,
    hasAdjoint := sorry,
    adj_simp := rotate3d' (-ω) x' by sorry,
    hasAdjDiff, 
    adjDiff_simp := rotate3d' (-ω) dx' by simp[SciLean.adjDiff] done,
    isInv := sorry,
    inv_simp := rotate3d' (-ω) x' by sorry
  argument ω
    isSmooth, 
    diff_simp := 
      let R  := rotate3d' ω
      let W  := cross ω
      let W' := (-1:ℝ)/∥ω∥² * cross ω
      let R' := (R - R ∘ W + 1) ∘ W'
      let Q  := (1 - W - rotate3d' (-ω)) ∘ W'
      -- let Q' := (λ x => x - W (W' x))
      ((R' + R) ∘ cross dω) x
      -- let θ   := ∥ω∥
      -- let ω'  := 1/θ * ω
      -- let x'  := cross dω x
      -- let x'' := cross ω' x'
      -- 1/∥ω∥² * (rotate3d' ω x'' - x'') + (x' - cross ω' (cross ω' x'))
      by sorry,
    hasAdjDiff, adjDiff_simp by (simp[adjDiff]; unfold hold; simp)
  --   hasAdjDiff, adjDiff
  -- argument x 
  --   isSmooth, 
  --   diff_simp := rotate3d ω dx by simp[rotate3d] done,
  --   hasAdjoint := sorry,
  --   adj_simp := rotate3d (-ω) x' by sorry,
  --   hasAdjDiff, 
  --   adjDiff_simp := rotate3d (-ω) dx' by simp[SciLean.adjDiff] done,
  --   isInv := sorry,
  --   inv_simp := rotate3d (-ω) x' by sorry


