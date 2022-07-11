import SciLean.Core
import SciLean.Data.PowType

namespace SciLean

  -- def cross (x y : ℝ^{3}) : ℝ^{3} := 
  --   Vec3.mk (x.y*y.z - x.z*y.y) (x.z*y.x - x.x*y.z) (x.x*y.y - x.y*y.x)
  -- argument x
  --   isLin := sorry, isSmooth, diff_simp, 
  --   hasAdjoint := sorry, 
  --   adj_simp := cross y x' by sorry,
  --   hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
  --   adjDiff_simp by simp[adjDiff]
  -- argument y
  --   isLin := sorry, isSmooth, diff_simp, 
  --   hasAdjoint := sorry, 
  --   adj_simp := cross y' x by sorry,
  --   hasAdjDiff := by constructor; infer_instance; simp; infer_instance done,
  --   adjDiff_simp by simp[adjDiff]

  -- @[simp]
  -- theorem cross.of_same (x : ℝ^(3:Nat)) : cross x x = 0 := sorry

  -- @[simp]
  -- theorem cross.smul_out_1 (x y : ℝ^(3:Nat)) (r : ℝ) : cross (r*x) y = r * cross x y := sorry
  -- @[simp]
  -- theorem cross.smul_out_2 (x y : ℝ^(3:Nat)) (r : ℝ) : cross x (r*y) = r * cross x y := sorry
