-- import SciLean.Core.IsSmooth
-- import SciLean.Core.IsLin
-- import SciLean.Core.HasAdjoint

import SciLean.Core.Diff
import SciLean.Core.Adjoint
import SciLean.Core.AdjDiff
import SciLean.Core.Inv


namespace SciLean


-- Sum --
---------

function_properties sum {ι X : Type} [Enumtype ι] (f : ι → X) : X
argument f [Vec X]
  isSmooth    := sorry,
  isLin       := sorry,
  diff_simp   := sum df by sorry
argument f [SemiHilbert X]
  hasAdjoint  := sorry,
  adj_simp    := λ _ => f' by sorry,
  hasAdjDiff  := by constructor; infer_instance; simp; infer_instance done,
  adjDiff_simp := λ _ => df' by simp[adjDiff] done
