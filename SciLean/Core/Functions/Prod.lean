-- import SciLean.Core.IsSmooth
-- import SciLean.Core.IsLin
-- import SciLean.Core.HasAdjoint

import SciLean.Core.Diff
import SciLean.Core.Adjoint
import SciLean.Core.AdjDiff
import SciLean.Core.Inv

namespace SciLean


-- Prod.fst --
--------------

function_properties Prod.fst {X Y : Type} (xy : X × Y) : X
argument xy [Vec X] [Vec Y]
  isSmooth     := sorry,
  isLin        := sorry,
  diff_simp    := dxy.1 by sorry
argument xy [SemiHilbert X] [SemiHilbert Y]
  hasAdjoint   := sorry,
  adj_simp     := (xy', 0) by sorry,
  hasAdjDiff   := by constructor; infer_instance; simp; infer_instance done,
  adjDiff_simp := (dxy', 0) by simp[adjDiff] done
argument xy [Nonempty X] [Subsingleton Y] [Inhabited Y] 
  isInv        := sorry,
  inv_simp     := (xy', default) by sorry

-- At some point I needed this because of some reduction shenanigans
-- instance [Vec X] [Vec Y] [Vec Z] (f : X → Y×Z) [IsSmooth f] : IsSmooth (λ x => (f x).1) := sorry

-- Prod.snd --
--------------

function_properties Prod.snd {X Y : Type} (xy : X × Y) : Y
argument xy [Vec X] [Vec Y]
  isSmooth     := sorry, 
  isLin        := sorry,
  diff_simp    := dxy.2 by sorry
argument xy [SemiHilbert X] [SemiHilbert Y]
  hasAdjoint   := sorry,
  adj_simp     := (0, xy') by sorry,
  hasAdjDiff   := by constructor; infer_instance; simp; infer_instance done,
  adjDiff_simp := (0, dxy') by simp[adjDiff] done
argument xy [Subsingleton X] [Inhabited X] [Nonempty Y]
  isInv        := sorry,
  inv_simp     := (default, xy') by sorry

-- At some point I needed this because of some reduction shenanigans
-- instance [Vec X] [Vec Y] [Vec Z] (f : X → Y×Z) [IsSmooth f] : IsSmooth (λ x => (f x).2) := sorry


