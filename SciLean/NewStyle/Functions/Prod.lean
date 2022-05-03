import SciLean.NewStyle.IsSmooth
import SciLean.NewStyle.IsLin
import SciLean.NewStyle.HasAdjoint
import SciLean.NewStyle.Diff
import SciLean.NewStyle.Adjoint

namespace SciLean


-- Prod.fst --
--------------

function_properties Prod.fst {X Y : Type} (xy : X × Y) : X
argument xy [Vec X] [Vec Y]
  isSmooth    := sorry,
  isLin       := sorry,
  diff_simp   := dxy.1 by sorry
argument xy [SemiHilbert X] [SemiHilbert Y]
  hasAdjoint  := sorry,
  adj_simp    := (xy', 0) by sorry

--    hasAdjDiff,
--    adj_diff := ??? by sorry


-- instance [Vec X] [Vec Y] [Vec Z] (f : X → Y×Z) [IsSmooth f] : IsSmooth (λ x => (f x).1) := sorry

-- Prod.snd --
--------------

function_properties Prod.snd {X Y : Type} (xy : X × Y) : Y
argument xy [Vec X] [Vec Y]
  isSmooth    := sorry, 
  isLin       := sorry,
  diff_simp   := dxy.2 by sorry
argument xy [SemiHilbert X] [SemiHilbert Y]
  hasAdjoint  := sorry,
  adj_simp    := (0, xy') by sorry
  -- adj_diff := ??? by sorry

-- instance [Vec X] [Vec Y] [Vec Z] (f : X → Y×Z) [IsSmooth f] : IsSmooth (λ x => (f x).2) := sorry


