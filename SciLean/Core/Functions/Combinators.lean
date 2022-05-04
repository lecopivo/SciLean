-- import SciLean.Core.IsSmooth
-- import SciLean.Core.IsLin
-- import SciLean.Core.HasAdjoint

import SciLean.Core.Diff
import SciLean.Core.Adjoint
import SciLean.Core.AdjDiff

namespace SciLean


-- Composition --
-----------------

function_properties Function.comp {X Y Z : Type} (f : Y → Z) (g : X → Y) (x : X) : Z
argument f [Vec Z]
  isLin      := by simp[Function.comp] infer_instance,
  isSmooth   := by simp[Function.comp] infer_instance,
  diff_simp  := df (g x) by simp[Function.comp] done
argument g [Vec Y] [Vec Z]
  isLin     [IsLin f]    := by simp[Function.comp] infer_instance,
  isSmooth  [IsSmooth f] := by simp[Function.comp] infer_instance,
  diff_simp [IsSmooth f] := δ f (g x) (dg x) by simp[Function.comp] done
argument x
  [Vec X] [Vec Y] [Vec Z]
  [IsLin f] [IsLin g]
  isLin     := by simp[Function.comp] infer_instance
argument x
  [Vec X] [Vec Y] [Vec Z]
  [IsSmooth f] [IsSmooth g] 
  isSmooth  := by simp[Function.comp] infer_instance,
  diff_simp := δ f (g x) (δ g x dx) by simp[Function.comp] done
argument x
  [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
  [HasAdjoint f] [HasAdjoint g]
  hasAdjoint := by simp[Function.comp] infer_instance,
  adj_simp   := (g† ∘ f†) x' by simp[Function.comp] done
argument x
  [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
  [HasAdjDiff f] [HasAdjDiff g]
  hasAdjDiff   := by simp[Function.comp]; infer_instance done,
  adjDiff_simp := ((δ† g x) ∘ (δ† f (g x))) dx'  by simp[Function.comp] done
  
