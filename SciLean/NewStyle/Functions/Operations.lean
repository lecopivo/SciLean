import SciLean.NewStyle.IsSmooth
import SciLean.NewStyle.IsLin
import SciLean.NewStyle.HasAdjoint
import SciLean.NewStyle.Diff
import SciLean.NewStyle.Adjoint

namespace SciLean


-- Neg.neg --
-------------

function_properties Neg.neg {X : Type} (x : X) : X
argument x [Vec X]
  isLin      := sorry,
  isSmooth   := sorry, 
  diff_simp  := - dx by sorry
argument x [SemiHilbert X]
  hasAdjoint := sorry,
  adj_simp   := - x' by sorry


-- HMul.hMul --
---------------

function_properties HMul.hMul {X : Type} (x : ℝ) (y : X) : X
argument x [Vec X] 
  isLin      := sorry,
  isSmooth   := sorry, 
  diff_simp  := dx * y by sorry
argument x [Hilbert X]
  hasAdjoint := sorry,
  adj_simp   := ⟪x', y⟫ by sorry
argument y [Vec X]
  isLin      := sorry,
  isSmooth   := sorry,
  diff_simp  := x * dy by sorry
argument y [SemiHilbert X]
  hasAdjoint := sorry,
  adj_simp   := x * y' by sorry


-- HAdd.hAdd --
---------------

function_properties HAdd.hAdd {X : Type} [Vec X] (x y : X) : X
argument x
  isSmooth  := sorry, 
  diff_simp := dx by sorry
  -- isInv       := sorry
  -- inv         := x' - y
argument y
  isSmooth  := sorry,
  diff_simp := dy by sorry
  -- isInv       := sorry
  -- inv         := y' - x
-- argument x y
--   isLin

-- function_properties HAdd.hAdd {X : Type} [SemiHilbert X] (x y : X) : X
--   hasAdjoint


-- HSub.hSub --
---------------

function_properties HSub.hSub {X : Type} [Vec X] (x y : X) : X
argument x
  isSmooth  := sorry, 
  diff_simp := dx by sorry
  -- isInv       := sorry
  -- inv         := x' + y
  
argument y
  isSmooth  := sorry,
  diff_simp := - dy by sorry
  -- isInv       := sorry
  -- inv         := y' + x
-- argument x y
--   isLin

-- function_properties HSub.hSub {X : Type} [SemiHilbert X] (x y : X) : X
-- argument x y
--   hasAdjoint

