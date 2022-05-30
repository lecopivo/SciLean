import SciLean.Core.Mor
import SciLean.Core.Fun

namespace SciLean


-- Prod.mk --
-------------

function_properties Prod.mk {X Y} (x : X) (y : Y) : X×Y
argument x [Inhabited X]
  isInv := sorry,
  inv_simp := x'.1 by sorry
argument x [Vec X] [Vec Y]
  isSmooth := sorry,
  diff_simp := (dx,0) by sorry
argument x [SemiHilbert X] [SemiHilbert Y]
  hasAdjDiff := by constructor; infer_instance; simp; admit,
  adjDiff_simp := dx'.1 by sorry
argument y [Inhabited Y]
  isInv := sorry,
  inv_simp := y'.2 by sorry
argument y [Vec X] [Vec Y]
  isSmooth := sorry,
  diff_simp := (0,dy) by sorry
argument y [SemiHilbert X] [SemiHilbert Y]
  hasAdjDiff := by constructor; infer_instance; simp; admit,
  adjDiff_simp := dy'.2 by sorry


-- Prod.fst --
--------------

function_properties Prod.fst {X Y} (xy : X × Y) : X
argument xy [Vec X] [Vec Y]
  isLin        := sorry,
  isSmooth, diff_simp, fwdDiff_simp
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
@[simp, simp_diff] 
theorem Prod.fst.arg_xy.diff_simp' {X Y} [Vec X] [Vec Y] : (δ λ x : X×Y => x.1) = λ x dx => dx.1 := by simp

-- Prod.snd --
--------------

function_properties Prod.snd {X Y} (xy : X × Y) : Y
argument xy [Vec X] [Vec Y]
  isLin        := sorry,
  isSmooth, diff_simp, fwdDiff_simp
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



