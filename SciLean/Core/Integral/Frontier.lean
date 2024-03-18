import SciLean.Core.Notation
import SciLean.Core.Integral.CIntegral
import SciLean.Core.Integral.ParametricInverse

open MeasureTheory

namespace SciLean


variable
  {R} [RealScalar R]
  {W} [SemiHilbert R W]
  {X} [SemiHilbert R X]
  {Y} [SemiHilbert R Y] [Module ℝ Y]
  {Z} [SemiHilbert R Z] [Module ℝ Z]


@[simp,ftrans_simp]
theorem frontier_inter {X} [TopologicalSpace X] (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) :
    frontier (A ∩ B) = (frontier A ∩ B) ∪ (A ∩ frontier B) := by
  sorry


@[simp,ftrans_simp]
theorem frontier_levelSet {X} [TopologicalSpace X] (φ ψ : X → R) :
    frontier {x | φ x ≤ ψ x} = {x | φ x = ψ x}  := by
  sorry
