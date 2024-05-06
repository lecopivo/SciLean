import SciLean.Core.Notation
import SciLean.Core.Integral.CIntegral
import SciLean.Core.Integral.ParametricInverse
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff

open MeasureTheory

namespace SciLean

variable
  {R} [RealScalar R]
  {W} [SemiHilbert R W]
  {X} [SemiHilbert R X]
  {Y} [SemiHilbert R Y] [Module ℝ Y]
  {Z} [SemiHilbert R Z] [Module ℝ Z]

set_default_scalar R

-- /-- Area measure on if `S` is co-dimension one surface. -/
-- opaque area' {X} [MeasureSpace X] {S : Set X} : Measure S := sorry

-- /-- Area measure of surfaces, can this be well defined? -/
-- opaque area {X} [MeasureSpace X] : Measure X := sorry

-- TODO: figure out how to use Hausdoff measure here
noncomputable
opaque surfaceMeasure [MeasureSpace X] (d : ℕ) : Measure X := sorry
  -- have m : EMetricSpace X := sorry
  -- have h : (Vec.toUniformSpace R) = PseudoEMetricSpace.toUniformSpace := sorry
  -- have b : @BorelSpace X _ (borel X) := sorry
  -- @Measure.hausdorffMeasure _ _ (borel _) (h ▸ b) d

open FiniteDimensional in
@[simp, ftrans_simp]
theorem surfaceMeasure_volume [MeasureSpace X] :
   surfaceMeasure (X:=X) (finrank R X) = volume := sorry_proof


@[ftrans_simp]
theorem surfaceMeasure_zero_singleton [MeasureSpace X] (x : X) :
  surfaceMeasure 0 {x} = 1 := sorry_proof
