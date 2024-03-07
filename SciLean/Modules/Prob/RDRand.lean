import Mathlib.MeasureTheory.Measure.VectorMeasure
import Mathlib.Logic.Function.Basic

import Probly.DRand

open MeasureTheory ENNReal BigOperators Finset

namespace Probly


variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]

-- can we define this?
-- does it have any reasonable meaning?
def drandAdjoint (L : X → DRand Y) : Y → DRand X := sorry

noncomputable
def randRevDeriv (f : X → Rand Y) (x : X) : Rand (Y × (Y → DRand X)) :=
  let y ~ f x
  Rand.pure (y, drandAdjoint (randDeriv f x))
