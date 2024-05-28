import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Dirac

import SciLean.Tactic.FTrans.Simp

open MeasureTheory

@[simp, ftrans_simp]
theorem volume_unit_univ : volume (univ : Set Unit) = 1 := sorry_proof
