import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Prod

import SciLean.Meta.SimpAttr
import SciLean.Util.SorryProof

namespace SciLean

open MeasureTheory

/-! WARNING: This file contains rewrite rules for Radon-Nikodym derivative which usually hold
  almost everywhere but here we postulate them as equalities everywhere. This is because we are
  lacking proper automation to apply equalities that hold only almost everywhere.
 -/


open Classical in
@[ simp_core]
theorem rnDeriv_restrict {X} [MeasurableSpace X] (μ ν : Measure X) (A : Set X) :
  (μ.restrict A).rnDeriv ν
  =
  fun x => (μ.rnDeriv ν x) * (if x ∈ A then 1 else 0) := sorry_proof


@[ simp_core]
theorem rnDeriv_prod_volume {X Y} [MeasureSpace X] [MeasureSpace Y] (μ : Measure X) (ν : Measure Y) :
  (μ.prod ν).rnDeriv volume
  =
  fun (x,y) => (μ.rnDeriv volume x) * (ν.rnDeriv volume y) := sorry_proof


-- This is pointwise version of: MeasureTheorey.Measure.rnDeriv_self
@[ simp_core]
theorem rnDeriv_self {X} [MeasurableSpace X] (μ : Measure X) :
  μ.rnDeriv μ
  =
  fun _ => 1 := sorry_proof
