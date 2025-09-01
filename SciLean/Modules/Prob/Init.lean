import Mathlib.Data.Erased
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

import SciLean.Modules.Prob.SimpAttr

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob


-- instance [RCLike R] [AddCommGroup M] [Module R M] : Module ℝ M := sorry
----------------------------------------------------------------------------------------------------
-- helpful Erased functions and instances ----------------------------------------------------------
----------------------------------------------------------------------------------------------------

noncomputable
scoped instance : Coe (Erased α) α := ⟨fun x => x.out⟩

noncomputable
instance [MeasurableSpace X] : CoeFun (Erased (Measure X)) (fun _ => Set X → ℝ≥0∞) where
  coe μ A := μ.out A

attribute [coe] Erased.out


abbrev erase (a : α) : Erased α := .mk a

@[rand_simp,simp]
theorem erase_out {α} (a : α) : (erase a).out = a := sorry
