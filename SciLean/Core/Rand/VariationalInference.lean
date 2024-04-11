import SciLean.Core.Rand.Rand
import SciLean.Core.Rand.Condition

import SciLean.Core.Distribution.ParametricDistribDeriv

import Mathlib.MeasureTheory.Constructions.Prod.Basic

namespace SciLean


open MeasureTheory
variable
  {R} [RealScalar R]
  {X Z} [MeasurableSpace X] [MeasurableSpace Z]

/-- Kullback–Leibler divergence of `Dₖₗ(P‖Q)` -/
noncomputable
def KLDiv (P Q : Rand X) : R := P.𝔼 (fun x => Scalar.log (P.pdf R Q.ℙ x))

/-- Evidence Lower Bound -/
noncomputable
def ELBO {X Z} [MeasureSpace Z] [MeasureSpace X]
    (P : Rand (Z×X)) (Q : Rand Z) (x : X) : R :=
  - Q.𝔼 (fun z => Scalar.log (Q.pdf R volume z) - Scalar.log (P.pdf R volume (z,x)))


/-- Express `Kullback–Leibler divergence` as log evidence + ELBO -/
theorem kldiv_elbo
    {X Z} [MeasureSpace Z] [MeasureSpace X]
    (P : Rand (Z×X)) (Q : Rand Z) (x : X) :
    KLDiv Q (P.conditionSnd x)
    =
    (Scalar.log (P.snd.pdf R volume x)) - ELBO P Q x := sorry_proof



----------------------------------------------------------------------------------------------------
-- KLDiv properties --------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

variable
  {W} [Vec R W]
  [Vec R X]

@[fun_trans]
theorem KLDiv.arg_P.cderiv_rule (P : W → Rand X) (Q : Rand X) :
    cderiv R (fun w => KLDiv (R:=R) (P w) Q)
    =
    fun w dw =>
      let dP := parDistribDeriv (fun w => (P w).ℙ.toDistribution (R:=R)) w dw
      dP.extAction' (fun x => Scalar.log ((P w).pdf R Q.ℙ x) - 1) := sorry_proof
