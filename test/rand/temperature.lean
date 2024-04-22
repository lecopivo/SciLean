import SciLean

import SciLean.Core.Rand.ExpectedValue

import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.ParametricDistribFwdDeriv
import SciLean.Core.Distribution.ParametricDistribRevDeriv
import SciLean.Core.Distribution.SurfaceDirac

import SciLean.Core.Functions.Gaussian

#exit

namespace SciLean

open MeasureTheory Set BigOperators

variable {R} [RealScalar R] [MeasureSpace R] [PlainDataType R]

set_default_scalar R


attribute [ftrans_simp]
  FiniteDimensional.finrank_self FiniteDimensional.finrank_prod
  not_le ite_mul mul_ite mul_neg mul_one setOf_eq_eq_singleton
  Finset.card_singleton PUnit.default_eq_unit Finset.univ_unique Finset.sum_const
  preimage_id'
  mem_setOf_eq mem_ite_empty_right mem_inter_iff mem_ite_empty_right mem_univ mem_Ioo
  and_true

@[ftrans_simp]
theorem _root_.PUnit.finrank [Semiring R] : FiniteDimensional.finrank R Unit = 0 := sorry_proof


----------------------------------------------------------------------------------------------------
-- Variational Inference - Test 1 ------------------------------------------------------------------
----------------------------------------------------------------------------------------------------



def model (T₀ : R) (S : Rand Bool) (T : Bool → R → Rand R) : Rand (Bool^[n]×R^[n]) := do
  let mut Tᵢ := T₀
  for i in [0:n] do
    let s ~ S
    if s then
      Tᵢ ~ T s Tᵢ
    else
      Tᵢ ~ T s Tᵢ
