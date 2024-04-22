import SciLean

import SciLean.Core.Rand.ExpectedValue

import SciLean.Core.Distribution.Basic
import SciLean.Core.Distribution.ParametricDistribDeriv
import SciLean.Core.Distribution.ParametricDistribFwdDeriv
import SciLean.Core.Distribution.ParametricDistribRevDeriv
import SciLean.Core.Distribution.SurfaceDirac

import SciLean.Core.Functions.Gaussian

namespace SciLean

open Rand MeasureTheory Set BigOperators

variable {R} [RealScalar R] [MeasureSpace R]

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

def model1 (T : Rand R) : Rand (R×R) :=
  let v ~ normal 0 1
  if 0 ≤ v then
    let obs ~ normal (1:R) 1
  else
    let obs ~ normal (-2:R) 1
