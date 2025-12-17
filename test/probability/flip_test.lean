import SciLean.Probability.Distributions.Flip
import SciLean.Probability.Tactic
import SciLean.Analysis.Scalar.FloatAsReal

open MeasureTheory ENNReal BigOperators Finset

open SciLean Rand

variable {R} [RealScalar R] [MeasureSpace R] [BorelSpace R] [ToString R]


def test (θ : R) : Rand R := do
  let b ← flip θ
  if b then
    pure 0
  else
    pure (-θ/2)

def test_mean (θ : R) := (test θ).mean
  rewrite_by
    unfold test
    simp[rand_push_E,flip.E_val]


-- #eval print_mean_variance (test 0.5) 1000 s!" of {test_mean 0.5}"
-- #eval print_mean_variance (test 0.7) 1000 s!" of {test_mean 0.7}"
