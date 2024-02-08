import SciLean.Modules.Prob.RandFwdDeriv
import SciLean.Core.FloatAsReal

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob

open Rand

variable {R} [RealScalar R]

instance {R} [RealScalar R] : MeasureSpace R := sorry

def uniform (a b : R) : Rand R := {
  μ := erase (1 • volume.restrict (Set.uIcc a b) )
  is_prob := sorry
  rand := sorry
}

-- TODO: this is incorrect if `a>b`
def duniform (a b da db : R) : DRand R := {
  action := fun φ => (Scalar.toReal R db) * φ b - (Scalar.toReal R da) * φ a
}

def fduniform (a b da db : R) : FDRand R := {
  val := uniform a b
  dval := duniform a b da db
}


-- @[rand_simp,simp]
-- theorem uniform.pdf_wrt_uniform (θ θ' : ℝ) :
--     (uniform θ).pdf' (uniform θ').a
--     =
--     fun b => if b then θ / θ' else (1-θ) / (1-θ') := by sorry

-- @[rand_simp,simp]
-- theorem duniform.density_wrt_uniform (θ : ℝ) :
--     duniform.density (uniform θ).a
--     =
--     fun b => if b then 1 / θ else 1 / (θ-1) := by sorry

-- @[rand_simp,simp]
-- theorem uniform.pdf (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
--     (uniform x).pdf' .count
--     =
--     fun b => if b then x else (1-x) := by sorry


variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]


@[simp,rand_AD]
theorem uniform.arg_ab.randDeriv_rule (a b : W → R) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    randDeriv (fun w => uniform (a w) (b w))
    =
    fun w dw =>
      let da := fderiv ℝ a w dw
      let db := fderiv ℝ b w dw
      (db • DRand.dirac (b w) - da • DRand.dirac (a w)) := sorry


@[simp,rand_AD]
theorem uniform.arg_ab.randFwdDeriv_rule (a b : W → R) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    randFwdDeriv (fun w => uniform (a w) (b w))
    =
    fun w dw =>
      let ada := fwdFDeriv ℝ a w dw
      let bdb := fwdFDeriv ℝ b w dw
      ⟨uniform ada.1 bdb.1, bdb.2 • DRand.dirac bdb.1 - ada.2 • DRand.dirac ada.1⟩ := by

  funext w dw
  simp (disch:=first | assumption | sorry) [randFwdDeriv,fwdFDeriv,fduniform]


@[simp,rand_AD]
theorem uniform.arg_x.randFwdDeriv_rule_siple :
    randFwdDeriv (fun ab : R×R => uniform ab.1 ab.2)
    =
    fun ab dab =>
      ⟨uniform ab.1 ab.2, duniform ab.1 ab.2 dab.1 dab.2⟩ := sorry
