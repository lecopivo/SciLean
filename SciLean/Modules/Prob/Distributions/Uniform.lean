import Probly.RandFwdDeriv

open MeasureTheory ENNReal BigOperators Finset

namespace Probly

#check Measure.smul_apply

variable (a b : ℝ)
#check (ENNReal.ofReal (1/|a-b|))

def uniform (a b : ℝ) : Rand ℝ := {
  μ := erase (1 • volume.restrict (Set.uIcc a b) )
  is_prob := sorry
  rand := sorry
}

-- TODO: this is incorrect if `a>b`
def duniform (a b da db : ℝ) : DRand ℝ := {
  action := fun φ => db * φ b - da * φ a
}

def fduniform (a b da db : ℝ) : FDRand ℝ := {
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
theorem uniform.arg_ab.randDeriv_rule (a b : W → ℝ) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    randDeriv (fun w => uniform (a w) (b w))
    =
    fun w dw =>
      let da := fderiv ℝ a w dw
      let db := fderiv ℝ b w dw
      duniform (a w) (b w) da db := sorry


@[simp,rand_AD]
theorem uniform.arg_ab.randFwdDeriv_rule (a b: W → ℝ) (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    randFwdDeriv (fun w => uniform (a w) (b w))
    =
    fun w dw =>
      let ada := fwdDeriv ℝ a w dw
      let bdb := fwdDeriv ℝ b w dw
      fduniform ada.1 bdb.1 ada.2 bdb.2 := by
 
  funext w dw
  simp (disch:=sorry) [randFwdDeriv,fwdDeriv,fduniform]


@[simp,rand_AD]
theorem uniform.arg_x.randFwdDeriv_rule_siple :
    randFwdDeriv (fun ab : ℝ×ℝ => uniform ab.1 ab.2)
    =
    fun ab dab =>
      fduniform ab.1 ab.2 dab.1 dab.2 := sorry
