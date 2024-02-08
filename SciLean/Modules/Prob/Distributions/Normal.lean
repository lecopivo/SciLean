import Probly.RandFwdDeriv

open MeasureTheory ENNReal BigOperators Finset

namespace Probly


def normal (μ σ : ℝ) : Rand ℝ := {
  μ := sorry
  is_prob := sorry
  rand := sorry
}

def dnormal (μ σ dμ dσ : ℝ) : DRand ℝ := {
  action := fun φ => sorry
}

def fdnormal (μ σ dμ dσ : ℝ) : FDRand ℝ := {
  val := normal μ σ
  dval := dnormal μ σ dμ dσ
}

noncomputable
def normalPdf (μ σ : ℝ) (x : ℝ) : ℝ := 
  1/(σ*(2*Real.pi).sqrt) * Real.exp (- (x-μ)^2 / (2*σ^2))

-- @[rand_simp,simp]
-- theorem normal.pdf_wrt_normal (μ σ : ℝ) :
--     (normal θ).pdf' (normal θ').μ
--     =
--     fun b => if b then θ / θ' else (1-θ) / (1-θ') := by sorry

@[rand_simp,simp]
theorem dnormal.density_wrt_normal (μ σ dμ dσ : ℝ) :
    (dnormal μ σ dμ dσ).density (normal μ σ).μ
    =
    fun x => 
      (dμ * (x-μ) + dσ * (x-μ-σ)*(x-μ+σ)/σ) / (σ^2) := by sorry

-- @[rand_simp,simp]
-- theorem normal.pdf (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
--     (normal x).pdf' .count
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
theorem normal.arg_μσ.randDeriv_rule (μ σ: W → ℝ) (hμ : Differentiable ℝ μ) (hσ : Differentiable ℝ σ) :
    randDeriv (fun w => normal (μ w) (σ w))
    =
    fun w dw =>
      let dμ := fderiv ℝ μ w dw
      let dσ := fderiv ℝ σ w dw
      dnormal (μ w) (σ w) dμ dσ := sorry

@[simp,rand_AD]
theorem normal.arg_μσ.randFwdDeriv_rule (μ σ: W → ℝ) (hμ : Differentiable ℝ μ) (hσ : Differentiable ℝ σ) :
    randFwdDeriv (fun w => normal (μ w) (σ w))
    =
    fun w dw =>
      let μdμ := (fwdDeriv ℝ μ w dw)
      let σdσ := (fwdDeriv ℝ σ w dw)
      ⟨normal μdμ.1 σdσ.1, dnormal μdμ.1 σdσ.1 μdμ.2 σdσ.2⟩ := sorry


@[simp,rand_AD]
theorem normal.arg_x.randFwdDeriv_rule_siple :
    randFwdDeriv (fun μσ : ℝ×ℝ => normal μσ.1 μσ.2)
    =
    fun μσ dμσ =>
      ⟨normal μσ.1 μσ.2, dnormal μσ.1 μσ.2 dμσ.1 dμσ.2⟩ := sorry
