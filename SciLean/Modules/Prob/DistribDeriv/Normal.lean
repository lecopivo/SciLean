import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Probability.Distributions.Gaussian


import SciLean.Modules.Prob.DistribDeriv.DistribDeriv
import SciLean.Modules.Prob.DistribDeriv.DistribFwdDeriv
import SciLean.Modules.Prob.DerivUnderIntegralSign

namespace SciLean.Prob

variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [MeasurableSpace Z]


open MeasureTheory ProbabilityTheory

noncomputable
def gaussian (μ σ : ℝ) (x : ℝ) : ℝ :=
  let x' := (x - μ)/σ
  (σ*Real.sqrt (2*Real.pi))⁻¹ * Real.exp (- (x'^2)/2)

noncomputable
def dgaussian (μ σ dμ dσ : ℝ) (x : ℝ) : ℝ :=
  let x' := (x - μ)/σ
  σ⁻¹ * (dμ * x' - dσ * (1 - x'^2)) * gaussian μ σ x

noncomputable
def normal (μ σ : ℝ) : Distribution ℝ :=
  (gaussianReal μ (σ^2).toNNReal).toDistribution

noncomputable
def dnormal (μ σ dμ dσ : ℝ) : Distribution ℝ :=
  fun φ =>  ∫ x, φ x * dgaussian μ σ dμ dσ x

noncomputable
def fdnormal (a b da db : ℝ) : FDistribution ℝ := {
  val := normal a b
  dval := dnormal a b da db
}


-- @[fprop]
theorem normal.differentiableAt (μ σ : X → ℝ) (φ : ℝ → ℝ) (x : X) (hσφ : σ x ≠ 0 ∨ DifferentiableAt ℝ φ (μ x))
    (hμ : DifferentiableAt ℝ μ x) (hσ : DifferentiableAt ℝ σ x)
    /- assume that φ is dominated by some polynomial and measurable -/ :
    DifferentiableAt ℝ (fun x' => normal (μ x') (σ x') φ) x := by simp[normal]; sorry



-- @[fprop]
theorem normal.bind._arg_xf.differentiableAt (μ σ : X → ℝ) (f : X → ℝ → Distribution Z) (φ : Z → ℝ) (x : X) (hσ₀ : σ x ≠ 0)
    (hμ : DifferentiableAt ℝ μ x) (hσ : DifferentiableAt ℝ σ x)
    -- TODO: weaken 'hf' such that we still need `hμ` and `hσ`
    (hf : DifferentiableUnderIntegralAt (fun x y => f x y φ) sorry x) :
    DifferentiableAt ℝ (fun x' => (normal (μ x') (σ x')).bind (f x') φ) x := by

  simp[normal,Distribution.bind]
  sorry -- apply hf.diff



@[simp]
theorem normal.distribDeriv_comp
    (μ σ : X → ℝ) (x dx : X) (φ : ℝ → ℝ) (hab : σ x ≠ 0)
    (hμ : DifferentiableAt ℝ μ x) (hμ : DifferentiableAt ℝ σ x)
    /- assume that φ is dominated by some polynomial and measurable -/ :
    distribDeriv (fun x : X => normal (μ x) (σ x)) x dx φ
    =
    let μ' := μ x
    let dμ := fderiv ℝ μ x dx
    let σ' := σ x
    let dσ := fderiv ℝ σ x dx
    dnormal μ' σ' dμ dσ φ := by

  simp[normal,dnormal,Distribution.bind,distribDeriv]
  sorry


@[simp]
theorem normal.bind.arg_xf.distribDeriv_rule
    (μ σ : X → ℝ) (f : X → ℝ → Distribution Z) (x dx) (φ : Z → ℝ) (hσ₀ : σ x ≠ 0)
    (hμ : DifferentiableAt ℝ μ x) (hμ : DifferentiableAt ℝ σ x)
    -- TODO: weaken 'hf' such that we still need `hμ` and `hσ`
    (hf : DifferentiableUnderIntegralAt (fun x y => f x y φ) sorry x) :
    distribDeriv (fun x' => (normal (μ x') (σ x')).bind (f x')) x dx φ
    =
    let μ' := μ x
    let dμ := fderiv ℝ μ x dx
    let σ' := σ x
    let dσ := fderiv ℝ σ x dx
    (dnormal μ' σ' dμ dσ).bind (f x ·) φ
    +
    (normal μ' σ').bind (fun y => distribDeriv (f · y) x dx) φ := by

  simp [distribDeriv, normal, dnormal, Distribution.bind]
  sorry


@[simp]
theorem normal.distribFwdDeriv_comp
    (μ σ : X → ℝ) (x dx : X) (φ : ℝ → ℝ×ℝ) (hσ₀ : σ x ≠ 0)
    (hμ : DifferentiableAt ℝ μ x) (hμ : DifferentiableAt ℝ σ x)
    /- integrability condition on φ -/:
    distribFwdDeriv (fun x : X => normal (μ x) (σ x)) x dx φ
    =
    let μdμ := fwdFDeriv ℝ μ x dx
    let σdσ := fwdFDeriv ℝ σ x dx
    fdnormal μdμ.1 σdσ.1 μdμ.2 σdσ.2 φ := by

  unfold distribFwdDeriv
  simp (disch := assumption) only [FDistribution_apply, distribDeriv_comp]
  rfl


@[simp]
theorem normal.bind.arg_xf.distribFwdDeriv_rule
    (μ σ : X → ℝ) (f : X → ℝ → Distribution Z) (x dx) (φ : Z → ℝ×ℝ) (hσ₀ : σ x ≠ 0)
    (hμ : DifferentiableAt ℝ μ x) (hμ : DifferentiableAt ℝ σ x)
    -- TODO: weaken 'hf' such that we still need `ha` and `hb`
    (hf : DifferentiableUnderIntegralAt (fun x y => f x y (fun x => (φ x).1)) sorry x) :
    distribFwdDeriv (fun x' => (normal (μ x') (σ x')).bind (f x')) x dx φ
    =
    let μdμ := fwdFDeriv ℝ μ x dx
    let σdσ := fwdFDeriv ℝ σ x dx
    (fdnormal μdμ.1 σdσ.1 μdμ.2 σdσ.2) (fun y => distribFwdDeriv (f · y) x dx φ) := by

  unfold distribFwdDeriv fdnormal fwdFDeriv
  simp (disch := assumption) only [FDistribution_apply, distribDeriv_rule, FDistribution.bind, Pi.add_apply,Distribution.bind]
  simp
  sorry -- linearity of normal in `φ`
