import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Probability.Distributions.Gaussian


import SciLean.Modules.Prob.DistribDeriv.DistribDeriv
import SciLean.Modules.Prob.DistribDeriv.DistribFwdDeriv
import SciLean.Modules.Prob.DerivUnderIntegralSign

namespace SciLean.Prob

variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]


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
  ⟨fun φ =>  ∫ x, dgaussian μ σ dμ dσ x • φ x⟩

noncomputable
def fdnormal (a b da db : ℝ) : FDistribution ℝ := {
  val := normal a b
  dval := dnormal a b da db
}


-- @[fprop]
theorem normal.differentiableAt (μ σ : X → ℝ) (φ : ℝ → W) (x : X) (hσφ : σ x ≠ 0 ∨ DifferentiableAt ℝ φ (μ x))
    (hμ : DifferentiableAt ℝ μ x) (hσ : DifferentiableAt ℝ σ x)
    /- assume that φ is dominated by some polynomial and measurable -/ :
    DifferentiableAt ℝ (fun x' => ⟪normal (μ x') (σ x'), φ⟫) x := by simp[normal]; sorry



-- @[fprop]
theorem normal.bind._arg_xf.differentiableAt (μ σ : X → ℝ) (f : X → ℝ → Distribution Z) (φ : Z → W) (x : X) (hσ₀ : σ x ≠ 0)
    (hμ : DifferentiableAt ℝ μ x) (hσ : DifferentiableAt ℝ σ x)
    -- TODO: weaken 'hf' such that we still need `hμ` and `hσ`
    (hf : DifferentiableUnderIntegralAt (fun x y => ⟪f x y, φ⟫) (fun x => (gaussianReal (μ x) ((σ x)^2).toNNReal)) x) :
    DifferentiableAt ℝ (fun x' => ⟪normal (μ x') (σ x') >>= (f x'), φ⟫) x := by

  simp[normal,bind]
  sorry -- apply hf.diff



@[simp]
theorem normal.distribDeriv_comp
    (μ σ : X → ℝ) (x dx : X) (φ : ℝ → W) (hab : σ x ≠ 0)
    (hμ : DifferentiableAt ℝ μ x) (hμ : DifferentiableAt ℝ σ x)
    /- assume that φ is dominated by some polynomial and measurable -/ :
    ⟪distribDeriv (fun x : X => normal (μ x) (σ x)) x dx, φ⟫
    =
    let μ' := μ x
    let dμ := fderiv ℝ μ x dx
    let σ' := σ x
    let dσ := fderiv ℝ σ x dx
    ⟪dnormal μ' σ' dμ dσ, φ⟫ := by

  simp[normal,dnormal,bind,distribDeriv]
  sorry


@[simp]
theorem normal.bind.arg_xf.distribDeriv_rule
    (μ σ : X → ℝ) (f : X → ℝ → Distribution Z) (x dx) (φ : Z → W) (hσ₀ : σ x ≠ 0)
    (hμ : DifferentiableAt ℝ μ x) (hμ : DifferentiableAt ℝ σ x)
    -- TODO: weaken 'hf' such that we still need `hμ` and `hσ`
    (hf : DifferentiableUnderIntegralAt (fun x y => ⟪f x y, φ⟫) (fun x => (gaussianReal (μ x) ((σ x)^2).toNNReal)) x) :
    ⟪distribDeriv (fun x' => bind (normal (μ x') (σ x')) (f x')) x dx, φ⟫
    =
    let μ' := μ x
    let dμ := fderiv ℝ μ x dx
    let σ' := σ x
    let dσ := fderiv ℝ σ x dx
    ⟪dnormal μ' σ' dμ dσ >>= (f x ·), φ⟫
    +
    ⟪normal μ' σ', fun y => ⟪distribDeriv (f · y) x dx, φ⟫⟫ := by

  simp [distribDeriv, normal, dnormal, bind]
  sorry


@[simp]
theorem normal.distribFwdDeriv_comp
    (μ σ : X → ℝ) (x dx : X) (φ : ℝ → W×W) (hσ₀ : σ x ≠ 0)
    (hμ : DifferentiableAt ℝ μ x) (hμ : DifferentiableAt ℝ σ x)
    /- integrability condition on φ -/:
    ⟪distribFwdDeriv (fun x : X => normal (μ x) (σ x)) x dx, φ⟫
    =
    let μdμ := fwdFDeriv ℝ μ x dx
    let σdσ := fwdFDeriv ℝ σ x dx
    ⟪fdnormal μdμ.1 σdσ.1 μdμ.2 σdσ.2, φ⟫ := by

  unfold distribFwdDeriv
  simp (disch := assumption) only [fdaction_mk_apply, distribDeriv_comp]
  rfl


@[simp]
theorem normal.bind.arg_xf.distribFwdDeriv_rule
    (μ σ : X → ℝ) (f : X → ℝ → Distribution Z) (x dx) (φ : Z → W×W) (hσ₀ : σ x ≠ 0)
    (hμ : DifferentiableAt ℝ μ x) (hμ : DifferentiableAt ℝ σ x)
    -- TODO: weaken 'hf' such that we still need `ha` and `hb`
    (hf : DifferentiableUnderIntegralAt (fun x y => ⟪f x y, φ⟫) (fun x => (gaussianReal (μ x) ((σ x)^2).toNNReal)) x) :
    ⟪distribFwdDeriv (fun x' => bind (normal (μ x') (σ x')) (f x')) x dx, φ⟫
    =
    let μdμ := fwdFDeriv ℝ μ x dx
    let σdσ := fwdFDeriv ℝ σ x dx
    ⟪fdnormal μdμ.1 σdσ.1 μdμ.2 σdσ.2, fun y => ⟪distribFwdDeriv (f · y) x dx, φ⟫⟫ := by

  unfold distribFwdDeriv fdnormal fwdFDeriv
  simp (disch := assumption) only [fdaction_mk_apply, distribDeriv_rule, bind, Pi.add_apply]
  sorry -- linearity of normal in `φ`
