import SciLean.Modules.Prob.RandFwdDeriv
import SciLean.Core.FloatAsReal

open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob

variable {R} [RealScalar R]

def flip (x : R) : Rand Bool := {
  μ :=
    let t := (ENNReal.ofReal (Scalar.toReal R x))     -- todo: clamp to [0,1]
    let f := (ENNReal.ofReal (Scalar.toReal R (1-x))) -- todo: clamp to [0,1]
    erase (t • Measure.dirac true + f • Measure.dirac false)
  is_prob := sorry
  rand :=
    fun g => do
    let g : StdGen := g.down
    let N := 1000000000000000
    let (n,g) := _root_.randNat g 0 N
    let y := (n : R) / (N : R)
    let b := if y ≤ x then true else false
    pure (b, ← ULiftable.up g)
}

def dflip : DRand Bool := {
  action := fun φ => φ true - φ false
}


@[rand_simp,simp]
theorem flip.pdf_wrt_flip (θ θ' : R) :
    (flip θ).pdf R (flip θ').μ
    =
    fun b => if b then θ / θ' else (1-θ) / (1-θ') := by sorry

@[rand_simp,simp]
theorem dflip.density_wrt_flip (θ : R) :
    dflip.density R (flip θ).μ
    =
    fun b => if b then 1 / θ else 1 / (θ-1) := by sorry


@[rand_simp,simp]
theorem flip.pdf (x : R) (hx : x ∈ Set.Icc 0 1) :
    (flip x).pdf R .count
    =
    fun b => if b then x else (1-x) := by sorry


variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace R W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace R X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace R Z] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]

@[rand_simp,simp]
theorem flip_integral (θ : R) (f : Bool → X) :
    ∫ x, f x ∂(flip θ).μ = θ • f true + (1-θ) • f false := by

  simp [flip,rand_simp]; sorry -- some odd smul with R and ℝ casting

theorem flip_expectedValue (θ : ℝ) (f : Bool → X) :
    (flip θ).E f = θ • f true + (1-θ) • f false := by

  simp[Rand.E,rand_simp]

theorem dflip_expectedValueChange (f : Bool → X) :
    dflip.dE f = f true - f false := by

  simp [DRand.dE,dflip]
  apply testFunctionExtension_ext
  intro φ y; simp [sub_smul]


@[simp,rand_AD]
theorem flip.arg_x.randDeriv_rule (x : W → R) (hf : Differentiable ℝ x) :
    randDeriv (fun w => flip (x w))
    =
    fun w dw =>
      let dx' := (fderiv ℝ x w dw)
      dx' • dflip := by

  simp (disch:=sorry) [rand_simp]
  funext w dw
  simp [randDeriv]
  apply DRand.ext; intro φ; simp[dflip,rand_simp]
  sorry -- just differentiation and ring


@[simp,rand_AD]
theorem flip.arg_x.randFwdDeriv_rule (x : W → R) (hf : Differentiable ℝ x) :
    randFwdDeriv (fun w => flip (x w))
    =
    fun w dw =>
      let x'  := (x w)
      let dx' := (fderiv ℝ x w dw)
      ⟨flip x', dx' • dflip⟩ := by

  unfold randFwdDeriv; simp (disch:= first | apply hf | sorry) [rand_simp, fwdFDeriv]
  rw[flip.arg_x.randDeriv_rule _ differentiable_id']
  simp


@[simp,rand_AD]
theorem flip.arg_x.randFwdDeriv_rule_siple :
    randFwdDeriv (fun x : R => flip x)
    =
    fun x dx =>
      ⟨flip x, dx • dflip⟩ := by

  unfold randFwdDeriv; simp (disch:= first | apply hf | sorry) [rand_simp]
  rw[flip.arg_x.randDeriv_rule _ differentiable_id']
  simp
