import SciLean.Modules.Prob.RandDeriv
import SciLean.Modules.Prob.FDRand


open MeasureTheory ENNReal BigOperators Finset

namespace SciLean.Prob

open Rand

variable
  {R} [RealScalar R]
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace R W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace R X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedSpace R Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedSpace R Z] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]



----------------------------------------------------------------------------------------------------
-- Lambda and Monadic Rules ------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[simp,rand_AD]
theorem randFwdDeriv_const (a : Rand α) :
    randFwdDeriv (fun _ : W => a)
    =
    fun _ _ => ⟨a,0⟩ := by

  unfold randFwdDeriv
  simp only [rand_simp]


@[simp,rand_AD]
theorem randFwdDeriv_comp (f : Y → Rand Z) (g : X → Y)
    (hf : RandDifferentiable f) (hg : Differentiable ℝ g) :
    randFwdDeriv (fun x : X => (f (g x)))
    =
    fun x dx =>
      let ydy := fwdFDeriv ℝ g x dx
      randFwdDeriv f ydy.1 ydy.2 := by

  funext x dx
  unfold randFwdDeriv fwdFDeriv
  simp (disch := first | apply hf | apply hg) only [rand_simp,randDeriv_comp,fwdFDeriv]



@[simp,rand_AD]
theorem FDRand.pure.arg_x.randFwdDeriv_rule (x : W → X) (hx : Differentiable ℝ x) :
    randFwdDeriv (fun w => pure (x w))
    =
    fun w dw =>
      let xdx := fwdFDeriv ℝ x w dw
      fdpure xdx.1 xdx.2 := by

  unfold randFwdDeriv fdpure
  simp (disch:=first | apply hx | sorry) only [rand_simp,fwdFDeriv]
  funext w dw
  rw [Rand.pure.arg_x.randDeriv_rule _ differentiable_id']
  simp


@[simp,rand_AD]
theorem FDRand.pure.arg_x.randFwdDeriv_rule_simple :
    randFwdDeriv (fun x : X => Rand.pure x)
    =
    fun x dx =>
      fdpure x dx := by

  unfold randFwdDeriv fdpure
  simp (disch:=first | apply hx | sorry) [rand_simp]
  funext w dw
  rw [Rand.pure.arg_x.randDeriv_rule _ differentiable_id']
  simp (disch:=first | apply hx | sorry) [rand_simp]


@[simp,rand_AD]
theorem Rand.bind.arg_xf.randFwdDeriv_rule (x : W → Rand α) (f : W → α → Rand β)
    (hx : RandDifferentiable x) (hf : ∀ x, RandDifferentiable (f · x)) :
    randFwdDeriv (fun w => (x w).bind (f w ·))
    =
    fun w dw => (randFwdDeriv x w dw).bind (fun x => randFwdDeriv (f · x) w dw) := by

  unfold randFwdDeriv FDRand.bind
  simp (disch:=first | apply hx | apply hf) only [rand_simp]



----------------------------------------------------------------------------------------------------
-- Other Rules -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[simp,rand_AD]
theorem ite.arg_tf.randFwdDeriv_rule {c} [Decidable c] (t f : W → Rand α) :
    randFwdDeriv (fun w => if c then (t w) else (f w))
    =
    fun w dw => if c then randFwdDeriv t w dw else randFwdDeriv f w dw := by
  if h : c then simp[h] else simp[h]

@[simp,rand_AD]
theorem Rand.E.arg_x.fderiv_rule (f : X → Rand Y) (φ : Y → Z) (x dx : X) (hf : RandDifferentiable f) :
    fderiv R (fun x' => (f x').E φ) x dx = ((randFwdDeriv f x dx).fdE φ).2 := sorry

@[simp,rand_AD]
theorem Rand.mean.arg_x.fderiv_rule (f : X → Rand Y) (x dx : X) (hf : RandDifferentiable f) :
    fderiv R (fun x' => (f x').mean) x dx = ((randFwdDeriv f x dx).fdmean).2 := sorry

@[simp,rand_AD]
theorem Rand.mean.arg_x.fwdDeriv_rule (f : X → Rand Y) (x dx : X) (hf : RandDifferentiable f) :
    fwdFDeriv R (fun x' => (f x').mean) x dx = ((randFwdDeriv f x dx).fdmean) := sorry
