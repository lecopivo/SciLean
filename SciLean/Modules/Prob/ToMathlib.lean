import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.VectorMeasure
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner

open MeasureTheory Classical BigOperators

/- When `X` is a vector space: smooth functions with compact support
   When `X` is a discrete space: functions with compact support -/
class HasTestFunctions (X : Type _) where
  IsTestFunction : (X → ℝ) → Prop
  -- todo: add some general properties of test functions that can be used later on

-- test functions as known in functional analysis
instance {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    HasTestFunctions X := sorry

-- functions with finite support
instance {X} [TopologicalSpace X] [DiscreteTopology X] :
    HasTestFunctions X := sorry

open HasTestFunctions in
structure TestFunctions (X : Type _) [HasTestFunctions X] where
  toFun : X → ℝ
  is_test_function : IsTestFunction toFun


instance [HasTestFunctions X] : TopologicalSpace (TestFunctions X) := sorry
instance [HasTestFunctions X] : AddCommGroup (TestFunctions X) := sorry
instance [HasTestFunctions X] : Module ℝ (TestFunctions X) := sorry
instance [HasTestFunctions X] : TopologicalAddGroup (TestFunctions X) := sorry


-- This is just a space of distributions
structure DMeasure (X : Type) [HasTestFunctions X] where
  action : (TestFunctions X) →L[ℝ] ℝ


def DMeasure.IsMeasure {X} [MeasurableSpace X] [HasTestFunctions X] (dμ : DMeasure X) : Prop :=
  -- Use SignedMeasure but I'm not sure how to write the integral then
  ∃ (μpos μneg : Measure X),
    (IsFiniteMeasure μpos ∧ IsFiniteMeasure μneg) ∧
    ∀ φ, dμ.action φ = ∫ x, φ.1 x ∂μpos - ∫ x, φ.1 x ∂μneg


open Classical
noncomputable
def DMeasure.measure {X} [MeasurableSpace X] [HasTestFunctions X] (dμ : DMeasure X) : SignedMeasure X :=
  if h : dμ.IsMeasure then
    let μpos := choose h
    let μneg := choose (choose_spec h)
    have ⟨_,_⟩ := (choose_spec (choose_spec h)).1
    μpos.toSignedMeasure - μneg.toSignedMeasure
  else
    0


/-- Extension `DMesure.action` to any function.

  if `f = ∑ i, φ i • x i`
  then `dμ.action' f = ∑ i, dμ.action (φ i) • x i`
  and `dμ.action' f` is well defined if it does not depend on the decomposition `f = ∑ i, φ i • x i`
-/
def DMeasure.action'
  {α} [MeasurableSpace α] [HasTestFunctions α]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (dμ : DMeasure α) (f : α → X) : X := sorry

variable [HasTestFunctions Y]

noncomputable
def measureDeriv
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {α} [MeasurableSpace α] [HasTestFunctions α]
  (f : X → Measure α) (x dx : X) : DMeasure α := {
  action := ⟨⟨⟨fun φ => fderiv ℝ (fun x' => ∫ y', φ.1 y' ∂(f x')) x dx,sorry⟩,sorry⟩, sorry⟩
}

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {α} [MeasurableSpace α] [HasTestFunctions α]
  {β} [MeasurableSpace β] [HasTestFunctions β]
  {γ} [MeasurableSpace γ] [HasTestFunctions γ]


structure MeasureDifferentiable (f : X → Measure α) where
  -- some nice condition such that all the therems go through

  -- this is definitely necessary
  differentiable :
    ∀ φ : TestFunctions α, Differentiable ℝ (fun x : X => ∫ y', φ.1 y' ∂(f x))
  -- what else?
  -- It think a guiding theorem should be `deriv_measure_under_integral` what do we need to make it true?


noncomputable
def diracDeriv (x dx : X) : DMeasure X := {
  action := ⟨⟨⟨fun φ => fderiv ℝ φ.1 x dx , sorry⟩,sorry⟩,sorry⟩
}

theorem measureDeriv_dirac (x dx : X) :
    (measureDeriv (fun x' => Measure.dirac x) x dx)
    =
    diracDeriv x dx := sorry

theorem measureDifferentiable_dirac (f : E → X) (hf : Differentiable ℝ f) :
    MeasureDifferentiable (fun x => Measure.dirac (f x)) := sorry


----------------------------------------------------------------------------------------------------

-- todo: generalize to SignedMeasure
noncomputable
def bindDM (x : DMeasure α) (f : α → Measure β) : DMeasure β := {
  action := ⟨⟨⟨fun φ => x.action ⟨fun x' => ∫ y', φ.1 y' ∂(f x'),sorry⟩ ,sorry⟩,sorry⟩,sorry⟩
}

-- todo: generalize to SignedMeasure
noncomputable
def bindMD (x : Measure α) (f : α → DMeasure β) : DMeasure β := {
  action := ⟨⟨⟨fun φ => ∫ x', (f x').action φ ∂x, sorry⟩, sorry⟩, sorry⟩
}

-- noncomputable
-- def joinRD (x : Measure (DMeasure α)) : DMeasure α := x.bindRD id

-- noncomputable
-- def joinDR (x : (DMeasure (Measure X))) : DMeasure X := x.bindDR id


----------------------------------------------------------------------------------------------------
-- monatic rules


theorem bindDM_dirac (x : DMeasure α) (f : α → X) (φ : X → E) :
    (bindDM x (fun x' => Measure.dirac (f x'))).action' φ
    =
    x.action' fun x' => φ (f x') := sorry

theorem pure_bindMD (x : X) (f : X → DMeasure Y) :
    bindMD (Measure.dirac x) f = f x := sorry

theorem bindMD_diracDeriv (x : Measure α) (f df : α → X) (φ : X → E) :
    (bindMD x (fun x' => diracDeriv (f x') (df x'))).action' φ
    =
    ∫ x', fderiv ℝ φ (f x') (df x') ∂x := sorry

theorem diracDeriv_bindDM (x dx : X) (f : X → Measure α) :
    (bindDM (diracDeriv x dx) f) = measureDeriv f x dx := sorry

theorem bindDR_bindDR (x : DMeasure α) (g : α → Measure β) (f : β → Measure γ) :
    bindDM (bindDM x g) f = (bindDM x (fun x' => (g x').bind f)) := sorry

theorem bindRD_bindDR (x : Measure α) (g : α → DMeasure β) (f : β → Measure γ) :
    bindDM (bindMD x g) f = bindMD x (fun x' => bindDM (g x') f) := sorry


----------------------------------------------------------------------------------------------------

theorem dpure_action' (x dx : X) (φ : X → E) :
    (diracDeriv x dx).action' φ = fderiv ℝ φ x dx := sorry

theorem bindMD_action' (x : Measure α) (f : α → DMeasure β) (φ : β → E) :
    (bindMD x f).action' φ = ∫ x', (f x').action' φ ∂x := sorry

theorem bindDM_action' (x : DMeasure α) (f : α → Measure β) (φ : β → E) :
    (bindDM x f).action' φ = x.action' (fun x' => ∫ y, φ y ∂(f x')) := sorry


----------------------------------------------------------------------------------------------------

instance : Zero (DMeasure α) := sorry
instance : Add (DMeasure α) := sorry

----------------------------------------------------------------------------------------------------

variable
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [MeasurableSpace Z]


theorem deriv_measure_under_integral (f : Y → Measure Z) (g : X → Y) (φ : TestFunctions Z)
    (hf : MeasureDifferentiable f) (hg : Differentiable ℝ g) :
    fderiv ℝ (fun x' : X => ∫ (z : Z), φ.1 z ∂↑(f (g x'))) x dx
    =
    fderiv ℝ (fun x' => ∫ (z : Z), φ.1 z ∂(f x')) (g x) (fderiv ℝ g x dx) := sorry



theorem measureDeriv_const (a : Measure α) :
    measureDeriv (fun _ : X => a)
    =
    fun w dw => 0 := sorry


theorem measureDeriv_comp (f : Y → Measure Z) (g : X → Y)
    (hf : MeasureDifferentiable f) (hg : Differentiable ℝ g) :
    measureDeriv (fun x : X => (f (g x)))
    =
    fun x dx =>
      let y := g x
      let dy := fderiv ℝ g x dx
      measureDeriv f y dy := sorry


theorem Rand.bind.arg_xf.measureDeriv_rule (x : X → Measure α) (f : X → α → Measure β)
    (hx : MeasureDifferentiable x) (hf : ∀ x, MeasureDifferentiable (f · x)) :
    measureDeriv (fun w => (x w).bind (f w))
    =
    fun w dw => bindDM (measureDeriv x w dw) (f w · )
                +
                bindMD (x w) (fun x => measureDeriv (f · x) w dw) := sorry
