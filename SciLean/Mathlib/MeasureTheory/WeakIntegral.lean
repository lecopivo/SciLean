import Mathlib.MeasureTheory.Integral.Bochner

import SciLean.Util.SorryProof

namespace MeasureTheory

variable
  {α} [MeasurableSpace α]
  {E} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [LocallyConvexSpace ℝ E]


def WeakMeasurable (f : α → E) :=
  ∀ e' : E →L[ℝ] ℝ, Measurable (fun x => e' (f x))

def AEWeakMeasurable (f : α → E) (μ : Measure α) :=
  ∃ g : α → E, WeakMeasurable g ∧ f =ᵐ[μ] g

def HasWeakIntegral (f : α → E) (e : E) (μ : Measure α) :=
  ∀ (e' : E →L[ℝ] ℝ),
    Integrable (fun x => e' (f x)) μ
    ∧
    ∫ x, e' (f x) ∂μ = e' e

def WeakIntegrable (f : α → E) (μ : Measure α) := ∃ e, HasWeakIntegral f e μ

open Classical in
noncomputable
def weakIntegral (μ : Measure α) (f : α → E) : E :=
  if h : WeakIntegrable f μ then
    Classical.choose h
  else
    0

-- I think here we utilize the locall covexity of E
theorem weak_integral_unique (f : α → E) (e : E) (μ : Measure α) :
    HasWeakIntegral f e μ → e = weakIntegral μ f := sorry_proof


-- I think here we utilize the locall covexity of E
theorem integrable_is_weak_integrable {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α → E) (μ : Measure α) :
    Integrable f μ → WeakIntegrable f μ := sorry_proof

theorem weak_integral_eq_integral {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α → E) (μ : Measure α) :
    Integrable f μ → weakIntegral μ f = ∫ x, f x ∂μ := sorry_proof

-- the big advantage of weak integral is
set_option linter.unusedVariables false in
theorem pointwise_integral (f : ι → α → E)
    (hf : ∀ i, WeakIntegrable (f i) μ) :
    weakIntegral μ (fun x => (f · x))
    =
    fun i => weakIntegral μ (fun x => f i x) := sorry_proof


@[simp]
theorem weakIntegral_dirac [MeasurableSingletonClass α] (f : α → E) (x : α) :
    weakIntegral (Measure.dirac x) f
    =
    f x := sorry_proof


@[simp]
theorem weakIntegral_zero (μ : Measure α) :
    weakIntegral μ (fun _ : α => (0:E))
    =
    0 := sorry_proof


set_option linter.unusedVariables false in
theorem weakIntegral_add (μ : Measure α)
    (f g : α → E) (hf : WeakIntegrable f μ) (hg : WeakIntegrable g μ)  :
    weakIntegral μ (fun x => f x + g x)
    =
    weakIntegral μ f + weakIntegral μ g := sorry_proof



set_option linter.unusedVariables false in
theorem weakIntegral_smul (μ : Measure α)
    (f g : α → E) (hf : WeakIntegrable f μ) (hg : WeakIntegrable g μ)  :
    weakIntegral μ (fun x => f x + g x)
    =
    weakIntegral μ f + weakIntegral μ g := sorry_proof


-- what are the correct conditions here?
set_option linter.unusedVariables false in
theorem weakIntegral_map
    {β} [MeasurableSpace β] {φ : α → β} (hφ : AEMeasurable φ μ) {f : β → E}
    (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
    weakIntegral (Measure.map φ μ) f = weakIntegral μ (fun x => f (φ x)) := sorry_proof
