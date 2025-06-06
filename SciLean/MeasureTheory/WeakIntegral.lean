import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- import Mathlib.MeasureTheory.Integral.Bochner.L1
-- import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory

import SciLean.Meta.SimpAttr
import SciLean.Util.SorryProof

namespace MeasureTheory

set_option deprecated.oldSectionVars true
variable
  {α} [MeasurableSpace α]
  {E} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [LocallyConvexSpace ℝ E]


def WeakMeasurable (f : α → E) :=
  ∀ e' : E →L[ℝ] ℝ, Measurable (fun x => e' (f x))

def AEWeakMeasurable (f : α → E) (μ : Measure α) :=
  ∃ g : α → E, WeakMeasurable g ∧ f =ᵐ[μ] g

/-- Element `e` is weak(Pettis) integral of `f`

wiki:https://en.wikipedia.org/wiki/Pettis_integral

Also see documentation for `weakIntegral`
-/
def HasWeakIntegral (f : α → E) (e : E) (μ : Measure α) :=
  ∀ (e' : E →L[ℝ] ℝ),
    Integrable (fun x => e' (f x)) μ
    ∧
    ∫ x, e' (f x) ∂μ = e' e


/-- Function `f` is weakly(Pettis) integrable

wiki:https://en.wikipedia.org/wiki/Pettis_integral

Also see documentation for `weakIntegral`
-/
def WeakIntegrable (f : α → E) (μ : Measure α) := ∃ e, HasWeakIntegral f e μ

open Classical in
/-- Weak(Pettis) Integral

Element `e` is weak integral of `f : α → E` if for all elements of the dual space `e' : E →L[ℝ] ℝ`
the integral of `fun x => e' (f x )` is equal to `e' e`, i.e.
```
∀ e', ∫ x, e' (f x) ∂μ = e' e
```

The main reason for introducing weak integral in SciLean is that we can integrate functions like
`f : α → ι → E` where `ι` is arbitrary type, not necessarily finite. Strong(Bochner) integral can
integrate `f : α → ι → E` only if `ι` is finite and `E` is normed space as then `ι → E` is
normed space too.

Our main application is when working with random variables as we can talk about random functions
`f : Rand (ι → E)` for arbitrary `ι` and `E` locally convex vector space.

wiki:https://en.wikipedia.org/wiki/Pettis_integral
 -/
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


@[simp, simp_core]
theorem weakIntegral_dirac [MeasurableSingletonClass α] (f : α → E) (x : α) :
    weakIntegral (Measure.dirac x) f
    =
    f x := sorry_proof


@[simp, simp_core]
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
theorem weakIntegral_smul {R} [RCLike R] [Module R E] [IsScalarTower ℝ R E] (μ : Measure α)
    (f : α → E) (hf : WeakIntegrable f μ) (c : R) :
    weakIntegral μ (fun x => c • f x)
    =
    c • weakIntegral μ f := sorry_proof


-- what are the correct conditions here?
set_option linter.unusedVariables false in
theorem weakIntegral_map
    {β} [MeasurableSpace β] {φ : α → β} (hφ : AEMeasurable φ μ) {f : β → E}
    (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
    weakIntegral (Measure.map φ μ) f = weakIntegral μ (fun x => f (φ x)) := sorry_proof
