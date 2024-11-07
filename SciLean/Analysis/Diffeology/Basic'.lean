import SciLean.Tactic.Autodiff
import SciLean.Data.ArrayN

import SciLean.Analysis.Diffeology.Util

/-!

# Diffeology

Diffeology (or diffeological space) on `X` is a minimal structure necessary to talk about smooth
maps.

This file has a definition of `Diffeology` and smooth map `DSmooth` between two diffeological
spaces.

wiki: https://en.wikipedia.org/wiki/Diffeology

TODO: Missing:
  - Plots should be maps from open sets of `ℝⁿ` to `X`.
  - Define `DSmoothAt`
  - Relaxed notions of diffology where plots are preserved when composed with differentiable
    (not smooth) maps

-/

namespace SciLean

open Diffeology.Util

local notation:max "ℝ^" n:max => Fin n → ℝ

/-- Diffeology on `X`, a minimal structure on a type to talk about smoothness.

A generalization of topological spaces and manifolds such that we can talk about smooth maps between
two diffeological spaces.

TODO: plots should be generalized maps from open subsets of `ℝⁿ` to `X`
  -/
class Diffeology (X : Type v) where
  Plot : ℕ → Type v
  plotEval {n} : Plot n → ℝ^n → X
  plot_ext (p q : Plot n) : plotEval p = plotEval q → p = q
  /-- Pots are closed under composition with a smooth function. -/
  plotComp {n m} (p : Plot n) {f : ℝ^m → ℝ^n} (hf : ContDiff ℝ ⊤ f) : Plot m
  plotComp_eval {n m} (p : Plot n) {f : ℝ^m → ℝ^n} (hf : ContDiff ℝ ⊤ f) (u : ℝ^m) :
    plotEval (plotComp p hf) u = plotEval p (f u)
  /-- Constant plots are differentiable. -/
  constPlot (n : ℕ) (x : X) : Plot n
  constPlot_eval (n x u) : plotEval (constPlot n x) u = x


section DDifferentiable

open Diffeology

variable
  {X : Type*} [Diffeology X]
  {Y : Type*} [Diffeology Y]
  {Z : Type*} [Diffeology Z]


def IsPlot {n} (f : ℝ^n → X) : Prop := ∃ p : Plot X n, plotEval p = f

instance : DFunLike (Plot X n) (ℝ^n) (fun _ => X) where
  coe := plotEval
  coe_injective' := plot_ext

@[ext]
theorem plot_ext (p q : Plot X n) : (∀ x, p x = q x) → p = q := by
  intro h; apply Diffeology.plot_ext
  funext x; exact (h x)

@[simp]
theorem plotEval_normalize (p : Plot X n) : plotEval p = p := by rfl

@[simp]
theorem constPlot_eval {n} (x : X) : constPlot n x = fun _ : ℝ^n => x := by
  funext u
  exact Diffeology.constPlot_eval n x u

def Diffeology.Plot.comp {n} (p : Plot X n) {f : ℝ^m → ℝ^n} (hf : ContDiff ℝ ⊤ f) : Plot X m :=
  plotComp p hf

@[simp]
theorem plotComp_normalize (p : Plot X n) {f : ℝ^m → ℝ^n} (hf : ContDiff ℝ ⊤ f) :
  plotComp p hf = p.comp hf := by rfl



@[simp]
theorem plot_is_plot {n} (p : Plot X n) : IsPlot p := sorry

/-- Smooth function between diffeological spaces.

Smooth function maps plots to plots.

NOTE: To actually compute derivatives we seem to need a more refined definition of smoothness. See
      - `TSSmooth` - "tangent space smooth" when we have `TangentSpace X TX`
      - `TBSmooth` - "tangent bundle smooth" when we have `TangentBundle X TX`
      `TSSmooth` and `TBSmooth` should be equivalend. We have both variants to see which one is
      easier to work with.

TODO: Define `DSmoothAt` variant once plots are generalized to maps from open subsets of `ℝⁿ` to `X` -/
@[fun_prop]
structure DSmooth (f : X → Y) : Prop where
  plot_preserving {n : ℕ} (p : Plot X n) : IsPlot (f ∘ p)


theorem DSmooth.compPlot {f : X → Y} (hf : DSmooth f) {p : ℝ^n → X} (hp : IsPlot p) : IsPlot (fun x => f (p x)) := sorry

noncomputable
def DSmooth.comp {f : X → Y} (hf : DSmooth f) (p : Plot X n) : Plot Y n  := sorry

@[simp]
theorem DSmooth.comp_eval {f : X → Y} (hf : DSmooth f) (p : Plot X n) (u : ℝ^n) :
  (hf.comp p) u = f (p u)  := sorry

namespace DSmooth

@[fun_prop]
theorem id_rule : DSmooth (fun x : X => x) := by
  constructor
  · intros n p; apply Exists.intro p; ext; simp

@[fun_prop]
theorem const_rule (y : Y) : DSmooth (fun _ : X => y) := by
  constructor
  · intros n p; apply Exists.intro (constPlot _ y); ext; simp

@[fun_prop]
theorem comp_rule (f : Y → Z) (g : X → Y)
    (hf : DSmooth f) (hg : DSmooth g) :
    DSmooth (fun x => f (g x)) := by
  constructor
  · intros n p; simp[Function.comp_def]
    apply hf.compPlot
    apply hg.compPlot
    simp

end DSmooth

end DDifferentiable
