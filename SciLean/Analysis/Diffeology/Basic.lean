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

/-- Diffeology on `X`, a minimal structure on a type to talk about smoothness.

A generalization of topological spaces and manifolds such that we can talk about smooth maps between
two diffeological spaces.

TODO: plots should be generalized maps from open subsets of `ℝⁿ` to `X`
  -/
class Diffeology (X : Type v) where
  /-- Set of mooth maps from `ℝ̂ⁿ` to `X`. -/
  plots (n : ℕ) : Set ((Fin n → ℝ) → X)
  /-- Pots are closed under composition with a smooth function. -/
  plot_comp {n m} {p} {f : (Fin n → ℝ) → (Fin m → ℝ)}
    (ph : p ∈ plots m) (hf : ContDiff ℝ ⊤ f) : p ∘ f ∈ plots n
  /-- Constant plots are differentiable. -/
  const_plot (n : ℕ) (x : X) : (fun _ => x) ∈ plots n


section DDifferentiable

open Diffeology

variable
  {X : Type*} [Diffeology X]
  {Y : Type*} [Diffeology Y]
  {Z : Type*} [Diffeology Z]

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
  plot_preserving {n : ℕ} (p : (Fin n → ℝ) → X) (hp : p ∈ plots n) : f ∘ p ∈ plots n


namespace DSmooth

@[fun_prop]
theorem id_rule : DSmooth (fun x : X => x) := by
  constructor
  · intros; unfold Function.comp; simp_all

@[fun_prop]
theorem const_rule (y : Y) : DSmooth (fun _ : X => y) := by
  constructor
  · intros; simp only [Function.comp_def, const_plot]

@[fun_prop]
theorem comp_rule (f : Y → Z) (g : X → Y)
    (hf : DSmooth f) (hg : DSmooth g) :
    DSmooth (fun x => f (g x)) := by
  constructor
  · intros n p hp;
    exact hf.plot_preserving _ (hg.plot_preserving _ hp)

end DSmooth

end DDifferentiable
