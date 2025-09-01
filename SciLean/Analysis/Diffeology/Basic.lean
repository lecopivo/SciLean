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

theorem Diffeology.Plot.isPlot (p : Plot X n) : IsPlot (X:=X) p := by
  apply Exists.intro p
  rfl

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
theorem plotComp_eval (p : Plot X n) {f : ℝ^m → ℝ^n} (hf : ContDiff ℝ ⊤ f) :
  p.comp hf = fun u => p (f u) := by funext u; exact Diffeology.plotComp_eval p hf u


@[simp]
theorem plot_is_plot {n} (p : Plot X n) : IsPlot p := ⟨p,rfl⟩

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
  ex_map_plot : ∃ g : (n : ℕ) → Plot X n → Plot Y n,
    ∀ n u p, g n p u = f (p u)

open Classical in
noncomputable
def DSmooth.mapPlot {n} (f : X → Y) (hf : DSmooth f) (p : Plot X n) : Plot Y n :=
  choose hf.ex_map_plot n p


namespace Diffeology
scoped notation f:90 " ∘["hf"] " p:91 => DSmooth.mapPlot f hf p
scoped notation f:90 " ∘ₚ " p:91 => DSmooth.mapPlot f (by fun_prop) p
end Diffeology

@[simp]
theorem DMoosth.mapPlot_eval (f : X → Y) (hf : DSmooth f) {n} (p : Plot X n) (u) :
    (f ∘[hf] p) u = f (p u) := by
  simp[DSmooth.mapPlot]
  exact Classical.choose_spec hf.ex_map_plot _ u p


namespace DSmooth

@[fun_prop]
theorem id_rule : DSmooth (fun x : X => x) := by
  constructor
  use (fun _ p => p); simp

@[fun_prop]
theorem const_rule (y : Y) : DSmooth (fun _ : X => y) := by
  constructor
  use (fun n _ => constPlot n y); simp

@[fun_prop]
theorem comp_rule (f : Y → Z) (g : X → Y)
    (hf : DSmooth f) (hg : DSmooth g) :
    DSmooth (fun x => f (g x)) := by
  constructor
  use (fun _ p => f ∘[hf] (g ∘[hg] p))
  simp


end DSmooth

end DDifferentiable
