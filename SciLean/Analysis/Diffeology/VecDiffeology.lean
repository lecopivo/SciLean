import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.Prod


namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ


open Diffeology in
class StandardDiffeology (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [Diffeology X] : Prop where
  plots_smooth {n} : ∀ {p : ℝ^n → X}, IsPlot (X:=X) p ↔ ContDiff ℝ ⊤ p

open Diffeology in
@[fun_prop]
theorem plot_contDiff
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Diffeology X] [StandardDiffeology X]
    (p : Plot X n) :
    ContDiff ℝ ⊤ p := by
  apply StandardDiffeology.plots_smooth.1
  simp


def mkStandardDiffeology (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Diffeology X where
  Plot n := {p : ℝ^n → X // ContDiff ℝ ⊤ p}
  plotEval p u := p.1 u
  plot_ext := by simp
  plotComp {n m} p {f} hf := ⟨fun x => p.1 (f x), by have := p.2; fun_prop⟩
  plotComp_eval := by simp
  constPlot n x := ⟨fun _ : ℝ^n => x, by fun_prop⟩
  constPlot_eval := by simp

noncomputable
instance : Diffeology ℝ := mkStandardDiffeology ℝ
instance : StandardDiffeology ℝ where
  plots_smooth := by
    intro n p
    constructor
    · intro hp; rw[← Classical.choose_spec hp]; exact (Classical.choose hp).2;
    · intro hp; apply Exists.intro ⟨p,hp⟩; rfl


open Diffeology in
class VecDiffeology (X : Type*) [AddCommGroup X] [Module ℝ X] [Diffeology X] : Prop where
  add_plot : ∀ (p q : Plot X n), IsPlot (fun u => p u + q u)
  smul_plot : ∀ (p : Plot ℝ n) (q : Plot X n), IsPlot (fun u => p u • q u)

open StandardDiffeology
instance (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [Diffeology X] [StandardDiffeology X] : VecDiffeology X where
  add_plot := by
    intro n p q
    apply plots_smooth.2
    have := plots_smooth.1 p.isPlot
    have := plots_smooth.1 q.isPlot
    fun_prop
  smul_plot := by
    intro n p q
    apply plots_smooth.2
    have := plots_smooth.1 p.isPlot
    have := plots_smooth.1 q.isPlot
    fun_prop


open Diffeology
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Diffeology X] [StandardDiffeology X]

noncomputable
def mkVecPlot (f : ℝ^n → X) (hf : ContDiff ℝ ⊤ f) : Plot X n := Classical.choose (plots_smooth.2 hf)

@[simp]
theorem mkVecPlot_eval (f : ℝ^n → X) (hf : ContDiff ℝ ⊤ f) :
  mkVecPlot f hf = f := by

  funext u
  have h := plots_smooth.2 hf
  have hh := congrFun (Classical.choose_spec h) u
  rw[← hh]; rfl

open TangentSpace
open StandardDiffeology
noncomputable
instance (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [Diffeology X] [StandardDiffeology X] :
    TangentSpace X (fun _ => X) where
  tangentMap p u := ⟨p u, fderiv ℝ p u⟩
  tangentMap_const := by simp
  tangentMap_fst := by simp
  exp := fun ⟨x,dx⟩ => mkVecPlot (fun t => x + t 0 • dx) (by fun_prop)
  exp_at_zero := by intro ⟨x,dx⟩; simp
  tangentMap_exp_at_zero := by intro ⟨x,dx⟩; fun_trans; rfl
