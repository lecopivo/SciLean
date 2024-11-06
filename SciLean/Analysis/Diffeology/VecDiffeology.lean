import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.Prod


namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ


open Diffeology in
class StandardDiffeology (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [Diffeology X] : Prop where
  plots_smooth : ∀ {n} {p : ℝ^n → X}, (p ∈ plots n) ↔ ContDiff ℝ ⊤ p := by rfl


def mkStandardDiffeology (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Diffeology X where
  plots n p := ContDiff ℝ ⊤ p
  plot_comp := by
    intro n m p f hp hf
    exact hp.comp hf
  const_plot := by
    intros;
    apply contDiff_const


instance : Diffeology ℝ := mkStandardDiffeology ℝ
instance : StandardDiffeology ℝ where
  plots_smooth := by intros; rfl


open Diffeology in
class VecDiffeology (X : Type*) [AddCommGroup X] [Module ℝ X] [Diffeology X] : Prop where
  add_plot : ∀ (p q : ℝ^n → X),
    p ∈ plots n → q ∈ plots n → (fun u => p u + q u) ∈ plots n
  smul_plot : ∀ (p : ℝ^n → ℝ) (q : ℝ^n → X),
    p ∈ plots n → q ∈ plots n → (fun u => p u • p u) ∈ plots n


open StandardDiffeology
instance (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [Diffeology X] [StandardDiffeology X] : VecDiffeology X where
  add_plot := by
    intro n p q hp hq
    apply plots_smooth.2
    have := plots_smooth.1 hp
    have := plots_smooth.1 hq
    fun_prop
  smul_plot := by
    intro n p q hp hq
    apply plots_smooth.2
    have := plots_smooth.1 hp
    have := plots_smooth.1 hq
    fun_prop


open StandardDiffeology
noncomputable
instance (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [Diffeology X] [StandardDiffeology X] :
    TangentSpace X (fun _ => X) where
  tangentMap p _ u du := fderiv ℝ p u du
  tangentMap_comp := by
    intro n m p f hp hf u du
    have := plots_smooth.1 hp
    fun_trans[Function.comp_def]
  tangentMap_const := by
    intros
    fun_trans
  tangentMap_linear := by
    intros; dsimp; fun_prop
  exp x dx t := x + t 0 • dx
  exp_at_zero := by simp
  exp_is_plot := by intro x dx; apply plots_smooth.2; fun_prop
  tangentMap_exp_at_zero := by intros; fun_trans
