import SciLean.Analysis.Diffeology.Basic

namespace SciLean

variable
  {I : Type*}
  {E : I → Type*} {TE : outParam ((i : I) → E i → Type*)} [∀ i, Diffeology (E i)]
  [∀ i e, AddCommGroup (TE i e)] [∀ i e, Module ℝ (TE i e)] [∀ i, TangentSpace (E i) (TE i)]

open Diffeology in
instance : Diffeology ((i : I) → E i) where
  plots := fun n p => ∀ i,
    (p · i) ∈ plots n
  smooth_comp := by
    intros n m p f hp hf i
    exact Diffeology.smooth_comp (hp i) hf
  const_plot := by
    intros n x i
    exact Diffeology.const_plot n (x i)

open TangentSpace in
instance
    {I : Type*}
    {E : I → Type*} {TE : outParam ((i : I) → E i → Type*)} [∀ i, Diffeology (E i)]
    [∀ i e, AddCommGroup (TE i e)] [∀ i e, Module ℝ (TE i e)] [∀ i, TangentSpace (E i) (TE i)] :
    TangentSpace ((i : I) → E i) (fun f => (i : I) → TE i (f i)) where

  tangent c hc x dx i := tangent (c · i) (hc i) x dx

  smooth_comp := by
    intros n m p f hp hf x dx
    have := fun i => smooth_comp (hp i) hf x dx
    simp_all [Function.comp_def]

  tangent_const := by
    intro n x t dt
    funext i;
    have := tangent_const (x i) t dt
    simp_all

  curve x dx t i := curve (x i) (dx i) t
  curve_at_zero := by intros; simp
  curve_is_plot x dx:= fun i => curve_is_plot (x i) (dx i)

  tangent_curve_at_zero := by
    intros x dx t
    funext i
    have := tangent_curve_at_zero (x i) (dx i) t
    simp_all

  tangent_linear := by
    intros n c hc x
    have := fun i => (tangent_linear _ (hc i) x).1
    have := fun i => (tangent_linear _ (hc i) x).2
    constructor <;> (intros; funext; simp_all)
