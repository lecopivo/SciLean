import SciLean.Analysis.Diffeology.PlotHomotopy

namespace SciLean

local notation:max "ℝ^" n:max => (Fin n) → ℝ

open Diffeology in
class Connection {X : Type*} (E : X → Type*) [Diffeology X] [∀ x, Diffeology (E x)] where
  /-- Lifts curve `c` on the base space `X` to the fibers `E (c x)` given a single fiber value `v`.

  Also known as parrallel transport of `v` along `c`. -/
  lift (c : ℝ^1 → X) (s t) (v : E (c s)) : E (c t)

  lift_inv (c : ℝ^1 → X) (hc : c ∈ plots 1) (s) (v : E (c s)) (t) :
    lift c t s (lift c s t v) = v

  lift_trans (c : ℝ^1 → X) (hc : c ∈ plots 1) (s r t) (v : E (c s)) :
    lift c r t (lift c s r v) = lift c s t v

  smooth_comp {n m}
    {p : ℝ^n → Sigma E}
    {ht : PlotPointHomotopy (fun u => (p u).1) x}
    {hp₂ : ht.transportSection' lift (fun u => (p u).2) ∈ plots n}
    (f : ℝ^m → ℝ^n) (hf : ContDiff ℝ ⊤ f)
    (ht' : PlotPointHomotopy (fun u => (p (f u)).1) x) :
    ht'.transportSection' lift (fun u => (p (f u)).2) ∈ plots m


def PlotPointHomotopy.transportSection
    {X : Type*} {E : X → Type*} [Diffeology X] [∀ x, Diffeology (E x)] [Connection E]
    {p : (Fin n → ℝ) → X} {x : X}
    (ht : PlotPointHomotopy p x)
    (v : (u : (Fin n → ℝ)) → E (p u)) : (Fin n → ℝ) → E x :=
  ht.transportSection' Connection.lift v


open Diffeology Util in
instance {X : Type*} (E : X → Type*) [Diffeology X] [∀ x, Diffeology (E x)] [Connection E] :
    Diffeology (Sigma E) where

  plots n c :=
    (fun u => (c u).1) ∈ plots n
    ∧
    ∀ (x : X) (ht : PlotPointHomotopy (fun u => (c u).1) x),
      ht.transportSection (fun x => (c x).2) ∈ plots n

  plot_comp := by
    intro n m p f hp hf
    have hp₁ := hp.1
    have hp₂ := hp.2
    constructor
    · apply plot_comp hp₁ hf
    · intro x ht
      unfold PlotPointHomotopy.transportSection
      apply Connection.smooth_comp (f:=f) (hf:=hf)
            (ht:=(ht.toPathAt 0).compPathLeft (PlotHomotopy.toPoint _ hp₁ (f 0)))
      · apply hp₂

  const_plot := by
    intros
    constructor
    · apply Diffeology.const_plot
    · intros
      simp
      unfold PlotPointHomotopy.transportSection
      unfold PlotPointHomotopy.transportSection'
      simp
      sorry
