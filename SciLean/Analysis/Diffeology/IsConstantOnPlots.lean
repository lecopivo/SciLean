import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.TangentSpace
import SciLean.Analysis.Diffeology.Prod
import SciLean.Analysis.Diffeology.Array

namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ

variable {X : Type*} [Diffeology X]

open Diffeology

@[fun_prop]
structure IsConstantOnPlots {X : Type*} [Diffeology X] {α : Sort u} (f : X → α) : Prop where
  val : ∀ n (p : Plot X n), ∃ c, ∀ m (g : ℝ^m → ℝ^n) (hg : ContDiff ℝ ⊤ g) (u : ℝ^m), f (p (g u)) = c

@[fun_prop]
theorem IsConstantOnPlots.const_rule {α : Sort u} (a : α):
  IsConstantOnPlots (fun x : X => a) := sorry

@[fun_prop]
theorem IsConstantOnPlots.comp_rule {X : Type*} [Diffeology X] (f : α → β) (g : X → α) (hg : IsConstantOnPlots g) :
  IsConstantOnPlots (fun x => f (g x)) := sorry


----------------------------------------------------------------------------------------------------


omit [Diffeology X] in
@[fun_prop]
theorem Array.size.arg_a.IsConstantOnPlots_rule [NormedAddCommGroup X] [NormedSpace ℝ X] :
    IsConstantOnPlots (fun x : Array X => x.size) := by

  constructor
  intro n p
  use p.dim
  intro m g _ u
  simp_all

open Classical

@[fun_prop]
theorem decide.arg_p.IsConstantOnPlots_rule (f : X → Prop) (df : (x : X) → Decidable (f x)) (hf : IsConstantOnPlots f) :
    IsConstantOnPlots (fun x => @decide (f x) (df x)) := by

  constructor
  intro n p
  have hc := choose_spec (hf.val n p)
  use (decide (f (p 0)))
  intro m g hg u;
  by_cases h0 : (f (p 0))
  · by_cases hu : (f (p (g u)))
    · simp[h0,hu]
    · simp[hc n (fun x => x) (by fun_prop) 0] at h0
      simp[hc m g hg u] at hu
      tauto
  · by_cases hu : (f (p (g u)))
    · simp[hc n (fun x => x) (by fun_prop) 0] at h0
      simp[hc m g hg u] at hu
      tauto
    · simp[h0,hu]


def subsetDiffeology (X : Type*) [Diffeology X] {c : X → Prop} (hc : IsConstantOnPlots c) : Diffeology {x : X // c x} where
  Plot n := {p : Plot X n // ∀ u, c (p u)}
  plotEval p u := ⟨p.1 u, p.2 u⟩
  plot_ext := by intro n ⟨x,hx⟩ ⟨y,hy⟩ h; simp; apply plot_ext; intro u; have hh := congrFun h u; simp_all
  plotComp p f hf := ⟨plotComp p.1 hf, fun u => sorry⟩
  plotComp_eval := by intros; simp
  constPlot n x := ⟨constPlot n x.1, by simp[x.2]⟩
  constPlot_eval := by intros; simp


@[fun_prop]
theorem dite.arg_cte.DSmooth_rule
  {X : Type*} [Diffeology X] {Y : Type*} [Diffeology Y]
  (c : X → Prop) (hc : IsConstantOnPlots c) (hc' : IsConstantOnPlots (fun x => ¬c x))
  (t : (x : X) → c x → Y) (ht : @DSmooth _ (subsetDiffeology _ hc) _ _ (fun x : {x // c x} => t x.1 x.2))
  (e : (x : X) → ¬c x → Y) (he : @DSmooth _ (subsetDiffeology _ hc') _ _ (fun x : {x // ¬c x} => e x.1 x.2)) :
  DSmooth (fun x => dite (c x) (t x) (e x)) := sorry


example : IsConstantOnPlots (fun x : Array ℝ => decide (x.size < 10)) := by fun_prop


theorem asdf' (f : X → Prop) (df : (x : X) → Decidable (f x)) (hf : IsConstantOnPlots f) :
  IsConstantOnPlots (fun x => @decide (f x) (df x)) := by sorry




-- @[fun_prop]
-- theorem dite.adsf
--   (f : X → Prop) (df : (x : X) → Decidable (f x)) (hf : IsConstantOnPlots f) :
--     IsConstantOnPlots (fun x => @decide (f x) (df x)) := by

--   constructor
--   intro n p
--   have hc := choose_spec (hf.val n p)
--   use (decide (f (p 0)))
--   intro u;
--   by_cases h0 : (f (p 0))
--   · by_cases hu : (f (p u))
--     · simp[h0,hu]
--     · simp[hc 0] at h0
--       simp[hc u] at hu
--       tauto
--   · by_cases hu : (f (p u))
--     · simp[hc 0] at h0
--       simp[hc u] at hu
--       tauto
--     · simp[h0,hu]
