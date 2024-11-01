import SciLean.Analysis.Diffeology.Basic

namespace SciLean

variable
  {X : Type*} {TX : outParam (X → Type*)} [Diffeology X] [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
  {Y : Type*} {TY : outParam (Y → Type*)} [Diffeology Y] [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]
  {Z : Type*} {TZ : outParam (Z → Type*)} [Diffeology Z] [∀ z, AddCommGroup (TZ z)] [∀ z, Module ℝ (TZ z)] [TangentSpace Z TZ]

open Diffeology in
instance : Diffeology (X × Y) where
  plots := fun n p =>
    Prod.fst ∘ p ∈ plots n ∧ Prod.snd ∘ p ∈ plots n
  smooth_comp := by
    intros n m p f hp hf
    constructor
    · exact Diffeology.smooth_comp hp.1 hf
    · exact Diffeology.smooth_comp hp.2 hf
  const_plot := by
    intros n x
    constructor
    · exact Diffeology.const_plot n x.1
    · exact Diffeology.const_plot n x.2

open TangentSpace in
instance
    {X : Type*} {TX : outParam (X → Type*)} [Diffeology X]
    {Y : Type*} {TY : outParam (Y → Type*)} [Diffeology Y]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
    [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY] :
    TangentSpace (X × Y) (fun xy => TX xy.1 × TY xy.2) where

  tangent c hc x dx := (tangent (Prod.fst ∘ c) hc.1 x dx, tangent (Prod.snd ∘ c) hc.2 x dx)

  smooth_comp := by
    intros n m p f hp hf x dx
    have := smooth_comp hp.1 hf x dx
    have := smooth_comp hp.2 hf x dx
    simp_all [Function.comp_def]

  tangent_const := by
    intro n x t dt
    have := tangent_const x.1 t dt
    have := tangent_const x.2 t dt
    simp_all [Function.comp_def]

  curve x dx t := (curve x.1 dx.1 t, curve x.2 dx.2 t)
  curve_at_zero := by intros; simp
  curve_is_plot x dx:= ⟨curve_is_plot x.1 dx.1, curve_is_plot x.2 dx.2⟩

  tangent_curve_at_zero := by
    intros x dx t
    have := tangent_curve_at_zero x.1 dx.1 t
    have := tangent_curve_at_zero x.2 dx.2 t
    simp_all [Function.comp_def]
    ext <;> simp

  tangent_linear := by
    intros n c hc x
    have := (tangent_linear _ hc.1 x).1
    have := (tangent_linear _ hc.1 x).2
    have := (tangent_linear _ hc.2 x).1
    have := (tangent_linear _ hc.2 x).2
    constructor <;> simp_all
