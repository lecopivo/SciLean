import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.TangentSpace

namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ

variable
  {I : Type*}
  {E : I → Type*} {TE : outParam ((i : I) → E i → Type*)} [∀ i, Diffeology (E i)]
  [∀ i e, AddCommGroup (TE i e)] [∀ i e, Module ℝ (TE i e)] [∀ i, TangentSpace (E i) (TE i)]

open Diffeology in
instance : Diffeology ((i : I) → E i) where
  Plot n := (i : I) → Plot (E i) n
  plotEval p u := fun i => p i u
  plot_ext := by
    intro _ _ _ h; funext i; apply plot_ext; intro u
    have := congrFun (congrFun h u) i; simp_all
  plotComp p f hf := fun i => plotComp (p i) hf
  plotComp_eval := by intros; simp
  constPlot n xdx := fun i => constPlot n (xdx i)
  constPlot_eval := by intros; simp

open Diffeology

@[simp]
theorem pi_plot_eval (p : (i : I) → Plot (E i) n) :
  (show Plot ((i : I) → E i) n from p) = fun u i => p i u := by rfl


def tsPiMap' {n : ℕ} :
    ((i : I) → (x : E i) × ((Fin n → ℝ) →ₗ[ℝ] TE i x))
    ≃
    (p : (i : I) → E i) × ((Fin n → ℝ) →ₗ[ℝ] (i : I) →  TE i (p i)) where
  toFun := fun p => ⟨fun i => (p i).1, fun du =>ₗ[ℝ] fun i => (p i).2 du⟩
  invFun := fun ⟨p,dp⟩ => fun i => ⟨p i, fun du =>ₗ[ℝ] dp du i⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl


def tsPiMap :
    ((i : I) → (x : E i) × (TE i x))
    ≃
    (p : (i : I) → E i) × ((i : I) →  TE i (p i)) where
  toFun := fun p => ⟨fun i => (p i).1, fun i => (p i).2⟩
  invFun := fun ⟨p,dp⟩ => fun i => ⟨p i, dp i⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl


open TangentSpace


instance
    {I : Type*}
    {E : I → Type*} {TE : outParam ((i : I) → E i → Type*)} [∀ i, Diffeology (E i)]
    [∀ i e, AddCommGroup (TE i e)] [∀ i e, Module ℝ (TE i e)] [∀ i, TangentSpace (E i) (TE i)] :
    TangentSpace ((i : I) → E i) (fun f => (i : I) → TE i (f i)) where

  tangentMap p u := tsPiMap' fun i => tangentMap (p i) u
  tangentMap_const := by intros; simp[constPlot]; rfl
  tangentMap_fst := by intros; simp[tsPiMap']
  exp xdx := fun i => exp (tsPiMap.symm xdx i)
  exp_at_zero := by intros; funext i; simp[tsPiMap]
  tangentMap_exp_at_zero := by intros; simp[tsPiMap',duality,tsPiMap]; rfl
