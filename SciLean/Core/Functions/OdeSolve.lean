import SciLean.Core.Diff
import SciLean.Core.Adjoint
import SciLean.Core.AdjDiff
import SciLean.Core.Inv

import SciLean.Core.Functions.Prod
import SciLean.Core.Functions.Operations

namespace SciLean


constant odeSolve {X} [Vec X] (f : ℝ → X → X) (t : ℝ) (x₀ : X) : X


--- Duhhh  move this somewhere ... 
instance {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] : IsSmooth (δ f) := sorry
instance {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] (x : X) : IsLin (δ f x) := sorry
instance {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] (x : X) : IsSmooth (δ f x) := sorry
instance {X Y₁ Y₂ Z} [Vec X] [Vec Y₁] [Vec Y₂] [Vec Z] (f : Y₁ → Y₂ → Z) (g₁ : X → Y₁) (g₂ : X → Y₂) [IsSmooth f] [∀ y₁, IsSmooth (f y₁)] [IsSmooth g₁] [IsSmooth g₂] 
  : IsSmooth (λ x => δ (f (g₁ x)) (g₂ x)) := by sorry

function_properties odeSolve {X} (f : ℝ → X → X) (t : ℝ) (x₀ : X) : X
argument t [Vec X] [IsSmooth f] [∀ s, IsSmooth (f s)]
  isSmooth  := sorry,
  diff_simp := dt * f t (odeSolve f t x₀) by sorry
argument t [Hilbert X] [IsSmooth f] [∀ s, IsSmooth (f s)]
  hasAdjDiff   := by constructor; infer_instance; simp; intro; infer_instance done,
  adjDiff_simp := ⟪dt', f t (odeSolve f t x₀)⟫ by simp[adjDiff] done
 
argument x₀ [Vec X] [IsSmooth f] [∀ s, IsLin (f s)]
  isLin   := sorry
argument x₀ [Hilbert X] [IsSmooth f] [∀ s, HasAdjoint (f s)]
  hasAdjoint := sorry,
  adj_simp   := odeSolve (λ s => (f (t - s))†) t x₀' 
  by 
    -- Define adjoint solution `y such that
    --  ∀ s, ⟪x (t - s), y s⟫ = ⟪x t, y 0⟫ 
    -- in particular for s := t we get desired ⟪x 0, y t⟫ = ⟪x t, y 0⟫
    -- Differentiate above equation w.r.t to `s and you get that `y satisfies
    -- δ y s 1 = (f (t - s))†
    sorry
argument x₀ [Vec X] [IsSmooth f] [∀ s, IsSmooth (f s)]
  isSmooth   := sorry,
  diff_simp  := odeSolve (λ s => δ (f s) (odeSolve f s x₀)) t dx₀
    by sorry
argument x₀ [Hilbert X] [IsSmooth f] [inst : ∀ t, HasAdjDiff (f t)]
  hasAdjDiff   := by 
    have isf := λ t => (inst t).isSmooth
    have iaf := λ t => (inst t).hasAdjDiff
    constructor; infer_instance; simp; intro x₀; infer_instance,
  adjDiff_simp := odeSolve (λ s => δ† (f (t - s)) (odeSolve f (t - s) x₀)) t dx₀' 
    by 
      have isf := λ t => (inst t).isSmooth
      have iaf := λ t => (inst t).hasAdjDiff
      simp at iaf
      simp[adjDiff] done


  
-- example [Hilbert X] (f : ℝ → X → X) (y : X) [IsSmooth f] [∀ t, HasAdjDiff (f t)] 
--   : ∇ (λ x₀ => ∥odeSolve f t x₀ - y∥²) = 0 := 
-- by 
--   simp; unfold hold; simp
