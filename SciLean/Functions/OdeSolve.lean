import SciLean.Core

namespace SciLean

noncomputable
def odeSolve {X} [Vec X] (f : ℝ → X → X) (t : ℝ) (x₀ : X) : X := sorry

function_properties odeSolve {X} (f : ℝ → X → X) (t : ℝ) (x₀ : X) : X
argument t [Vec X] [IsSmooth f] [∀ s, IsSmooth (f s)]
  isSmooth  := sorry,
  diff_simp := dt * f t (odeSolve f t x₀) by sorry
argument t [Hilbert X] [IsSmooth f] [∀ s, IsSmooth (f s)]
  hasAdjDiff   := by constructor; infer_instance; simp; intro; infer_instance done,
  adjDiff_simp := ⟪dt', f t (odeSolve f t x₀)⟫ by simp[adjointDifferential,hold] done
 
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
    -- ∂ y s 1 = (f (t - s))†
    sorry
argument x₀ [Vec X] [IsSmooth f] [∀ s, IsSmooth (f s)]
  isSmooth   := sorry,
  diff_simp  := odeSolve (λ s => ∂ (f s) (odeSolve f s x₀)) t dx₀
    by sorry
argument x₀ [Hilbert X] [IsSmooth f] [inst : ∀ t, HasAdjDiff (f t)]
  hasAdjDiff   := by 
    have isf := λ t => (inst t).isSmooth
    have iaf := λ t => (inst t).hasAdjDiff
    constructor; infer_instance; simp; intro x₀; infer_instance,
  adjDiff_simp := odeSolve (λ s => ∂† (f (t - s)) (odeSolve f (t - s) x₀)) t dx₀' 
    by 
      have isf := λ t => (inst t).isSmooth
      have iaf := λ t => (inst t).hasAdjDiff
      simp at iaf
      admit
      -- simp[adjointDifferential] done


  
-- example [Hilbert X] (f : ℝ → X → X) (y : X) [IsSmooth f] [∀ t, HasAdjDiff (f t)] 
--   : ∇ (λ x₀ => ∥odeSolve f t x₀ - y∥²) = 0 := 
-- by 
--   simp; unfold hold; simp
