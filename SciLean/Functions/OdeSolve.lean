import SciLean.Core

namespace SciLean

-- TODO: Add Semi Group property for `f` that guarantees the existence
--       of solution for all times

noncomputable
def odeSolve {X} [Vec X] (f : ℝ → X → X) (t : ℝ) (x₀ : X) : X := sorry

function_properties odeSolve {X} (f : ℝ → X → X) (t : ℝ) (x₀ : X) : X
argument t [Vec X] [IsSmooth f] [∀ s, IsSmooth (f s)]
  isSmooth  := sorry_proof,
  diff_simp := dt * f t (odeSolve f t x₀) by sorry_proof
argument t [Hilbert X] [IsSmooth f] [∀ s, IsSmooth (f s)]
  hasAdjDiff   := by constructor; infer_instance; simp; intro; infer_instance done,
  adjDiff_simp := ⟪dt', f t (odeSolve f t x₀)⟫ by simp[adjointDifferential,hold] done
 
argument x₀ [Vec X] [IsSmooth f] [∀ s, IsLin (f s)]
  isLin   := sorry_proof
argument x₀ [Hilbert X] [IsSmooth f] [∀ s, HasAdjoint (f s)]
  hasAdjoint := sorry_proof,
  adj_simp   := odeSolve (λ s => (f (t - s))†) t x₀' 
  by 
    -- Define adjoint solution `y such that
    --  ∀ s, ⟪x (t - s), y s⟫ = ⟪x t, y 0⟫
    -- in particular for s := t we get desired ⟪x 0, y t⟫ = ⟪x t, y 0⟫
    -- Differentiate above equation w.r.t to `s and you get that `y satisfies
    -- ∂ y s 1 = (f (t - s))†
    sorry_proof
argument x₀ [Vec X] [IsSmooth f] [∀ s, IsSmooth (f s)]
  isSmooth   := sorry_proof,
  diff_simp  := odeSolve (λ s => ∂ (f s) (odeSolve f s x₀)) t dx₀
    by sorry_proof
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
      simp[adjointDifferential]
      done


instance odeSolve.arg_f.isSmooth {X W} [Vec X] [Vec W] 
  (f : W → ℝ → X → X) [IsSmooth f] [∀ w, IsSmooth (f w)] [∀ w t, IsSmooth (f w t)]
  : IsSmooth (λ w => odeSolve (f w)) := sorry_proof

@[simp]
theorem odeSolve.arg_f.diff_simp {X W} [Vec X] [Vec W] 
  (f : W → ℝ → X → X) [IsSmooth f] [∀ w, IsSmooth (f w)] [∀ w t, IsSmooth (f w t)]
  : ∂ (λ w => odeSolve (f w))
    =
    λ w dw t x => (odeSolve (λ t (x,dx) => (f w t x, ∂ f w dw t x + ∂ (f w t) x dx)) t (x,0)).1
  := sorry_proof

theorem odeSolve.arg_f.diff_simp_alt {X W} [Vec X] [Vec W] 
  (f : W → ℝ → X → X) [IsSmooth f] [∀ w, IsSmooth (f w)] [∀ w t, IsSmooth (f w t)]
  : ∂ (λ w => odeSolve (f w))
    =
    λ w dw t x₀ => 
      let x := λ t => odeSolve (f w) t x₀
      (odeSolve (λ t dx => ∂ f w dw t (x t) + ∂ (f w t) (x t) dx) t 0)
  := sorry_proof

-- @[simp]
-- theorem odeSolve.arg_f.adj_simp {X W} [SemiHilbert X] [SemiHilbert W] 
--   (f : W → ℝ → X → X) [IsSmooth f] [∀ w, IsSmooth (f w)] [∀ w t, IsSmooth (f w t)] (x₀ : X)
--   : (λ w => odeSolve (f w) t x₀)†
--     =
--     λ x' => sorry
--   := sorry_proof

-- @[simp]
-- theorem odeSolve.arg_f.adjDiff_simp {X W} [SemiHilbert X] [SemiHilbert W] 
--   (f : W → ℝ → X → X) [IsSmooth f] [∀ w, IsSmooth (f w)] [∀ w t, IsSmooth (f w t)] (x₀ : X)
--   : ∂† (λ w => odeSolve (f w) t x₀)
--     =
--     λ w dw' => 
--       sorry := 
--   by
--     simp only [adjointDifferential]
--     simp [odeSolve.arg_f.diff_simp_alt]
    
-- example [Hilbert X] (f : ℝ → X → X) (y : X) [IsSmooth f] [∀ t, HasAdjDiff (f t)] 
--   : ∇ (λ x₀ => ∥odeSolve f t x₀ - y∥²) = 0 := 
-- by 
--   simp[gradient]; unfold hold; simp
