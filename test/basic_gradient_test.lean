import SciLean.Basic
import SciLean.Tactic

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Hilbert X] [Hilbert Y] [Hilbert Z]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ]

-- set_option trace.Meta.Tactic.simp.rewrite true in
example (y : X)
  : 
    ∇ (λ x : X => 2 * ⟪x,x⟫) = λ x : X => (2 : ℝ) * ((2 : ℝ) * x)
  := by autograd done

example (g : ι → ℝ) 
  : 
    ∇ (λ (f : ι → ℝ) => ∑ i, f i) g 
    = 
    (λ _ => (1 : ℝ)) 
  := by autograd done

set_option synthInstance.maxHeartbeats 5000

example {n} (g : Fin n → ℝ) [NonZero n]
  : 
    ∇ (λ (f : Fin n → ℝ) => ∑ i, (f (i + 1))*(f i)) g 
    = 
    (λ i => g (i - 1) + g (i + 1)) 
  := 
by 
  autograd done


example {X} [Hilbert X] (x : X) 
  : 
    ∇ (λ x : X => ∥x∥²) x = (2 : ℝ) * x 
  := 
by autograd done

example {n} (g : Fin n → ℝ) [NonZero n]
  : 
    ∇ (λ (f : Fin n → ℝ) => ∑ i, ⟪(f (i + 1) - f i), (f (i + 1) - f i)⟫) g 
    = 
    (λ i => (2 : ℝ) * (g (i - 1 + 1) - g (i - 1) - (g (i + 1) - g i))) 
  := 
by 
  autograd; funext i; simp; done

-- set_option synthInstance.maxHeartbeats 1000
-- example (g : ι → ℝ) 
--   : 
--     ∇ (λ (f : ι → ℝ) => ∑ i, (42 : ℝ) * f i) g 
--     = 
--     (λ _ => (42 : ℝ)) 
--   := by autograd done

-- example (g : ι → ℝ) 
--   : 
--     ∇ (λ (f : ι → ℝ) => ∑ i, (f i)*(f i)) g = (2 : ℝ) * g 
--   := 
-- by autograd; done


  --   example : δ (λ x => ∑ i, x[i]) x dx = ∑ i, dx[i] := by simp done
  --   example : δ (λ x => ∑ i, 2*x[i]) x dx = ∑ i, 2*dx[i] := by simp done
  --   example : δ (λ x => (∑ i, x[i]*x[i])) x dx = ∑ i, dx[i]*x[i] + x[i]*dx[i] := by autodiff done
  --   example : ∇ (λ x => ∑ i, x[i]) x = lmk (λ i => 1) := by autograd done
  --   example : ∇ (λ x => ∑ i, x[i]*x[i]) x = (2:ℝ)*x := by autograd done

  --   example : ∇ (λ x => ∑ i, x[i]*x[i-a]) x = ((lmk λ i => x[i-a]) + (lmk λ i => x[i+a])) := by autograd done
  --   -- example : ∇ (λ x => ∑ i, (x[i+a] - x[i])*(x[i+a] - x[i])) x = 0 := by autograd done -- Needs some more sophisticated simplifications

    -- variable {n : Nat} [NonZero n] (a : Fin n)

    -- example : ∇ (λ (f : Fin n → ℝ) => ∑ i, (f (i+a) - f i)*(f (i+a) - f i)) 
    --           = 
    --           (λ (f : Fin n → ℝ) i => 2 * (f (i - a + a) - f (i - a) - (f (i + a) - f i))) := by autograd done
  --   example (c : ℝ) : ∇ (λ (f : Fin n → ℝ) => ∑ i, c*(f i)*(f i)) = (λ (f : Fin n → ℝ) => (2:ℝ)*c*f) := by autograd done
