import SciLean.Basic
import SciLean.Tactic

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Hilbert X] [Hilbert Y] [Hilbert Z]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ]

example (y z : X) [Hilbert X] 
  : 
    ∇ (λ x : X => ⟪x,y⟫) z = y 
  := by autograd done

example (y : X) [Hilbert X] 
  : 
    ∇ (λ x : X => ⟪x,x⟫) y = (2 : ℝ) * y 
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


def norm {X} [Hilbert X] (x : X) := Math.sqrt ⟪x, x⟫

notation "∥" x "∥" => norm x

-- TODO: Move this somewhere else
instance {X} [Hilbert X] : IsSmooth (λ x : X => ∥x∥^2) := sorry
@[simp] theorem differential_of_squared_norm {X} [Hilbert X] 
  : δ (λ x : X => ∥x∥^2) = λ x dx : X => 2*⟪x, dx⟫ := sorry

example {X} [Hilbert X] (x : X) 
  : 
    ∇ (λ x : X => ∥x∥^2) x = (2 : ℝ) * x 
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
