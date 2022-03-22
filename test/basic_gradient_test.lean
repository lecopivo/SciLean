import SciLean.Basic
import SciLean.Tactic

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Hilbert X] [Hilbert Y] [Hilbert Z]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ]

variable {n : Nat} [NonZero n]

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

set_option synthInstance.maxHeartbeats 400 in
set_option maxHeartbeats 8000 in
example 
  : ∇ (λ (f : Fin n → ℝ) => ∑ i, (f (i + 1))*(f i))
    = 
    (λ (f : Fin n → ℝ) i => f (i - 1) + f (i + 1)) 
  := 
by 
  autograd done

set_option synthInstance.maxHeartbeats 700 in
set_option maxHeartbeats 11000 in
example 
  : ∇ (λ (f : ℝ^n) => ∑ i, f[i + 1]*f[i])
    = 
    λ (f : ℝ^n) => PowType.intro λ i => f[i - 1] + f[i + 1]
  := 
by 
  autograd done


example {X} [Hilbert X] (x : X) 
  : 
    ∇ (λ x : X => ∥x∥²) x = (2 : ℝ) * x 
  := 
by autograd done

-- set_option synthInstance.maxHeartbeats 1000 in
example (g : Fin n → ℝ)
  : 
    ∇ (λ (f : Fin n → ℝ) => ∑ i, ⟪(f (i + 1) - f i), (f (i + 1) - f i)⟫) g 
    = 
    (λ i => (2 : ℝ) * (g (i - 1 + 1) - g (i - 1) - (g (i + 1) - g i))) 
  := 
by
  autograd done


-- Too slow with `x : (ℝ^(3:ℕ))^n
example (l : Fin n → ℝ)
  : ∇ (λ (x : Fin n → Fin 3 → ℝ) => ∑ i, ∥ ∥x i  - x (i-1)∥² - (l i)^2∥²)
    =
    (fun (x : Fin n → Fin 3 → ℝ) =>
      (2:ℝ) * fun j =>
        (∥x j - x (j - 1)∥² - l j ^ 2) * ((2:ℝ) * (x j - x (j - 1))) -
        (∥x (j + 1) - x (j + 1 - 1)∥² - l (j + 1) ^ 2) * ((2:ℝ) * (x (j + 1) - x (j + 1 - 1))))
  := by autograd done


-- set_option trace.Meta.Tactic.simp.rewrite true in
set_option synthInstance.maxSize 256 in
example
  : ∇ (λ x : Fin n → Fin 3 → ℝ => ∑ i j, ∥x i - x j∥²)
    = 
    0
   -- (fun x => (2:ℝ) * ((fun j => (n:ℝ) * x j - fun j => sum fun i => x i j) - fun j => (fun j => sum fun i => x i j) - (n:ℝ) * x j))
 := by
   autograd
   -- I was unable to typecheck the rhs, so we are just checking if `autograd` terminates on this
   admit

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


example : δ (λ x : ℝ^n => ∑ i, x[i]) = λ x dx => ∑ i, dx[i] := by simp done
example : δ (λ x : ℝ^n => ∑ i, 2*x[i]) = λ x dx => ∑ i, (2:ℝ)*dx[i] := by simp done
example : δ (λ x : ℝ^n => (∑ i, x[i]*x[i])) = λ x dx => (∑ i, dx[i]*x[i]) + (∑ i, x[i]*dx[i]) := by simp done
example : ∇ (λ x : ℝ^n => ∑ i, x[i]) = λ x => PowType.intro (λ i => (1:ℝ)) := by autograd done
example : ∇ (λ x : ℝ^n => ∑ i, x[i]*x[i]) = λ x : ℝ^n => (2:ℝ)*x := by autograd admit -- not quite there, not sure what to do about this case

  --   example : ∇ (λ x => ∑ i, x[i]*x[i-a]) x = ((lmk λ i => x[i-a]) + (lmk λ i => x[i+a])) := by autograd done
  --   -- example : ∇ (λ x => ∑ i, (x[i+a] - x[i])*(x[i+a] - x[i])) x = 0 := by autograd done -- Needs some more sophisticated simplifications

    -- variable {n : Nat} [NonZero n] (a : Fin n)

    -- example : ∇ (λ (f : Fin n → ℝ) => ∑ i, (f (i+a) - f i)*(f (i+a) - f i)) 
    --           = 
    --           (λ (f : Fin n → ℝ) i => 2 * (f (i - a + a) - f (i - a) - (f (i + a) - f i))) := by autograd done
  --   example (c : ℝ) : ∇ (λ (f : Fin n → ℝ) => ∑ i, c*(f i)*(f i)) = (λ (f : Fin n → ℝ) => (2:ℝ)*c*f) := by autograd done
