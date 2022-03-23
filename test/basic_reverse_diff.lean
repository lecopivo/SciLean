import SciLean.Basic
import SciLean.Tactic

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Hilbert X] [Hilbert Y] [Hilbert Z]
variable {ι κ : Type} [Enumtype ι] [Enumtype κ]

variable {n : Nat} [NonZero n]

-- set_option trace.Meta.Tactic.simp true in
example
  : 𝓑 (λ x : Fin n → Fin 3 → ℝ => ∑ i j, ∥x i - x j∥²)
    = 
    0 := 
by
  simp
  simp
  admit


instance (x y : X) : HasAdjoint λ dx => δ (λ x y : X => x - y) x dx y := 
by 
  simp infer_instance done

instance (x y : X) : HasAdjoint λ dy => δ (λ y : X => x - y) y dy := 
by 
  rw[Smooth.differential_of_uncurried_linear_2 HSub.hSub]; simp
  infer_instance done


variable (f : (α → (β×(β→α))))

@[simp]
theorem reverse_comp_id {α β : Type} (f : (α → (β×(β→α)))) 
  : f • (λ x => (x, λ dx => dx)) = f := 
by     
  funext x; simp[reverse_comp]
  conv => lhs; enter [2,x]; simp
  done

@[simp]
theorem reverse_id_comp {α β : Type} (f : (α → (β×(β→α)))) 
  : (λ x => (x, λ dx => dx)) • f = f :=
by     
  funext x; simp[reverse_comp]
  conv => lhs; enter [2,x]; simp
  done

example (i j : Fin n) 
  : (𝓑 fun (x : Fin n → X) => x i - x j) = 0 :=
by
  simp
  simp[reverse_diff, Function.uncurry]
  admit


-- These collect what needs to be defined for atomic functions

