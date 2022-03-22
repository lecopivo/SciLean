import SciLean.Operators.Calculus.Differential
import SciLean.Operators.Adjoint

namespace SciLean.ReverseDiff

variable {α β γ α' β': Type}
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {U V W : Type} [SemiHilbert U] [SemiHilbert V] [SemiHilbert W]

@[simp] 
theorem reverse_diff_of_comp 
        (f : V → W) (g : U → V) 
        [IsSmooth g] [IsSmooth f]
    : 𝓑 (λ x => f (g x)) = (λ x => (𝓑 f • 𝓑 g) x) := 
by 
  funext x; simp[reverse_diff, reverse_diff, reverse_comp]
  funext dz; simp
  done

@[simp] 
theorem reverse_diff_of_function_comp
        (f : V → W) (g : U → V) 
        [IsSmooth g] [IsSmooth f] 
        : 𝓑 (f ∘ g) = (𝓑 f • 𝓑 g) := 
by
  simp[Function.comp] done

@[simp]
theorem reverse_diff_of_linear 
        (f : U → V) [IsLin f]
        (x : U)
        : 𝓑 f x = (f x, f†) := 
by 
  simp[reverse_diff] done
