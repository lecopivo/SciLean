import SciLean.Operators.Adjoint.Basic

open Function
namespace SciLean

open SemiInner

variable {α β γ : Type}
variable {X Y Z : Type} {R D e}
variable [Vec R] [SemiHilbert X R D e] [SemiHilbert Y R D e] [SemiHilbert Z R D e]

namespace SciLean.Adjoint

  @[simp] 
  theorem adjoint_of_function_id 
          : adjoint (id : X → X) = id := sorry

  @[simp] 
  theorem adjoint_of_function_comp (f : Y → Z) [HasAdjoint f] (g : X → Y) [HasAdjoint g] 
          : adjoint (f∘g) = adjoint g ∘ adjoint f := sorry

  @[simp]
  theorem adjoint_of_function_comp_arg_1 {n} [NonZero n]
      (g : Fin n → Fin n) [IsInv g]
      : adjoint (λ (f : Fin n → X) => f ∘ g) = (λ f => f ∘ g⁻¹) := sorry

  @[simp]
  theorem adjoint_of_uncurry (f : X → Y → Z) [IsLin (λ xy : X × Y => f xy.1 xy.2)]
          : adjoint (uncurry f) = adjoint (λ xy : X × Y => f xy.1 xy.2) := rfl
