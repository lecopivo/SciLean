import SciLean.Operators.Adjoint.Basic

open Function
namespace SciLean

open SemiInner

variable {α β γ : Type}
variable {X Y Z S : Type} 
variable [Signature S] [Vec S]
variable [SemiHilbert X S] [SemiHilbert Y S] [SemiHilbert Z S]

namespace SciLean.Adjoint

  @[simp] 
  theorem adjoint_of_function_id 
          : (id : X → X)† = id := sorry

  @[simp] 
  theorem adjoint_of_function_comp (f : Y → Z) [IsLin f] (g : X → Y) [IsLin g] 
          : (f∘g)† = g† ∘ f† := sorry

  @[simp]
  theorem adjoint_of_function_comp_arg_1 {n} [NonZero n]
      (g : Fin n → Fin n) [IsInv g]
      : (λ (f : Fin n → X) => f ∘ g)† = (λ f => f ∘ g⁻¹) := sorry

  @[simp]
  theorem adjoint_of_uncurry (f : X → Y → Z) [IsLin (λ xy : X × Y => f xy.1 xy.2)]
          : (uncurry f)† = (λ xy : X × Y => f xy.1 xy.2)† := rfl
