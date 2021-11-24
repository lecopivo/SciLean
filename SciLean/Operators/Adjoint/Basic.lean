import SciLean.Categories
import SciLean.Operators.Inverse
import SciLean.Operators.Sum
import SciLean.Simp

import Init.Classical

set_option synthInstance.maxHeartbeats 5000

open Function
namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [Hilbert X] [Hilbert Y] [Hilbert Z]

def adjoint_definition (f : X → Y) (h : IsLin f) (y : Y) 
    : ∃ (x' : X), ∀ x, ⟨x', x⟩ = ⟨y, (f x)⟩ := sorry

noncomputable
def adjoint (f : X → Y) (y : Y) : X :=
    match Classical.propDecidable (IsLin f) with
      | isTrue  h => Classical.choose (adjoint_definition f h y)
      | _ => (0 : X)

postfix:max "†" => adjoint

namespace Adjoint

  instance (f : X → Y) [IsLin f] : IsLin f† := sorry

  @[simp]
  theorem adjoint_of_adjoint (f : X → Y) [IsLin f] : f†† = f := sorry

  @[simp] 
  theorem adjoint_of_id
      : (λ x : X => x)† = id := sorry

  @[simp]
  theorem adjoint_of_const {n}
      : (λ (x : X) (i : Fin n) => x)† = sum := sorry

  @[simp]
  theorem adjoint_of_sum {n}
      : (sum)† = (λ (x : X) (i : Fin n) => x) := sorry

  @[simp]
  theorem adjoint_of_swap {n m}
      : (λ (f : Fin n → Fin m → Y) => (λ j i => f i j))† = λ f i j => f j i := sorry

  @[simp]
  theorem adjoint_of_parm {n} (f : X → Fin n → Y) (i : Fin n) [IsLin f]
      : (λ x => f x i)† = (λ y => f† (λ j => (kron i j)*y)) := sorry

  @[simp]
  theorem adjoint_of_arg {n} [NonZero n] 
      (f : Y → Fin n → Z) [IsLin f]
      (g1 : X → Y) [IsLin g1]
      (g2 : Fin n → Fin n) [IsInv g2]
      : (λ x i => f (g1 x) (g2 i))† = g1† ∘ f† ∘ (λ h => h ∘ g2⁻¹) := sorry

  @[simp] 
  theorem adjoint_of_comp (f : Y → Z) [IsLin f] (g : X → Y) [IsLin g] 
      : (λ x => f (g x))† = g† ∘ f† := sorry

  @[simp] 
  theorem adjoint_of_comp_parm {n} (f : β → Y → Z) [∀ b, IsLin (f b)] (g1 : Fin n → β) (g2 : X → Fin n → Y) [IsLin g2] 
      : (λ x i => (f (g1 i) (g2 x i)))† = g2† ∘ (λ z i => (f (g1 i))† (z i)) := sorry

  @[simp]
  theorem adjoint_of_comp_arg1 {n} [NonZero n] (g : Fin n → Fin n) [IsInv g]
      : (λ (f : Fin n → X) i => f (g i))† = (λ f => f ∘ g⁻¹) := sorry

  -- Unfortunatelly this theorem is dangerous and causes simp to loop indefinitely
  -- @[simp 1000000] 
  -- def adjoint_of_composition_arg (f : Y → β → Z) (b : β) [IsLin (λ y => f y b)] (g : X → Y) [IsLin g] 
  --     : (λ x => f (g x) b)† = g† ∘ (λ y => f y b)† := sorry

  @[simp]
  theorem adjoint_of_diag {Y1 Y2 : Type} [Hilbert Y1] [Hilbert Y2]
      (f : Y1 → Y2 → Z) (g1 : X → Y1) (g2 : X → Y2) 
      [IsLin (λ yy : Y1 × Y2 => f yy.1 yy.2)] [IsLin g1] [IsLin g2]
      : (λ x => f (g1 x) (g2 x))† = (uncurry HAdd.hAdd) ∘ (pmap g1† g2†) ∘ (uncurry f)† := sorry

  @[simp]
  theorem adjoint_of_diag_arg {Y1 Y2 : Type} [Hilbert Y1] [Hilbert Y2]
      (f : Y1 → Y2 → Z) (g1 : X → Fin n → Y1) (g2 : X → Fin n → Y2)
      [IsLin (λ yy : Y1 × Y2 => f yy.1 yy.2)] [IsLin g1] [IsLin g2]
      : (λ x i => f (g1 x i) (g2 x i))† = (uncurry HAdd.hAdd) ∘ (pmap g1† g2†) ∘ (λ f => (λ i => (f i).1, λ i => (f i).2)) ∘ (comp (uncurry f)†) := sorry


end Adjoint
