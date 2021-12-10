import SciLean.Categories.Zero
import SciLean.Categories.Inv.Core

open Function
namespace SciLean.Inv

variable {α β γ : Type} 
variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]
variable {U V W : Type} [Hilbert U] [Hilbert V] [Hilbert W] 

--- Arithmetic operations
--- We have specialized instances for Fin because we do not use Mathlib and do not have a definition of a Group in SciLean
instance {X} [Vec X] (y : X) : IsInv (λ x => x + y) := sorry
instance {n} (y : Fin n) : IsInv (λ x => x + y) := sorry
instance {X} [Vec X] (x : X) : IsInv (λ y => x + y) := sorry
instance {n} (x : Fin n) : IsInv (λ y => x + y) := sorry

instance {X} [Vec X] (y : X) : IsInv (λ x => x - y) := sorry
instance (y : Fin n) : IsInv (λ x => x - y) := sorry
instance {X} [Vec X] (x : X) : IsInv (λ y => x - y) := sorry
instance (x : Fin n) : IsInv (λ y => x - y) := sorry

instance (s : ℝ) [NonZero s] : IsInv (λ (r : ℝ)  => r*s) := sorry

instance {X} [Vec X] (r : ℝ) [NonZero r] : IsInv (λ (x : X)  => r*x) := sorry

instance {X} [Vec X] : IsInv (λ (x : X) => -x) := sorry
