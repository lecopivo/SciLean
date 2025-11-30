import Lean
import SciLean.Util.SorryProof

namespace SciLean

/-- 
  `FunPropT` is a transitive closure of a function property.
  
  This is inspired by `CoeT` or `MonadLiftT`. The idea is that we have a user-facing 
  typeclass like `IsSmooth` that you provide instances for, but when you actually use it, 
  you want to infer its transitive closure `IsSmoothT`.

  The advantage is that we can provide instances that derive `IsSmooth` from `IsLin` 
  that can fail quickly. For example, when deriving smoothness of `f ∘ g`, you don't 
  want to try composition of smooth functions **and** composition of linear functions. 
  You want to apply the composition theorem only once! Deriving smoothness from linearity 
  should work only for atomic functions.
-/
class FunPropT (P : (α → β) → Prop) (f : α → β) : Prop

/-- Base case: if a function has property P, then it has the transitive closure of P -/
instance (priority := 100) funPropT_of_funProp {P : (α → β) → Prop} {f : α → β} (h : P f) : FunPropT P f :=
  sorry_proof

/-- Composition case: if f and g have the transitive closure of P, then so does f ∘ g -/
instance (priority := 90) funPropT_comp {P : (α → β) → Prop} {Q : (β → γ) → Prop} {R : (α → γ) → Prop}
    {f : β → γ} {g : α → β} 
    (h₁ : FunPropT P g) (h₂ : FunPropT Q f) 
    (h₃ : ∀ {f g}, P g → Q f → R (f ∘ g)) : 
    FunPropT R (f ∘ g) :=
  sorry_proof

-- Simple example to test with #eval
def exampleProp (f : Nat → Nat) : Prop := ∀ n, f n ≥ n

instance : FunPropT exampleProp (fun n => n + 1) := funPropT_of_funProp (fun n => Nat.le_add_right n 1)

#eval "TransitiveClosure module loaded successfully"

end SciLean
