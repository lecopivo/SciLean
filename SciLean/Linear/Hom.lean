import SciLean.Prelude
import SciLean.Linear.Combinators
import SciLean.Tactic

def LinearMap (X Y : Type) [Vec X] [Vec Y] : Type := { f : X → Y // IsLin f }
def LinearMap.mk {X Y} [Vec X] [Vec Y] (f : X → Y) [IsLin f] : LinearMap X Y := ⟨f, by infer_instance⟩

infixr:25 "⊸" => LinearMap

instance {X Y} [Vec X] [Vec Y] : CoeFun (X ⊸ Y) (λ _ => X → Y) := ⟨λ f => f.1⟩
instance {X Y} [Vec X] [Vec Y] (f : X ⊸ Y) : IsLin (f : X → Y) := sorry

instance {X Y} [Vec X] [Vec Y] : Vec (X ⊸ Y) := sorry  -- Define operations! proofs can be sorry
instance {X Y} [Vec X] [Vec Y] : IsLin (CoeFun.coe : (X ⊸ Y) → (X → Y)) := sorry

namespace Lin
  variable {α β γ : Type}
  variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

  def id : X ⊸ X := ⟨λ x => x, by rmlamlet; infer_instance⟩
  def const (β : Type) : X ⊸ β → X := ⟨λ x b => x, by rmlamlet; infer_instance⟩
  def swap1 : (X ⊸ β → Z) ⊸ (β → X ⊸ Z) := sorry
  def swap2 : (α → Y ⊸ Z) ⊸ (Y ⊸ α → Z) := sorry
  def swap  : (X ⊸ Y ⊸ Z) ⊸ (Y ⊸ X ⊸ Z) := sorry
  def comp : (Y ⊸ Z) ⊸ (X ⊸ Y) ⊸ (X ⊸ Z) := ⟨λ f => ⟨λ g => ⟨λ x => f (g x), by rmlamlet; infer_instance⟩, sorry⟩, sorry⟩

  -- The only form of `diag` that is possible
  -- def tensor : (X ⊸ X ⊸ Y) ⊸ (X ⊗ X ⊸ Y) := sorry

-- Does not work :(
-- macro "λₗ" xs:Lean.explicitBinders "=> " b:term : term => Lean.expandExplicitBinders `LinearMap.make xs b

  -- syntax "λₗ" Lean.explicitBinders " => " term : term 
  syntax binder := " ( " term " : " term " ) "
  syntax "λ" binder+ "⊸" term : term 
  -- syntax "λ" Lean.explicitBinders " -o " term : term 

  macro_rules
    | `(λ ($x : $X) ⊸ $b) => `((⟨λ ($x : $X) => $b, by rmlamlet; infer_instance⟩ : LinearMap _ _)) 
    | `(λ ($x : $X) $xs ⊸ $b) => `((⟨λ ($x : $X) => (λ $xs ⊸ $b), by rmlamlet; infer_instance⟩ : LinearMap _ _)) 

  variable {X : Type} [Vec X]

  #check (λ (x : X) ⊸ (3:ℝ)*x + x)
  #check (λ (x : X) (x : X) ⊸ (0 : X))

end Lin
