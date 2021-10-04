import SciLean.Prelude
import SciLean.Meta

def LinearMap (X Y : Type) [Vec X] [Vec Y] : Type := { f : X → Y // IsLin f }
def LinearMap.mk {X Y} [Vec X] [Vec Y] (f : X → Y) [IsLin f] : LinearMap X Y := ⟨f, by infer_instance⟩

infixr:50 "⇀" => LinearMap

instance {X Y} [Vec X] [Vec Y] : CoeFun (X ⇀ Y) (λ _ => X → Y) := ⟨Subtype.val⟩

-- instance {X Y} [Vec X] [Vec Y] : Vec (X ⇀ Y) := sorry

-- instance {X Y} [Vec X] [Vec Y] : IsLin (@CoeFun.coe (X ⇀ Y) _ _) := sorry




namespace Linear
  variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

  -- def id := λₗ (x : X) => x
  -- def comp := λₗ (f : Y ⇀ Z) (g : X ⇀ Y) (x : X) => A (B x) 

-- Does not work :(
-- macro "λₗ" xs:Lean.explicitBinders "=> " b:term : term => Lean.expandExplicitBinders `LinearMap.make xs b

end Linear
