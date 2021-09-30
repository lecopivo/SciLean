

class IsInv {X Y} (f : X → Y) := 
  (inj : ∀ x y, f x = f y → x = y)
  (surj : ∀ y, ∃ x, f x = y)

def inverse {U V} : (U → V) → (V → U) := sorry
def inverse_definition {U V} (f : U → V) (u : U) (v : V) [IsInv f] : f u = v → inverse f v = u := sorry

@[simp] def inverse_inverse {U V} (f : U → V) (u : U) [IsInv f] : inverse f (f u) = u := sorry
@[simp] def inverse_inverse_2 {U V} (f : U → V) (v : V) [IsInv f] : f (inverse f v) = v := sorry

def add.inverse [Add α] [Neg α] : inverse (HAdd.hAdd a : α → α) = HAdd.hAdd (-a) := sorry
