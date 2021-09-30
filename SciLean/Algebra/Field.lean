import SciLean.Basic

class Field (F : Type u) extends Add F, Sub F, Mul F, Div F, Neg F, Inv F, One F, Zero F :=
  (add_assoc : ∀ x y z : F, (x + y) + z = x + (y + z))
  (add_comm : ∀ x y : F, x + y = y + x)
  (add_zero : ∀ x : F, x + 0 = x)
  (zero_add : ∀ x : F, 0 + x = x)

  (mul_assoc : ∀ x y z : F, (x * y) * z = x * (y * z))
  (mul_comm : ∀ x y : F, x * y = y * x)
  (mul_one : ∀ x, x * 1 = x)
  (one_mul : ∀ x, 1 * x = x)
