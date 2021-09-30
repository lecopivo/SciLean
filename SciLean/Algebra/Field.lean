import SciLean.Algebra.Basic

class Field (F : Type u) extends Add F, Sub F, Mul F, Div F, Neg F, One F, Zero F :=
  (add_assoc : ∀ x y z : F, (x + y) + z = x + (y + z))
  (add_comm : ∀ x y : F, x + y = y + x)
  (add_zero : ∀ x : F, x + 0 = x)
  (zero_add : ∀ x : F, 0 + x = x)

  (mul_assoc : ∀ x y z : F, (x * y) * z = x * (y * z))
  (mul_comm : ∀ x y : F, x * y = y * x)
  (mul_one : ∀ x : F, x * 1 = x)
  (one_mul : ∀ x : F, 1 * x = x)
  --- ...

attribute [simp] Field.add_zero Field.zero_add Field.one_mul Field.mul_one 

