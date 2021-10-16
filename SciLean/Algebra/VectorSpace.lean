import SciLean.Algebra.Real


-- __   __      _             ___
-- \ \ / /__ __| |_ ___ _ _  / __|_ __  __ _ __ ___
--  \ V / -_) _|  _/ _ \ '_| \__ \ '_ \/ _` / _/ -_)
--   \_/\___\__|\__\___/_|   |___/ .__/\__,_\__\___|
--                               |_|
-- At the and we will use Convenient Vector Space. It is a special kind of topological vector space

class Vec (U : Type u) extends Add U, Sub U, HMul ℝ U U, Neg U, Zero U :=
  (add_assoc : ∀ x y z : U, (x + y) + z = x + (y + z))
  (add_comm : ∀ x y : U, x + y = y + x)
  (add_zero : ∀ x : U, x + 0 = x)
  (zero_add : ∀ x : U, 0 + x = x)
  --- TODO: write down proper definition

section CommonVectorSpaces

  variable {α β : Type u}
  variable {U V} [Vec U] [Vec V]

  instance : HMul ℝ PUnit PUnit := ⟨λ x y => PUnit.unit⟩
  instance : Vec PUnit :=
  {
    add_assoc := sorry,
    add_comm := sorry,
    add_zero := sorry,
    zero_add := sorry
  }

  instance : Vec ℝ :=
  {
    add_assoc := sorry,
    add_comm := sorry,
    add_zero := sorry,
    zero_add := sorry
  }

  instance : Vec (α → U) :=   {
    add_assoc := sorry,
    add_comm := sorry,
    add_zero := sorry,
    zero_add := sorry
  }

  instance : Vec (U × V) :=   {
    add_assoc := sorry,
    add_comm := sorry,
    add_zero := sorry,
    zero_add := sorry
  }

end CommonVectorSpaces


