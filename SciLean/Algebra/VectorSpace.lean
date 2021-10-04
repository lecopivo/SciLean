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


--  _  _ _ _ _             _     ___
-- | || (_) | |__  ___ _ _| |_  / __|_ __  __ _ __ ___
-- | __ | | | '_ \/ -_) '_|  _| \__ \ '_ \/ _` / _/ -_)
-- |_||_|_|_|_.__/\___|_|  \__| |___/ .__/\__,_\__\___|
--                                  |_|

class Inner (α : Type u) where
  (inner : α → α → ℝ)

macro "⟨" t:term "," s:term "⟩" : term => `(Inner.inner $t $s)
macro "∥" t:term "∥" : term => `(Real.sqrt ⟨$t, $t⟩)

class Hilbert (U : Type u) extends Inner U, Vec U :=
  (inner_symm : ∀ x y : U, ⟨x, y⟩ = ⟨y, x⟩)
  (inner_pos  : ∀ x : U, x ≠ 0 → ⟨x, x⟩ > (0 : ℝ))
  (inner_add : ∀ x y z : U, ⟨x + y, z⟩ = ⟨x, z⟩ + ⟨y, z⟩)
  (inner_mul : ∀ (x y: U) (r : ℝ), ⟨r * x, y⟩ = r * ⟨x, y⟩)
  -- TODO: is this enough?
  
section Hilbert

variable {U} [Hilbert U]

def inner (u v : U) := ⟨u, v⟩
def inner.ext (u v : U) : (∀ w, ⟨u, w⟩ = ⟨v, w⟩) → (u = v) := sorry

def inner.add (u v w : U)  : ⟨u + v, w⟩ = ⟨u, w⟩ + ⟨v, w⟩ := sorry
def inner.mul (u v : U) (c : ℝ)  : ⟨c * u, v⟩ = c * ⟨u, v⟩ := sorry
def inner.sym (u v : U)  : ⟨u, v⟩ = ⟨v, u⟩ := sorry

end Hilbert

section CommonHilbertSpaces

  instance : Inner ℝ := ⟨λ x y => x*y⟩
  instance : Hilbert ℝ := 
  {
    inner_symm := sorry,
    inner_pos := sorry,
    inner_add := sorry,
    inner_mul := sorry
  } 

  instance : Inner PUnit := ⟨λ x y => 0⟩
  instance : Hilbert PUnit := 
  {
    inner_symm := sorry,
    inner_pos := sorry,
    inner_add := sorry,
    inner_mul := sorry
  } 


  -- @[simp] def inner_on_reals (x y : ℝ) : ⟨x, y⟩ = x * y := by simp[Inner.inner]

  variable {U V} [Hilbert U] [Hilbert V]
  instance : Inner (U×V) := ⟨λ x y => ⟨x.1, y.1⟩ + ⟨x.2, y.2⟩⟩
  instance : Hilbert (U×V) := 
  {
    inner_symm := sorry,
    inner_pos := sorry,
    inner_add := sorry,
    inner_mul := sorry
  } 

end CommonHilbertSpaces 
