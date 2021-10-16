import SciLean.Algebra.VectorSpace

--  ___            _   ___                     ___             _         _
-- / __| ___ _ __ (_) |_ _|_ _  _ _  ___ _ _  | _ \_ _ ___  __| |_  _ __| |_
-- \__ \/ -_) '  \| |  | || ' \| ' \/ -_) '_| |  _/ '_/ _ \/ _` | || / _|  _|
-- |___/\___|_|_|_|_| |___|_||_|_||_\___|_|   |_| |_| \___/\__,_|\_,_\__|\__|

class SemiInner (X : Type u) : Type (u+1) where
  integrable_domain : Type
  domain            : integrable_domain   -- proof that `integrable_domain` is nonempty
  semi_inner     : X → X → integrable_domain → ℝ
  loc_integrable : X → Prop
  test_function  : integrable_domain → X → Prop

-- export SemiInner (integrable_domain semi_inner loc_integrable test_function domain)

instance {X} [SemiInner X] : Inhabited (SemiInner.integrable_domain X) := ⟨SemiInner.domain⟩

-- abbrev IntDom (X : Type u) [SemiInner X] := SemiInner.integrable_domain X

-- class LocInt {X : Type u} [SemiInner X] (x : X) : Prop where
--   proof : SemiInner.loc_integrable x

-- class TestFun {X : Type u} [SemiInner X] (i : IntDom X) (x : X) : Prop where
--   proof : SemiInner.test_function i x

-- syntax:60 "(" term:60 " , " term:61 ")_[" term:62 "]" : term
-- macro_rules | `(($x,$y)_[$i]) => `(SemiInner.semi_inner $x $y $i)

--- TODO: Make sure preceences are correct!!!
notation:100 "(" x:60 ", " y:61 ")_[" i:62 "]" => SemiInner.semi_inner x y i 

-- Semi inner product on canonical domain. 
-- This is usefull for Hilbert spaces where there is only one domain.
notation:100 "⟨" x:60 ", " y:61 "⟩" => SemiInner.semi_inner x y SemiInner.domain
notation:120 "∥" x:80 "∥"  => Math.sqrt (SemiInner.semi_inner x x SemiInner.domain)

namespace SemiInner

  instance : SemiInner ℝ :=
  {
    integrable_domain := Unit
    domain            := Unit.unit
    semi_inner        := λ x y _ => x * y
    loc_integrable    := λ _ => True
    test_function     := λ _ _ => True
  }

  instance : SemiInner PUnit :=
  {
    integrable_domain := Unit
    domain            := Unit.unit
    semi_inner        := λ x y _ => 0
    loc_integrable    := λ _ => True
    test_function     := λ _ _ => True
  }

  instance (X : Type u) (Y : Type v) [SemiInner X] [SemiInner Y] : SemiInner (X × Y) :=
  { 
    integrable_domain := integrable_domain X × integrable_domain Y
    domain         := (arbitrary, arbitrary)
    semi_inner     := λ (x,y) (x',y') (D,E) => (x,x')_[D] + (y,y')_[E]
    loc_integrable := λ (x,y) => loc_integrable x ∧ loc_integrable y
    test_function  := λ (D,E) (x,y) => test_function D x ∧ test_function E y
  }

  instance (X : Type u) [SemiInner X] [Zero X] : SemiInner (Nat → X) :=
  {
    integrable_domain := Nat × integrable_domain X
    domain            := (0, arbitrary)
    semi_inner        := λ f g (n, D) => ∑ i : Fin n, (f i, g i)_[D]
    loc_integrable    := λ f => ∀ i, loc_integrable (f i)
    test_function     := λ (n, D) f => ∀ i, if (i < n) then (test_function D (f i)) else ((f i) = 0)
  }

  --- Add dependent type version ...
  instance {n} (X : Type u) [SemiInner X] [Zero X] : SemiInner (Fin n → X) :=
  {
    integrable_domain := integrable_domain X
    domain            := arbitrary
    semi_inner        := λ f g D => ∑ i : Fin n, (f i, g i)_[D]
    loc_integrable    := λ f => ∀ i, loc_integrable (f i)
    test_function     := λ D f => ∀ i, test_function D (f i)
  }

  -- for this we need integral and derivative these will be defined in Prelude
  -- def is_continuous {X Y} [Vec X] [Vec Y] (f : X → Y) : Prop := sorry
  -- def integral {X : Type u} [Vec X] (a b : ℝ) (f : ℝ → X) (h : is_continuous f) : X := sorry
  -- instance (X : Type u) [SemiInner X] [Vec X] : SemiInner (ℝ → X) := 
  -- {
  --   integrable_domain := (ℝ×ℝ) × integrable_domain X
  --   semi_inner         := λ (f g : ℝ → X) ((a,b), i) => integral a b (λ t => (f t, g t)_[i])
  --   loc_integrable := is_continuous f
  --   test_function := is_smooth f ∧ zero_gradients_at a f ∧ zero_gradients_at b f
  -- }                             

end SemiInner

--  ___            _   _  _ _ _ _             _     ___
-- / __| ___ _ __ (_) | || (_) | |__  ___ _ _| |_  / __|_ __  __ _ __ ___
-- \__ \/ -_) '  \| | | __ | | | '_ \/ -_) '_|  _| \__ \ '_ \/ _` / _/ -_)
-- |___/\___|_|_|_|_| |_||_|_|_|_.__/\___|_|  \__| |___/ .__/\__,_\__\___|
--                                                     |_|

class SemiHilbert (X : Type u) extends SemiInner X, Vec X where
  semi_inner_add : ∀ (x y z : X) D, (x + y, z)_[D] = (x,z)_[D] + (y,z)_[D]
  semi_inner_mul : ∀ (x y : X) (r : ℝ) D, (r*x,y)_[D] = r*(x,y)_[D]
  semi_inner_sym : ∀ (x y : X) D, (x,y)_[D] = (y,x)_[D]
  semi_inner_pos : ∀ (x : X) D, ((x,x)_[D]) ≥ (0 : ℝ)
  semi_inner_ext : ∀ (x : X), loc_integrable x → ((x = 0) ↔ (∀ D (y : X) (h : test_function D y), (x,y)_[D] = 0))



namespace SemiHilbert 

  -- U×V, Nat → U, Fin n → U are SemiHilbert

end SemiHilbert 

--  _  _ _ _ _             _     ___
-- | || (_) | |__  ___ _ _| |_  / __|_ __  __ _ __ ___
-- | __ | | | '_ \/ -_) '_|  _| \__ \ '_ \/ _` / _/ -_)
-- |_||_|_|_|_.__/\___|_|  \__| |___/ .__/\__,_\__\___|
--                                  |_|

class Hilbert (U : Type u) extends SemiHilbert U where
  domain_unique : ∀ D, D = domain
  all_integrable : ∀ x, loc_integrable x
  all_test_fun   : ∀ x, test_function domain x

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
    inner_sym := sorry,
    inner_pos := sorry,
    inner_add := sorry,
    inner_mul := sorry
  } 

  instance : Inner PUnit := ⟨λ x y => 0⟩
  instance : Hilbert PUnit := 
  {
    inner_sym := sorry,
    inner_pos := sorry,
    inner_add := sorry,
    inner_mul := sorry
  } 

  variable {U V} [Hilbert U] [Hilbert V]
  instance : Inner (U×V) := ⟨λ x y => ⟨x.1, y.1⟩ + ⟨x.2, y.2⟩⟩
  instance : Hilbert (U×V) := 
  {
    inner_sym := sorry,
    inner_pos := sorry,
    inner_add := sorry,
    inner_mul := sorry
  } 

  instance {n} : Inner (Fin n → U) := ⟨λ f g => ∑ i, ⟨f i, g i⟩⟩
  instance : Hilbert (Fin n → U) := 
  {
    inner_sym := sorry,
    inner_pos := sorry,
    inner_add := sorry,
    inner_mul := sorry
  } 

end CommonHilbertSpaces 
