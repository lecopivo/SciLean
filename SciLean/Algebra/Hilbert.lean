import Mathlib.Data.Enumtype

import SciLean.Algebra.VectorSpace

namespace SciLean

--  ___            _   ___                     ___             _         _
-- / __| ___ _ __ (_) |_ _|_ _  _ _  ___ _ _  | _ \_ _ ___  __| |_  _ __| |_
-- \__ \/ -_) '  \| |  | || ' \| ' \/ -_) '_| |  _/ '_/ _ \/ _` | || / _|  _|
-- |___/\___|_|_|_|_| |___|_||_|_||_\___|_|   |_| |_| \___/\__,_|\_,_\__|\__|

-- Signature of a SemiInner product
-- structure SemiInner.Signature where
--   Dom  : Type -- domain      
--   Dom' : Type -- usuall of type `D → ℝ` (or isomorphic to it) excep in the case of D = Unit then D' is just ℝ
--   eval   : Dom' → Dom → ℝ
-- attribute [reducible]  SemiInner.Signature.Dom'  SemiInner.Signature.Dom  SemiInner.Signature.eval

class SemiInner (X : Type u) (Dom : Type v) where
  semiInner     : X → X → Dom → ℝ
  testFunction  : Dom → X → Prop

class SemiInnerTrait (X : Type u) where
  domOf : Type v
attribute [reducible] SemiInnerTrait.domOf

@[reducible]
instance {X S} [SemiInner X S] : SemiInnerTrait X := ⟨S⟩


abbrev semiInner {X : Type u} [SemiInnerTrait X] [inst : SemiInner X (SemiInnerTrait.domOf X)] 
       := SemiInner.semiInner (self := inst) 

-- How to set up priorities correctly? 
notation "⟪" x ", " y "⟫" => semiInner x y  

-- Not sure if I want this coercion, it is a bit overkill
-- instance : Coe (Unit → ℝ) ℝ := ⟨λ f => f ()⟩
notation "∥" x "∥"  => Math.sqrt (SemiInner.semiInner (Dom := Unit) x x ())

namespace SemiInner

  export SemiInnerTrait (domOf)

  
  instance : SemiInner ℝ Unit :=
  {
    semiInner    := λ x y _ => x * y
    testFunction := λ _ _ => True
  }

  instance (X Y Dom) [SemiInner X Dom] [SemiInner Y Dom] : SemiInner (X × Y) Dom :=
  { 
    semiInner     := λ (x,y) (x',y') => ⟪x,x'⟫ + ⟪y,y'⟫
    testFunction  := λ D (x,y) => testFunction D x ∧ testFunction D y
  }

  instance (ι X Dom) [SemiInner X Dom] [Zero X] [Enumtype ι] : SemiInner (ι → X) Dom :=
  {
    semiInner    := λ f g => ∑ i, ⟪f i, g i⟫
    testFunction := λ D f => ∀ i, testFunction D (f i)
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


class SemiHilbert (X : Type u) (Dom : Type v) extends Vec X, SemiInner X Dom  where
  semi_inner_add : ∀ (x y z : X),     ⟪x + y, z⟫ = ⟪x,z⟫ + ⟪y,z⟫
  semi_inner_mul : ∀ (x y : X) (r : ℝ),  ⟪r*x,y⟫ = r*⟪x,y⟫
  semi_inner_sym : ∀ (x y : X),            ⟪x,y⟫ = ⟪y,x⟫
  semi_inner_pos : ∀ (x : X) D, (⟪x,x⟫ D) ≥ (0 : ℝ)
  semi_inner_ext : ∀ (x : X), ((x = 0) ↔ (∀ D (x' : X) (h : testFunction D x'), ⟪x,x'⟫ D = 0))
  -- Add test functions form a subspace

class Hilbert (X : Type u) extends SemiHilbert X Unit


namespace SemiHilbert 

  open SemiInner

  instance : SemiHilbert ℝ Unit := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }

  instance (X Y Dom) [SemiHilbert X Dom] [SemiHilbert Y Dom] : SemiHilbert (X × Y) Dom := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }

  instance (ι : Type) (X Dom )[SemiHilbert X Dom] [Enumtype ι] : SemiHilbert (ι → X) Dom := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }

end SemiHilbert 
