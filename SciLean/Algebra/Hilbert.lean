import Mathlib.Data.Enumtype

import SciLean.Algebra.VectorSpace

namespace SciLean

--  ___            _   ___                     ___             _         _
-- / __| ___ _ __ (_) |_ _|_ _  _ _  ___ _ _  | _ \_ _ ___  __| |_  _ __| |_
-- \__ \/ -_) '  \| |  | || ' \| ' \/ -_) '_| |  _/ '_/ _ \/ _` | || / _|  _|
-- |___/\___|_|_|_|_| |___|_||_|_||_\___|_|   |_| |_| \___/\__,_|\_,_\__|\__|

namespace SemiInner 

  class Signature (S : Type u) where
    Dom : Type v
    eval : S → Dom → ℝ

  class Trait (X : Type u) where
    sigOf : Type v

  -- attribute [reducible] SignatureDom.Dom
  attribute [reducible] Trait.sigOf

end SemiInner

open SemiInner in
class SemiInner (X : Type u) (S : Type v) [Signature S] where  
  semi_inner : X → X → S
  testFunction : Signature.Dom S → X → Prop

namespace SemiInner

  @[reducible]
  instance {X S} [Signature S] [SemiInner X S] : Trait X := ⟨S⟩

  export Trait (sigOf)

  -- @[reducible]
  -- abbrev domOf (X) [SemiInnerTrait X] [inst : SemiInner X (sigOf X)] 
  --   := SignatureDom.Dom (sigOf X)

  -- def testFunction {X S} [SemiInner X S]
  --   (D : domOf X) (x : X) : Prop 
  --   := SemiInner.testFunctionProp D x

  abbrev semiInner {X : Type u} [Trait X] [Signature (sigOf X)]
    [inst : SemiInner X (sigOf X)] 
    := SemiInner.semi_inner (self := inst) 

  -- How to set up priorities correctly? 
  notation "⟪" x ", " y "⟫" => semiInner x y  

  -- Not sure if I want this coercion, it is a bit overkill
  instance : Coe (Unit → ℝ) ℝ := ⟨λ f => f ()⟩
  notation "∥" x "∥"  => Math.sqrt (SemiInner.semiInner (S := Unit) x x ())

  instance : Signature ℝ :=
  {
    Dom  := Unit
    eval := λ r _ => r  
  }

  instance : SemiInner ℝ ℝ :=
  {
    semi_inner       := λ x y => x * y
    testFunction := λ _ _ => True
  }

  instance (X Y S) [Vec S] [Signature S] [SemiInner X S] [SemiInner Y S] : SemiInner (X × Y) S :=
  { 
    semi_inner        := λ (x,y) (x',y') => ⟪x,x'⟫ + ⟪y,y'⟫
    testFunction  := λ D (x,y) => testFunction D x ∧ testFunction D y
  }

  instance (ι X S) [Vec S] [Signature S] [SemiInner X S] [Enumtype ι] : SemiInner (ι → X) S :=
  {
    semi_inner       := λ f g => ∑ i, ⟪f i, g i⟫
    testFunction := λ D f => ∀ i, testFunction D (f i)
  }

  -- for this we need integral and derivative these will be defined in Prelude
  -- def is_continuous {X Y} [Vec X] [Vec Y] (f : X → Y) : Prop := sorry
  -- def integral {X : Type u} [Vec X] (a b : ℝ) (f : ℝ → X) (h : is_continuous f) : X := sorry
  -- instance (X : Type u) [SemiInner X] [Vec X] : SemiInner (ℝ → X) := 
  -- {
  --   integrable_Sain := (ℝ×ℝ) × integrable_Sain X
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

open SemiInner Signature in
class SemiHilbert (X : Type u) (S : Type v) [Signature S] [Vec S] extends Vec X, SemiInner X S where
  semi_inner_add : ∀ (x y z : X),     ⟪x + y, z⟫ = ⟪x,z⟫ + ⟪y,z⟫
  semi_inner_mul : ∀ (x y : X) (r : ℝ),  ⟪r*x,y⟫ = r*⟪x,y⟫
  semi_inner_sym : ∀ (x y : X),            ⟪x,y⟫ = ⟪y,x⟫
  semi_inner_pos : ∀ (x : X) D, (eval ⟪x,x⟫ D) ≥ (0 : ℝ)
  semi_inner_ext : ∀ (x : X), 
                     ((x = 0) 
                      ↔ 
                      (∀ D (x' : X) (h : testFunction D x'), eval ⟪x,x'⟫ D = 0))
  -- Add test functions form a subspace

abbrev Hilbert (X : Type u) := SemiHilbert X ℝ

namespace SemiHilbert 

  open SemiInner

  instance : SemiHilbert ℝ ℝ := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }

  -- instance : Hilbert ℝ := by infer_instance

  instance (X Y S) [Signature S] [Vec S] [SemiHilbert X S] [SemiHilbert Y S] 
    : SemiHilbert (X × Y) S := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }

  instance (ι : Type u) (X S) [Signature S] [Vec S] [SemiHilbert X S] [Enumtype ι] 
    : SemiHilbert (ι → X) S := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }

end SemiHilbert 
