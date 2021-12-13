import SciLean.Mathlib.Data.Enumtype

import SciLean.Algebra.VectorSpace

namespace SciLean

--  ___            _   ___                     ___             _         _
-- / __| ___ _ __ (_) |_ _|_ _  _ _  ___ _ _  | _ \_ _ ___  __| |_  _ __| |_
-- \__ \/ -_) '  \| |  | || ' \| ' \/ -_) '_| |  _/ '_/ _ \/ _` | || / _|  _|
-- |___/\___|_|_|_|_| |___|_||_|_||_\___|_|   |_| |_| \___/\__,_|\_,_\__|\__|

namespace SemiInner

  structure Signature where
    R : Type u
    D : Type v
    eval : R → D → ℝ

  attribute [reducible] Signature.R Signature.D

  @[reducible]
  def Signature.addInterval (s : Signature) : Signature :=
    ⟨(ℝ × ℝ) → s.R,
     (ℝ × ℝ) × s.D,
     λ f (I, d) => s.eval (f I) d⟩
  
  class Trait (X : Type u) where
    sig : Signature

end SemiInner

attribute [reducible] SemiInner.Trait.sig

open SemiInner in
class SemiInner' (X : Type u) (S : Signature) where  
  semiInner : X → X → S.R
  testFunction : S.D → X → Prop

-- open SemiInner in
-- class SemiInner (X : Type u) [Trait X] extends SemiInner' X (Trait.sig X)

-- #check @SemiInner'.semiInner (self := SemiInner.toSemiInner' _ (Trait.sig _))

-- instance {X} [SemiInner.Trait X] [SemiInner X] : SemiInner' X (SemiInner.Trait.sig X) := SemiInner.semi_inner_inst

namespace SemiInner

  -- @[reducible]
  -- instance {X S} [Signature S] [SemiInner X S] : Trait X := ⟨S⟩

  -- export Trait (sigOf)

  -- @[reducible]
  -- abbrev domOf (X) [SemiInnerTrait X] [inst : SemiInner X (sigOf X)] 
  --   := SignatureDom.Dom (sigOf X)

  -- def testFunction {X S} [SemiInner X S]
  --   (D : domOf X) (x : X) : Prop 
  --   := SemiInner.testFunctionProp D x

  abbrev semiInner' {X : Type u} [Trait X] [Vec (Trait.sig X).R] [SemiInner' X (Trait.sig X)] : X → X → (Trait.sig X).R
    := SemiInner'.semiInner

  -- How to set up priorities correctly? 
  notation "⟪" S "|" x ", " y "⟫" => SemiInner'.semiInner (S := S) x y  
  notation "⟪" x ", " y "⟫" => semiInner' x y  

  notation "∥" x "∥"  => Math.sqrt (SemiInner'.semiInner (S := Unit) x x ())

  abbrev RealSig : Signature := ⟨ℝ, Unit, λ r _ => r⟩
  -- instance : Vec RealSig.R := by simp[RealSig] infer_instance done

  open SemiInner'

  -- Reals
  instance : SemiInner' ℝ RealSig :=
  {
    semiInner := λ x y => x * y
    testFunction := λ _ _ => True
  }
  -- @[reducible] instance : Trait ℝ := ⟨RealSig⟩
  -- instance : SemiInner ℝ := SemiInner.mk

  -- Product
  instance (X Y S) [Vec S.R] [SemiInner' X S] [SemiInner' Y S] 
  : SemiInner' (X × Y) S :=
  { 
    semiInner     := λ (x,y) (x',y') => ⟪S| x,x'⟫ + ⟪S| y,y'⟫
    testFunction  := λ D (x,y) => testFunction D x ∧ testFunction D y
  }
  -- @[reducible] instance {X Y} [Trait X] : Trait (X × Y) := ⟨Trait.sig X⟩
  -- @[reducible] instance {X Y} [Trait Y] : Trait (X × Y) := ⟨Trait.sig Y⟩
  -- instance (X Y) [Trait X] [SemiInner X] [SemiInner' Y (Trait.sig X)] [Vec (Trait.sig X).R] : SemiInner (X × Y) := SemiInner.mk
  -- instance (X Y) [Trait Y] [SemiInner Y] [SemiInner' X (Trait.sig Y)] [Vec (Trait.sig Y).R] : SemiInner (X × Y) := SemiInner.mk

  -- Function space over finite set
  instance (ι X S) [SemiInner' X S] [Vec S.R] [Enumtype ι] : SemiInner' (ι → X) S :=
  {
    semiInner       := λ f g => ∑ i, ⟪S| f i, g i⟫
    testFunction := λ D f => ∀ i, testFunction D (f i)
  }
  -- @[reducible] instance {ι X} [Trait X] [Enumtype ι] : Trait (ι → X) := ⟨Trait.sig X⟩
  -- instance (ι : Type u) (X) [Trait X] [SemiInner X] [Enumtype ι] [Vec (Trait.sig X).R] : SemiInner (ι → X) := SemiInner.mk

end SemiInner


--  ___            _   _  _ _ _ _             _     ___
-- / __| ___ _ __ (_) | || (_) | |__  ___ _ _| |_  / __|_ __  __ _ __ ___
-- \__ \/ -_) '  \| | | __ | | | '_ \/ -_) '_|  _| \__ \ '_ \/ _` / _/ -_)
-- |___/\___|_|_|_|_| |_||_|_|_|_.__/\___|_|  \__| |___/ .__/\__,_\__\___|
--                                                     |_|
section SemiHilbert
open SemiInner

class SemiHilbert' (X : Type u) (S : Signature) [Vec S.R] extends SemiInner' X S, Vec X where
  semi_inner_add : ∀ (x y z : X),     ⟪S| x + y, z⟫ = ⟪S| x,z⟫ + ⟪S| y,z⟫
  semi_inner_mul : ∀ (x y : X) (r : ℝ),  ⟪S| r*x,y⟫ = r*⟪S| x,y⟫
  semi_inner_sym : ∀ (x y : X),            ⟪S| x,y⟫ = ⟪S| y,x⟫
  semi_inner_pos : ∀ (x : X) D, (S.eval ⟪S| x,x⟫ D) ≥ (0 : ℝ)
  semi_inner_ext : ∀ (x : X), 
                     ((x = 0) 
                      ↔ 
                      (∀ D (x' : X) (h : testFunction D x'), S.eval ⟪S| x,x'⟫ D = 0))
  -- Add test functions form a subspace


-- class SemiHilbert (X : Type u) [outParam $ Trait X] [outParam $ Vec (Trait.sig X).R] extends SemiHilbert' X (Trait.sig X)
-- instance {X} [Trait X] [Vec (Trait.sig X).R] [SemiHilbert X] : SemiInner X := SemiInner.mk

 -- SemiHilbert (X : Type u) [SemiInner X] [Vec (SemiInner.sig X).R] := SemiHilbert' X (SemiInner.sig X)

abbrev Hilbert (X : Type u) := SemiHilbert' X SemiInner.RealSig
@[reducible] instance {X} [Hilbert X] : Trait X := ⟨SemiInner.RealSig⟩
-- instance {X} [Hilbert X] : SemiInner X := SemiInner.mk

-- I really do not understand why is this necessary ... I think it is a bug
-- reported here: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Odd.20type.20class.20failure
instance {X} [SemiHilbert' X SemiInner.RealSig] : Vec X := SemiHilbert'.toVec SemiInner.RealSig
-- Alternatively we can change [Vec S.R] to [outParam $ Vec S.R] 
-- but this causes some timeouts somewhere else ...

variable {X} [Hilbert X] (x y : X) (r s : ℝ)

#check r * x

namespace SemiHilbert 

  open SemiInner

  instance : SemiHilbert' ℝ RealSig := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }
  -- instance : SemiHilbert ℝ := SemiHilbert.mk

  instance (X Y S) [Vec S.R] [SemiHilbert' X S] [SemiHilbert' Y S] 
    : SemiHilbert' (X × Y) S := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }
  -- instance {X Y} [Trait X] [Vec (Trait.sig X).R] [SemiHilbert X] [SemiHilbert' Y (Trait.sig X)]: SemiHilbert ℝ := SemiHilbert.mk
  -- instance {X Y} [Trait Y] [Vec (Trait.sig Y).R] [SemiHilbert Y] [SemiHilbert' X (Trait.sig Y)]: SemiHilbert ℝ := SemiHilbert.mk


  instance (ι : Type v) (X S) [Vec S.R] [SemiHilbert' X S] [Enumtype ι] 
    : SemiHilbert' (ι → X) S := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }
  -- instance {ι : Type v} {X} [Trait X] [Vec (Trait.sig X).R] [SemiHilbert X] [Enumtype ι] : SemiHilbert (ι → X) := SemiHilbert.mk


end SemiHilbert 
