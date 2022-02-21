import SciLean.Mathlib.Data.Enumtype

import SciLean.Algebra.VectorSpace

namespace SciLean

namespace SemiInner

  class Trait (X : Type u) where
    R : Type v
    D : Type w
    eval : R → D → ℝ

  class Trait₂ (X : Type u) (Y : Type u') where
    R : Type v
    D : Type w
    eval : R → D → ℝ

  attribute [reducible] Trait.R Trait.D Trait.eval
  attribute [reducible] Trait₂.R Trait₂.D Trait₂.eval

  @[reducible] instance {X Y} [Trait X] : Trait₂ X Y := ⟨Trait.R X, Trait.D X, Trait.eval⟩
  @[reducible] instance {X Y} [Trait Y] : Trait₂ X Y := ⟨Trait.R Y, Trait.D Y, Trait.eval⟩

  -- class Guard (X : Type u) 
  -- class Guard₂ (X : Type u) (Y : Type u')

  -- instance {X} [Trait X] : Guard X := ⟨⟩
  -- instance {X Y} [Trait₂ X Y] : Guard₂ X Y := ⟨⟩

end SemiInner

class SemiInner (X : Type u) (R : Type v) (D : Type w) (eval : R → D → ℝ) where  
  semiInner : X → X → R
  testFunction : D → X → Prop

namespace SemiInner

  @[reducible] instance (X) (R : Type u) (D : Type v) (e : R → D → ℝ) [SemiInner X R D e] : Trait X := ⟨R, D, e⟩

  -- open SemiInner in
  -- abbrev semiInner' {X : Type u} [Trait X] [SemiInner X (Trait.R X) (Trait.D X) Trait.eval] : X → X → (Trait.R X)
  --   := SemiInner.semiInner Trait.eval

  -- notation "⟪" e "|" x ", " y "⟫" => SemiInner.semiInner e x y  

  abbrev semiInner' {X} [Trait X] [inst : SemiInner X (Trait.R X) (Trait.D X) Trait.eval] (x y : X) 
    := SemiInner.semiInner (self := inst) _ x y

  abbrev testFunction' {X} [Trait X] [inst : SemiInner X (Trait.R X) (Trait.D X) Trait.eval]
    := SemiInner.testFunction (self := inst)

  notation "⟪" x ", " y "⟫" => semiInner' x y 

  def normSqr {X}[Trait X] [inst : SemiInner X (Trait.R X) (Trait.D X) Trait.eval] (x : X) := ⟪x, x⟫

  notation "∥" x "∥²" => normSqr x

  -- @[reducible] instance : Trait ℝ := ⟨ℝ, Unit, λ r _ => r⟩

  -- Reals
  instance : SemiInner ℝ ℝ Unit (λ r _ => r):=
  {
    semiInner := λ x y => x * y
    testFunction := λ _ _ => True
  }

  -- Product type
  instance (X Y R D e) [SemiInner X R D e] [SemiInner Y R D e] [Add R] 
    : SemiInner (X × Y) R D e :=
  { 
    semiInner     := λ (x,y) (x',y') => ⟪x,x'⟫ + ⟪y,y'⟫
    testFunction  := λ d (x,y) => testFunction' d x ∧ testFunction' d y
  }
  -- Maybe use Trait₂
  @[reducible] instance (X Y) [Trait X] : Trait (X × Y) 
    := ⟨Trait.R X, Trait.D X, Trait.eval⟩
  @[reducible] instance (X Y) [Trait Y] : Trait (X × Y) 
    := ⟨Trait.R Y, Trait.D Y, Trait.eval⟩

  -- Pi type
  instance (ι X R D e) [SemiInner X R D e] [Add R] [Zero R] [Enumtype ι] : SemiInner (ι → X) R D e :=
  {
    semiInner       := λ f g => ∑ i, ⟪f i, g i⟫
    testFunction := λ d f => ∀ i, testFunction' d (f i)
  }
  @[reducible] instance {X} [Trait X] [Enumtype ι] : Trait (ι → X) 
    := ⟨Trait.R X, Trait.D X, Trait.eval⟩

  -- example (X R D e) [SemiInner X R D e] [Enumtype ι] [Add R] [Zero R] 
  --   : SemiInner (ι → X) R D e := by infer_instance

end SemiInner

--   (R : outParam (Type v)) (D : outParam (Type w)) (e : outParam (R → D → ℝ))
--   (R : Type u) (D : Type v) (e : R → D → ℝ)
open SemiInner in
class SemiHilbert (X) (R : Type u) (D : Type v) (e : R → D → ℝ) [outParam $ Vec R] extends Vec X, SemiInner X R D e where
  semi_inner_add : ∀ (x y z : X),      ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
  semi_inner_mul : ∀ (x y : X) (r : ℝ),  ⟪r*x, y⟫ = r*⟪x, y⟫
  semi_inner_sym : ∀ (x y : X),            ⟪x, y⟫ = ⟪y, x⟫
  semi_inner_pos : ∀ (x : X) D,  (e ⟪x, x⟫ D) ≥ (0 : ℝ)
  semi_inner_ext : ∀ (x : X), 
                     ((x = 0) 
                      ↔ 
                      (∀ D (x' : X) (h : testFunction D x'), e ⟪x, x'⟫ D = 0))

attribute [inferTCGoalsRL] SemiHilbert.toSemiInner

abbrev Hilbert (X : Type u) := SemiHilbert X ℝ Unit (λ r _ => r)
-- @[reducible] instance {X} [Hilbert X] : SemiInner.Trait X := by infer_instance
-- @[reducible] instance {X R D e} [SemiInner X R D e] : SemiInner.Trait X := by infer_instance

namespace SemiHilbert 

  open SemiInner

  instance : Hilbert ℝ := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }

  -- instance (X Y) [Trait₂ X Y] [Vec (Trait₂.R X Y)] 
  --   [SemiHilbert X (Trait₂.R X Y) (Trait₂.D X Y) Trait₂.eval] 
  --   [SemiHilbert Y (Trait₂.R X Y) (Trait₂.D X Y) Trait₂.eval] 
  --   : SemiHilbert (X × Y) (Trait₂.R X Y) (Trait₂.D X Y) Trait₂.eval := 
  @[inferTCGoalsRL]
  instance (X Y R D e) -- [Trait₂ X Y] 
    [Vec R]
    [SemiHilbert X R D e] 
    [SemiHilbert Y R D e] 
    : SemiHilbert (X × Y) R D e := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }
  -- instance {X Y} [Trait X] [Vec (Trait.sig X).R] [SemiHilbert X] [SemiHilbert' Y (Trait.sig X)]: SemiHilbert ℝ := SemiHilbert.mk
  -- instance {X Y} [Trait Y] [Vec (Trait.sig Y).R] [SemiHilbert Y] [SemiHilbert' X (Trait.sig Y)]: SemiHilbert ℝ := SemiHilbert.mk

  -- set_option trace.Meta.synthInstance true in
  -- example {X Y} [Hilbert X] [Hilbert Y] : Hilbert (X × Y) := by infer_instance


  -- instance (X) [Trait X] [Vec (Trait.R X)] 
  --   [SemiHilbert X (Trait.R X) (Trait.D X) Trait.eval] (ι : Type v) [Enumtype ι] 
  --   : SemiHilbert (ι → X) (Trait.R X) (Trait.D X) Trait.eval := 

  @[inferTCGoalsRL]
  instance (X R D e) --[Trait X] 
    [Vec R]
    [SemiHilbert X R D e] (ι : Type v) [Enumtype ι] 
    : SemiHilbert (ι → X) R D e := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }
  -- instance {ι : Type v} {X} [Trait X] [Vec (Trait.sig X).R] [SemiHilbert X] [Enumtype ι] : SemiHilbert (ι → X) := SemiHilbert.mk

end SemiHilbert

-- example (n m) : SemiInner.Trait (Fin n → Fin m → ℝ) := by infer_instance
