import SciLean.Mathlib.Data.Enumtype

import SciLean.Algebra.VectorSpace

namespace SciLean

class SemiInner (X : Type u) where  
  Domain : Type
  domain : Domain -- some arbitrary domain
  semiInner : X → X → Domain → ℝ
  testFunction : Domain → X → Prop

-- attribute [reducible] SemiInner.Domain

namespace SemiInner

  prefix:max "𝓓 " => Domain
  instance {X} [SemiInner X] : Inhabited (𝓓 X) := ⟨domain⟩

  notation "⟪" x ", " y "⟫" => semiInner x y default
  notation "⟪" x ", " y "⟫[" Ω "]" => (semiInner x y) Ω

  def normSqr {X} [SemiInner X] (x : X) := ⟪x, x⟫

  notation "∥" x "∥²" => normSqr x

  -- Reals
  -- @[reducible]
  instance : SemiInner ℝ :=
  {
    Domain := Unit
    domain := ()
    semiInner := λ x y _ => x * y
    testFunction := λ _ _ => True
  }

  -- Product type
  -- @[reducible]
  instance (X Y) [SemiInner X] [SemiInner Y]
    : SemiInner (X × Y) :=
  { 
    Domain := Domain X × Domain Y
    domain := (domain, domain)
    semiInner     := λ (x,y) (x',y') (Ω, Ω') => ⟪x,x'⟫[Ω] + ⟪y,y'⟫[Ω']
    testFunction  := λ (Ω,Ω') (x,y) => testFunction Ω x ∧ testFunction Ω' y
  }

  -- Pi type
  -- @[reducible]
  instance (X) [SemiInner X] (ι) [Enumtype ι] : SemiInner (ι → X) :=
  {
    Domain := Domain X
    domain := domain
    semiInner    := λ f g Ω => ∑ i, ⟪f i, g i⟫[Ω]
    testFunction := λ Ω f => ∀ i, testFunction Ω (f i)
  }

  instance (X) [SemiInner X] [Zero X] : SemiInner (ℤ → X) :=
  {
    Domain := (ℤ × ℤ) × (𝓓 X)
    domain := ((0, 1), default)
    semiInner    := λ f g ((a, b), Ω) => ∑ i : Fin (b - a).toNat, ⟪f (a + i), g (a + i)⟫[Ω]
    testFunction := λ ((a, b), Ω) f => ∀ i : ℤ, 
      if (i ≥ a) ∧ (i < b) 
      then testFunction Ω (f i)
      else (f i) = 0
  }

end SemiInner

-- (R : outParam (Type v)) (D : outParam (Type w)) (e : outParam (R → Domain → ℝ))
-- (R : Type u) (D : Type v) (e : R → Domain → ℝ)
open SemiInner in
class SemiHilbert (X) extends Vec X, SemiInner X where
  semi_inner_add : ∀ (x y z : X) Ω,      ⟪x + y, z⟫[Ω] = ⟪x, z⟫[Ω] + ⟪y, z⟫[Ω]
  semi_inner_mul : ∀ (x y : X) (r : ℝ) Ω,  ⟪r*x, y⟫[Ω] = r*⟪x, y⟫[Ω]
  semi_inner_sym : ∀ (x y : X) Ω,            ⟪x, y⟫[Ω] = ⟪y, x⟫[Ω]
  semi_inner_pos : ∀ (x : X) Ω,            (⟪x, x⟫[Ω]) ≥ (0 : ℝ)
  semi_inner_ext : ∀ (x : X),
    ((x = 0) ↔ (∀ Ω (x' : X) (h : testFunction d x'), ⟪x, x'⟫[Ω] = 0))

-- Hilbert space is something where Domains are an singleton/unit/contractible type
open SemiInner Function in
class Hilbert (X) extends SemiHilbert X where
  D_is_unit : ∃ f : 𝓓 X → Unit, bijective f
                                     
namespace SemiHilbert 

  open SemiInner

  instance : SemiHilbert ℝ := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }

  instance : Hilbert ℝ :=
  {
    D_is_unit := sorry
  }

  instance (X Y) [SemiHilbert X] [SemiHilbert Y] 
    : SemiHilbert (X × Y) := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }

  instance (X Y) [Hilbert X] [Hilbert Y] 
    : Hilbert (X × Y) := 
  {
    D_is_unit := sorry
  }

  instance (X) [SemiHilbert X] (ι) [Enumtype ι] 
    : SemiHilbert (ι → X) := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
  }

  instance (X) [Hilbert X] (ι) [Enumtype ι] 
    : Hilbert (ι → X) := 
  {
    D_is_unit := sorry
  }

end SemiHilbert
