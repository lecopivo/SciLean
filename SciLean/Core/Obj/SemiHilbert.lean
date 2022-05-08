import SciLean.Mathlib.Data.Enumtype

import SciLean.Core.Obj.Vec

namespace SciLean

class TestFunctions (X : Type u) where  
  testFunction : X → Prop
  test : X → (ϕ : X) → (h : testFunction ϕ) → ℝ

-- attribute [reducible] TestFunctions.Domain


namespace TestFunctions

  -- Reals
  -- @[reducible]
  instance : TestFunctions ℝ :=
  {
    testFunction := λ _ => True
    test := λ x y _ => x * y
  }

  -- Product type
  -- @[reducible]
  instance (X Y) [TestFunctions X] [TestFunctions Y]
    : TestFunctions (X × Y) :=
  { 
    testFunction  := λ (x,y) => testFunction x ∧ testFunction y
    test := λ (x,y) (x',y') h => test x x' h.1 + test y y' h.2
  }

  -- Pi type
  -- @[reducible]
  instance (X) [TestFunctions X] (ι) [Enumtype ι] : TestFunctions (ι → X) :=
  {
    testFunction := λ f => ∀ i, testFunction (f i)
    test := λ x ϕ h => ∑ i, test (x i) (ϕ i) (h i)
  }

  -- instance (X) [TestFunctions X] [Zero X] : TestFunctions (ℤ → X) :=
  -- {
  --   Domain := (ℤ × ℤ) × (𝓓 X)
  --   domain := ((0, 1), default)
  --   TestFunctions    := λ f g ((a, b), Ω) => ∑ i : Fin (b - a).toNat, ⟪f (a + i), g (a + i)⟫[Ω]
  --   testFunction := λ ((a, b), Ω) f => ∀ i : ℤ, 
  --     if (i ≥ a) ∧ (i < b) 
  --     then testFunction Ω (f i)
  --     else (f i) = 0
  -- }

end TestFunctions

-- (R : outParam (Type v)) (D : outParam (Type w)) (e : outParam (R → Domain → ℝ))
-- (R : Type u) (D : Type v) (e : R → Domain → ℝ)
open TestFunctions in
class SemiHilbert (X) extends Vec X, TestFunctions X 
  -- semi_inner_add : ∀ (x y z : X) Ω,      ⟪x + y, z⟫[Ω] = ⟪x, z⟫[Ω] + ⟪y, z⟫[Ω]
  -- semi_inner_mul : ∀ (x y : X) (r : ℝ) Ω,  ⟪r*x, y⟫[Ω] = r*⟪x, y⟫[Ω]
  -- semi_inner_sym : ∀ (x y : X) Ω,            ⟪x, y⟫[Ω] = ⟪y, x⟫[Ω]
  -- semi_inner_pos : ∀ (x : X) Ω,            (⟪x, x⟫[Ω]) ≥ (0 : ℝ)
  -- semi_inner_ext : ∀ (x : X),
  --   ((x = 0) ↔ (∀ Ω (ϕ : X) (h : testFunction Ω ϕ), ⟪x, ϕ⟫[Ω] = 0))
  -- semi_inner_gtr : ∀ (x ϕ : X) (Ω Ω' : 𝓓 X), 
  --   testFunction Ω ϕ → Ω < Ω' → ⟪x, ϕ⟫[Ω'] = ⟪x, ϕ⟫[Ω]
  -- Maybe that {ϕ // testFunction Ω ϕ} form a vector space

-- class Hilbert (X) extends SemiHilbert X, UniqueDomain X
                                     
namespace SemiHilbert 

  open TestFunctions

  instance : SemiHilbert ℝ := 
  {
    -- semi_inner_add := sorry
    -- semi_inner_mul := sorry
    -- semi_inner_sym := sorry
    -- semi_inner_pos := sorry
    -- semi_inner_ext := sorry
    -- semi_inner_gtr := sorry
  }

  instance (X Y) [SemiHilbert X] [SemiHilbert Y] 
    : SemiHilbert (X × Y) := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
    semi_inner_gtr := sorry
  }


  instance (X) [SemiHilbert X] (ι) [Enumtype ι] 
    : SemiHilbert (ι → X) := 
  {
    semi_inner_add := sorry
    semi_inner_mul := sorry
    semi_inner_sym := sorry
    semi_inner_pos := sorry
    semi_inner_ext := sorry
    semi_inner_gtr := sorry
  }


end SemiHilbert
