import SciLean.Mathlib.Data.Enumtype

import SciLean.Algebra.VectorSpace

namespace SciLean

class Inner (X : Type u) where  
  inner : X → X → ℝ

namespace Inner

  notation "⟪" x ", " y "⟫" => Inner.inner x y

  def normSqr {X} [Inner X] (x : X) := ⟪x, x⟫
  def norm {X} [Inner X] (x : X) := Math.sqrt (normSqr x)

  notation "∥" x "∥²" => normSqr x
  notation "∥" x "∥" => norm x

end Inner

structure VecSubspace {X} [Vec X] (V : X → Prop) : Prop where
  zero : V 0
  add : ∀ x y, V x → V y → V (x + y)
  smul : ∀ (s : ℝ) x, V x → V (s * x)

class TestFunctions (X : Type u) [Vec X] where
  TestFun : X → Prop
  is_lin_subspace : VecSubspace TestFun

export TestFunctions (TestFun)

open Inner in
class SemiHilbert (X) extends Vec X, Inner X, TestFunctions X where
  inner_add : ∀ (x y z : X), (TestFun x ∧ TestFun y) ∨ TestFun z → 
    ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
  inner_mul : ∀ (x y : X) (r : ℝ), TestFun x ∨ TestFun y →
    ⟪r*x, y⟫ = r*⟪x, y⟫
  inner_sym : ∀ (x y : X), TestFun x ∨ TestFun y →
    ⟪x, y⟫ = ⟪y, x⟫
  inner_pos : ∀ (x : X), TestFun x →
    ⟪x, x⟫ ≥ (0 : ℝ)
  inner_ext : ∀ (x : X),
    ((x = 0) ↔ (∀ (ϕ : X), TestFun ϕ → ⟪x, ϕ⟫ = 0))

class Hilbert (X) extends SemiHilbert X where
  all_are_test : ∀ x : X, TestFun x
                                     
--- Reals

instance : Inner ℝ where
  inner x y := x * y 

instance : TestFunctions ℝ where
  TestFun x := True
  is_lin_subspace := sorry

instance : SemiHilbert ℝ where
  inner_add := sorry
  inner_mul := sorry
  inner_sym := sorry
  inner_pos := sorry
  inner_ext := sorry

instance : Hilbert ℝ where
  all_are_test := sorry

-- Product space

instance (X Y) [Inner X] [Inner Y] : Inner (X × Y) where
  inner := λ (x,y) (x',y') => ⟪x,x'⟫ + ⟪y,y'⟫

instance (X Y) [Vec X] [Vec Y] [TestFunctions X] [TestFunctions Y] : TestFunctions (X×Y) where
  TestFun xy := TestFun xy.1 ∧ TestFun xy.2
  is_lin_subspace := sorry

instance (X Y) [SemiHilbert X] [SemiHilbert Y] : SemiHilbert (X × Y) where
  inner_add := sorry
  inner_mul := sorry
  inner_sym := sorry
  inner_pos := sorry
  inner_ext := sorry

instance (X Y) [Hilbert X] [Hilbert Y] : Hilbert (X × Y) where
  all_are_test := sorry

-- Function type

instance (X) [Inner X] (ι) [Enumtype ι] : Inner (ι → X) where
  inner := λ f g => ∑ i, ⟪f i, g i⟫

instance (X) [Vec X] [TestFunctions X] (ι) [Enumtype ι] : TestFunctions (ι → X) where
  TestFun f := ∀ i, TestFun (f i)
  is_lin_subspace := sorry

instance (X) [SemiHilbert X] (ι) [Enumtype ι] 
  : SemiHilbert (ι → X) where
  inner_add := sorry
  inner_mul := sorry
  inner_sym := sorry
  inner_pos := sorry
  inner_ext := sorry

instance (X) [Hilbert X] (ι) [Enumtype ι] 
  : Hilbert (ι → X) where
  all_are_test := sorry

