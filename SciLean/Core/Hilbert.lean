import SciLean.Mathlib.Data.Enumtype

import SciLean.Core.Vec

namespace SciLean

class Inner (X : Type) where  
  inner : X → X → ℝ

namespace Inner

  notation "⟪" x ", " y "⟫" => Inner.inner x y

  def normSqr {X} [Inner X] (x : X) := ⟪x, x⟫
  def norm {X} [Inner X] (x : X) := (normSqr x).sqrt

  notation "∥" x "∥²" => normSqr x
  notation "∥" x "∥" => norm x

end Inner

class TestFunctions (X : Type) where
  TestFun : X → Prop

export TestFunctions (TestFun)


-- All elements of a Convenient Hilbert space are test functions
-- I think that inner_mul and inner_sym do not need to assume TestFun on x or y
-- because ⟪r*x, y⟫ or ⟪y,x⟫ is meaningulf iff ⟪x,y⟫ is
-- We are mainly interested if this holds for integrals i.e. when ⟪f, g⟫ = ∫ x, f x * g x
class SemiHilbert (X) extends Vec X, Inner X, TestFunctions X where
  inner_add : ∀ (x y z : X), TestFun x ∧ TestFun y ∧ TestFun z →
    ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
  inner_mul : ∀ (x y : X) (r : ℝ),
    ⟪r*x, y⟫ = r*⟪x, y⟫
  inner_sym : ∀ (x y : X),
    ⟪x, y⟫ = ⟪y, x⟫
  inner_pos : ∀ (x : X), TestFun x →
    ⟪x, x⟫ ≥ (0 : ℝ)
  inner_ext : ∀ (x : X),
    ((x = 0) ↔ (∀ (ϕ : X), TestFun ϕ → ⟪x, ϕ⟫ = 0))
  is_lin_subspace : VecProp (X:=X) TestFun

  -- Maybe add this? Can we prove it or do we need to assume it?
  -- Is this true on (ℝ ⟿ ℝ)? It should be otherwise I'm questioning everything.
  -- inner_with_testfun_is_smooth : ∀ ϕ, TestFun ϕ → IsSmooth ⟪·, ϕ⟫     

  -- inner_ext does imply `TestFun x → x ≠ 0 → ⟪x,x⟫ > 0`
  -- Let ϕ s.t. ⟪x,ϕ⟫ > 0, let (ε > 0)
  --  ⟪x - ε * ϕ, x - ε * ϕ⟫ = ⟪x,x⟫ - 2*ε*⟪x,ϕ⟫ + ε²*⟪ϕ,ϕ⟫ ≥ 0
  --  ⟪x,x⟫ ≥ 2*ε*⟪x,ϕ⟫ - ε²*⟪ϕ,ϕ⟫
  -- For sufficiently small ε we have
  --  0 < 2*ε*⟪x,ϕ⟫ - ε²*⟪ϕ,ϕ⟫ ≤ ⟪x,x⟫

  -- Inner product is not a smooth function function on (ℝ ⟿ ℝ)
  -- Take a smooth path γ t := ϕ t * λ x ⟿ 1 / sqrt (x*x + 1)
  -- where `ϕ : ℝ → ℝ` is a smooth bumb function that is non zero only on [-1,1]
  -- Then:
  --   1. ∀ t ∈ (-1,1),     ⟪γ t, γ t⟫ = ∞
  --   2. ∀ t ∈ ℝ \ (-1,1), ⟪γ t, γ t⟫ = 0


-- Can we prove that `⟪·, ·⟫` is smooth function? Or do we need to assume it?
class Hilbert (X) extends SemiHilbert X where
  all_are_test : ∀ x : X, TestFun x
                                     

def SemiHilbert.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] [HMul ℝ α α] [Inner α] [TestFunctions α] : SemiHilbert α
  := SemiHilbert.mk (toVec := Vec.mkSorryProofs) sorry_proof sorry_proof sorry_proof sorry_proof sorry_proof sorry_proof

def Hilbert.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] [HMul ℝ α α] [Inner α] [TestFunctions α] : Hilbert α
  := Hilbert.mk (toSemiHilbert := SemiHilbert.mkSorryProofs) sorry_proof

--- Reals

instance : Inner ℝ where
  inner x y := x * y 

instance : TestFunctions ℝ where
  TestFun x := True

instance : Hilbert ℝ := Hilbert.mkSorryProofs

-- Product space

instance (X Y) [Inner X] [Inner Y] : Inner (X × Y) where
  inner := λ (x,y) (x',y') => ⟪x,x'⟫ + ⟪y,y'⟫

instance (X Y) [Vec X] [Vec Y] [TestFunctions X] [TestFunctions Y] : TestFunctions (X×Y) where
  TestFun xy := TestFun xy.1 ∧ TestFun xy.2

instance (X Y) [SemiHilbert X] [SemiHilbert Y] : SemiHilbert (X × Y) := SemiHilbert.mkSorryProofs
instance (X Y) [Hilbert X] [Hilbert Y] : Hilbert (X × Y) := Hilbert.mkSorryProofs

-- Function type

instance (X) [Inner X] (ι) [Enumtype ι] : Inner (ι → X) where
  inner := λ f g => ∑ i, ⟪f i, g i⟫

instance (X) [Vec X] [TestFunctions X] (ι) [Enumtype ι] : TestFunctions (ι → X) where
  TestFun f := ∀ i, TestFun (f i)

instance (X) [SemiHilbert X] (ι) [Enumtype ι] : SemiHilbert (ι → X) := SemiHilbert.mkSorryProofs
instance (X) [Hilbert X] (ι) [Enumtype ι] : Hilbert (ι → X) := Hilbert.mkSorryProofs
