import Mathlib.Analysis.InnerProductSpace.Basic
import SciLean.Core.Objects.Vec
import SciLean.Core.Objects.Scalar
import SciLean.Core.NotationOverField

import SciLean.Data.EnumType

namespace SciLean

open IsROrC ComplexConjugate

/-- Square of L₂ norm over the field `K` -/
class Norm2 (K X : Type _) where
  norm2 : X → K

instance [Inner K X] : Norm2 K X where
  norm2 x := Inner.inner x x

notation "‖" x "‖₂²[" K "]" => @Norm2.norm2 K _ _ x

def norm₂ (K : Type _) {R X : Type _} [Scalar R K] [Norm2 K X] (x : X) : K := Scalar.sqrt (Norm2.norm2 x)

notation "‖" x "‖₂[" K "]" => norm₂ K x

@[simp]
theorem norm₂_squared_nat {R K X : Type _} [Scalar R K] [Norm2 K X] (x : X)
  : ‖x‖₂[K] ^ 2 = ‖x‖₂²[K] := by sorry_proof

@[simp]
theorem norm₂_squared {R K X : Type _} [Scalar R K] [Norm2 K X] (x : X)
  : ‖x‖₂[K] ^ (2:K) = ‖x‖₂²[K] := by sorry_proof

section Inner

notation "⟪" x ", " y "⟫[" K "]" => @Inner.inner K _ _ x y

namespace NotationOverField

scoped elab "‖" x:term "‖₂²" : term => do
  let fieldName ← currentFieldName.get
  let K := Lean.mkIdent fieldName
  Lean.Elab.Term.elabTerm (← `(@Norm2.norm2 $K _ _ $x)) none

@[app_unexpander Norm2.norm2] def unexpandNorm2 : Lean.PrettyPrinter.Unexpander
  | `($(_) $x) => `(‖ $x ‖₂²)
  | _ => throw ()

scoped elab "‖" x:term "‖₂" : term => do
  let fieldName ← currentFieldName.get
  let K := Lean.mkIdent fieldName
  Lean.Elab.Term.elabTerm (← `(norm₂ $K $x)) none

@[app_unexpander norm₂] def unexpandNorm₂ : Lean.PrettyPrinter.Unexpander
  | `($(_) K $x) => `(‖ $x ‖₂)
  | _ => throw ()

scoped elab "⟪" x:term ", " y:term "⟫" : term => do
  let fieldName ← currentFieldName.get
  let K := Lean.mkIdent fieldName
  Lean.Elab.Term.elabTerm (← `(@Inner.inner $K _ _ $x $y)) none

@[app_unexpander Inner.inner] def unexpandInner : Lean.PrettyPrinter.Unexpander
  | `($(_) $x $y) => `(⟪$x, $y⟫)
  | _ => throw ()

end NotationOverField


instance (K X Y) [AddCommMonoid K] [Inner K X] [Inner K Y] : Inner K (X × Y) where
  inner := λ (x,y) (x',y') => ⟪x,x'⟫[K] + ⟪y,y'⟫[K]

-- instance (K X) [AddCommMonoid K] [Inner K X] (ι) [Fintype ι] : Inner K (ι → X) where
--   inner := λ f g => ∑ i, ⟪f i, g i⟫[K]

-- instance (K X) [AddCommMonoid K] [Inner K X] (ι) [EnumType ι] : Inner K (ι → X) where
--   inner := λ f g => EnumType.sum fun i => ⟪f i, g i⟫[K]

instance (priority:=low) (K ι) (X : ι → Type _) 
  [AddCommMonoid K] [∀ i, Inner K (X i)] [EnumType ι] 
  : Inner K ((i : ι) → X i) where
  inner := λ f g => ∑ i, ⟪f i, g i⟫[K]

end Inner

section TestFunctions 

/-- TestFunctions defines a subset of well behaved elemets w.r.t. to the inner product. 
For example:
  1. test function on `ℕ → ℝ` are sequences with only finitely many non-zero elements
  2. test function on `C∞(ℝ, ℝ)` are functions with compact support

see `SemiInnerProductSpace` for more information
-/
class TestFunctions (X : Type _) where
  TestFunction : Set X

export TestFunctions (TestFunction)

instance (X Y) [TestFunctions X] [TestFunctions Y] : TestFunctions (X×Y) where
  TestFunction xy := TestFunction xy.1 ∧ TestFunction xy.2

-- instance (X ι : Type _) [TestFunctions X]  : TestFunctions (ι → X) where
--   TestFunction f := ∀ i, TestFunction (f i)

instance (priority:=low) (ι : Type _) (X : ι → Type _) [∀ i, TestFunctions (X i)]
  : TestFunctions ((i : ι) → X i) where
  TestFunction f := ∀ i, TestFunction (f i)

end TestFunctions 


/-- SemiInnerProductSpace is almost InnerProductSpace but `⟪x,y⟫` does not make 
sense for all elements `x y : X`. For example, `C∞(ℝ, ℝ)` or `ℕ → ℝ` are almost 
inner product spaces but `∫ x : ℝ, f x * g x` or `∑ i : ℕ, a i * b i` are not 
meaningful for all `f, g` or `a, b`. Therefore we introduce notion of test functions
and `⟪x, φ⟫` has meaning only when `φ` is test function, `x` can be arbitrary.

The important property is that deciding if an element is zero, `x = 0`, can be
determined by testing `⟪x, ϕ⟫[K] = 0` for all test functions `φ`. This is known 
as fundamental lemma of the calculus of variations.
https://en.wikipedia.org/wiki/Fundamental_lemma_of_the_calculus_of_variations

This also allows a definition of adjoint between two semi-inner product spaces, see `semiAdjoint`.
-/
class SemiInnerProductSpace (K : Type _) [IsROrC K] (X : Type _) extends Vec K X, Inner K X, TestFunctions X, Norm2 K X where
  add_left : ∀ (x y z : X), (TestFunction x ∧ TestFunction y) ∨ TestFunction z →
    ⟪x + y, z⟫[K] = ⟪x, z⟫[K] + ⟪y, z⟫[K]
  smul_left : ∀ (x y : X) (r : K),   -- I thinkg here we do not need `TestFunction x ∨ TestFunction y`
    ⟪r • x, y⟫[K] = conj r * ⟪x, y⟫[K]
  conj_sym : ∀ (x y : X),            -- I thinkg here we do not need `TestFunction x ∨ TestFunction y`
    conj ⟪y, x⟫[K] = ⟪x, y⟫[K]
  inner_pos : ∀ (x : X), TestFunction x →
    IsROrC.re ⟪x, x⟫[K] ≥ (0 : ℝ) ∧ IsROrC.im ⟪x, x⟫[K] = 0
  inner_ext : ∀ (x : X),
    ((x = 0) ↔ (∀ (ϕ : X), TestFunction ϕ → ⟪x, ϕ⟫[K] = 0))
  is_lin_subspace : VecProp K (X:=X) TestFunction
  inner_norm2 : ∀ (x : X), ⟪x, x⟫[K] = ‖x‖₂²[K]

  inner_with_testfun_is_continuous : ∀ ϕ, TestFunction ϕ → Continuous (⟪·, ϕ⟫[K])

  -- inner_ext does imply `TestFunction x → x ≠ 0 → ⟪x,x⟫ > 0`
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

/-- Almost Hilbert space but does not have to be complete. It is only c∞-complete.

The important property is that the norm `‖x‖₂` and inner product `⟪x,y⟫` is meaningful for any `x y : X`. For general semi-inner prodcut space the norm and inner product is well defined only for `x ∈ TestFunction`-/
class SemiHilbert (K : Type _) [IsROrC K] (X : Type _) extends SemiInnerProductSpace K X where
  test_functions_true : ∀ x, TestFunction x

variable {K} [IsROrC K]

instance {K} [IsROrC K] : Inner K K where
  inner x y := conj x * y

instance [IsROrC K] : TestFunctions K where
  TestFunction _ := True

instance : SemiInnerProductSpace K K where
  add_left := by simp[Inner.inner, add_mul]
  smul_left := by simp[Inner.inner, mul_assoc]
  conj_sym := by simp[Inner.inner,mul_comm]
  inner_pos := by sorry_proof
  inner_ext := 
    by 
      simp[Inner.inner, TestFunction]; 
      intro x
      constructor
      intro h; simp[h]
      intro h; have q := h 1; induction q; (case mpr.inl => assumption); (case mpr.inr _ => sorry_proof)
  is_lin_subspace := sorry_proof
  inner_norm2 := by simp[Norm2.norm2]
  inner_with_testfun_is_continuous := by simp[Inner.inner]; continuity

instance : SemiHilbert K K where
  test_functions_true := by simp[TestFunction]

instance {K} [IsROrC K] : Inner K Unit where
  inner _ _ := 0

instance [IsROrC K] : TestFunctions Unit where
  TestFunction _ := True

instance : SemiInnerProductSpace K Unit where
  add_left := by simp[Inner.inner]
  smul_left := by simp[Inner.inner]
  conj_sym := by simp[Inner.inner]
  inner_pos := by simp[Inner.inner]
  inner_ext := by simp[Inner.inner, TestFunction]; 
  is_lin_subspace := by constructor <;> simp[TestFunction]
  inner_norm2 := by simp[Norm2.norm2, Inner.inner]
  inner_with_testfun_is_continuous := by simp[Inner.inner]; continuity

instance : SemiHilbert K Unit where
  test_functions_true := by simp[TestFunction]

-- Complete InnerProductSpace is SemiInnerProductSpace
instance (priority:=low) [IsROrC K] [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  : SemiInnerProductSpace K X where
  scalar_wise_smooth := by sorry_proof
  TestFunction _ := True
  add_left := by sorry_proof
  smul_left := by sorry_proof
  conj_sym := by sorry_proof
  inner_pos := by sorry_proof
  inner_ext := by sorry_proof
  is_lin_subspace := by sorry_proof
  inner_norm2 := by simp[Norm2.norm2]
  inner_with_testfun_is_continuous := by simp[Inner.inner]; continuity

abbrev SemiInnerProductSpace.mkSorryProofs {α} [Vec K α] [Inner K α] [TestFunctions α] : SemiInnerProductSpace K α
  := SemiInnerProductSpace.mk sorry_proof sorry_proof sorry_proof sorry_proof sorry_proof sorry_proof sorry_proof sorry_proof

instance (X Y) [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] : SemiInnerProductSpace K (X × Y) := SemiInnerProductSpace.mkSorryProofs
instance (X Y) [SemiHilbert K X] [SemiHilbert K Y] : SemiHilbert K (X × Y) where
  test_functions_true := by intro (x,y); simp[TestFunction]; constructor <;> apply SemiHilbert.test_functions_true

-- instance (X) [SemiInnerProductSpace K X] (ι) [Fintype ι] : SemiInnerProductSpace K (ι → X) := SemiInnerProductSpace.mkSorryProofs
-- instance (X) [SemiInnerProductSpace K X] (ι) [EnumType ι] : SemiInnerProductSpace K (ι → X) := SemiInnerProductSpace.mkSorryProofs
instance (ι) (X : ι → Type _) [∀ i, SemiInnerProductSpace K (X i)] [EnumType ι] : SemiInnerProductSpace K ((i : ι) → X i) 
  := SemiInnerProductSpace.mkSorryProofs

instance (ι) (X : ι → Type _) [∀ i, SemiHilbert K (X i)] [EnumType ι] : SemiHilbert K ((i : ι) → X i) where
  test_functions_true := by simp[TestFunction]; intro f i; apply SemiHilbert.test_functions_true

