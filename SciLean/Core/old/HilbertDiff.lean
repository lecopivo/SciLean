import SciLean.Core.Diff
import SciLean.Core.Hilbert

namespace SciLean

/-- Diffeological space with SemiHilbert structure on the tangent space

  TODO: Add some smoothness condition such that we can differentiate inner product
    However, this requires parallel transport!
  -/
@[reducible]
class SemiHilbertDiff (X : Type) extends Diff X where
  [instInnerTS : ∀ x, Inner (𝒯[x] X)]
  [instTestFunctionsTS : ∀ x, TestFunctions (𝒯[x] X)]
  inner_add : ∀ (x' : X) (x y z : 𝒯[x'] X), TestFun x ∧ TestFun y ∧ TestFun z →
    ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫
  inner_mul : ∀ (x' : X) (x y : 𝒯[x'] X) (r : ℝ),
    ⟪r•x, y⟫ = r*⟪x, y⟫
  inner_sym : ∀ (x' : X) (x y : 𝒯[x'] X),
    ⟪x, y⟫ = ⟪y, x⟫
  inner_pos : ∀ (x' : X) (x : 𝒯[x'] X), TestFun x →
    ⟪x, x⟫ ≥ (0 : ℝ)
  inner_ext : ∀ (x' : X) (x : 𝒯[x'] X),
    ((x = 0) ↔ (∀ (ϕ : 𝒯[x'] X), TestFun ϕ → ⟪x, ϕ⟫ = 0))
  is_lin_subspace : ∀ x', VecProp (X:=𝒯[x'] X) TestFun

attribute [reducible]
  SemiHilbertDiff.instInnerTS
  SemiHilbertDiff.instTestFunctionsTS
  SemiHilbertDiff.toDiff

@[reducible]
instance (priority:=low) (X : Type) [SemiHilbert X] : SemiHilbertDiff X :=
{
  inner_add := λ _ => SemiHilbert.inner_add
  inner_mul := λ _ => SemiHilbert.inner_mul
  inner_sym := λ _ => SemiHilbert.inner_sym
  inner_pos := λ _ => SemiHilbert.inner_pos
  inner_ext := λ _ => SemiHilbert.inner_ext
  is_lin_subspace := λ _ => SemiHilbert.is_lin_subspace
}

@[reducible]
instance (X) [SemiHilbertDiff X] (x : X) : SemiHilbert (𝒯[x] X) :=
{
  inner_add := SemiHilbertDiff.inner_add x
  inner_mul := SemiHilbertDiff.inner_mul x
  inner_sym := SemiHilbertDiff.inner_sym x
  inner_pos := SemiHilbertDiff.inner_pos x
  inner_ext := SemiHilbertDiff.inner_ext x
  is_lin_subspace := SemiHilbertDiff.is_lin_subspace x
}

@[reducible]
instance SemiHilbertDiff_of_Prod
  (X) [SemiHilbertDiff X] (Y) [SemiHilbertDiff Y]
  : SemiHilbertDiff (X×Y) :=
{
  inner_add := λ _ => SemiHilbert.inner_add
  inner_mul := λ _ => SemiHilbert.inner_mul
  inner_sym := λ _ => SemiHilbert.inner_sym
  inner_pos := λ _ => SemiHilbert.inner_pos
  inner_ext := λ _ => SemiHilbert.inner_ext
  is_lin_subspace := λ _ => SemiHilbert.is_lin_subspace
}

@[reducible]
instance SemiHilbertDiff_of_funType
  {ι : Type} [Enumtype ι]
  (X) [SemiHilbertDiff X]
  : SemiHilbertDiff (ι → X) :=
{
  inner_add := λ _ => SemiHilbert.inner_add
  inner_mul := λ _ => SemiHilbert.inner_mul
  inner_sym := λ _ => SemiHilbert.inner_sym
  inner_pos := λ _ => SemiHilbert.inner_pos
  inner_ext := λ _ => SemiHilbert.inner_ext
  is_lin_subspace := λ _ => SemiHilbert.is_lin_subspace
}

@[reducible]
instance SemiHilbertDiff_of_Sum (X) [SemiHilbertDiff X] (Y) [SemiHilbertDiff Y]
  : SemiHilbertDiff (X⊕Y) :=
{
  inner_add := λ xy => match xy with | .inl _ => SemiHilbert.inner_add | .inr _ => SemiHilbert.inner_add
  inner_mul := λ xy => match xy with | .inl _ => SemiHilbert.inner_mul | .inr _ => SemiHilbert.inner_mul
  inner_sym := λ xy => match xy with | .inl _ => SemiHilbert.inner_sym | .inr _ => SemiHilbert.inner_sym
  inner_pos := λ xy => match xy with | .inl _ => SemiHilbert.inner_pos | .inr _ => SemiHilbert.inner_pos
  inner_ext := λ xy => match xy with | .inl _ => SemiHilbert.inner_ext | .inr _ => SemiHilbert.inner_ext
  is_lin_subspace := λ xy => match xy with | .inl _ => SemiHilbert.is_lin_subspace | .inr _ => SemiHilbert.is_lin_subspace
}


--------------------------------------------------------------------------------


@[reducible]
class HilbertDiff (X : Type) extends SemiHilbertDiff X where
  all_are_test : ∀ (x : X) (dx : 𝒯[x] X), TestFun dx

attribute [reducible] HilbertDiff.toSemiHilbertDiff

@[reducible]
instance (priority:=low) (X : Type) [Hilbert X] : HilbertDiff X := ⟨λ _ => Hilbert.all_are_test⟩

@[reducible]
instance (X) [HilbertDiff X] (x : X) : Hilbert (𝒯[x] X) where
  all_are_test := HilbertDiff.all_are_test x

@[reducible]
instance instHilbertDiffProd
  (X) [HilbertDiff X] (Y) [HilbertDiff Y]
  : HilbertDiff (X×Y) := ⟨λ _ => Hilbert.all_are_test⟩

@[reducible]
instance instHilbertDiffForAll
  {ι : Type} [Enumtype ι]
  (X) [HilbertDiff X]
  : HilbertDiff (ι → X) := ⟨λ _ => Hilbert.all_are_test⟩

@[reducible]
instance isntHilbertDiffSum (X) [HilbertDiff X] (Y) [HilbertDiff Y]
  : HilbertDiff (X⊕Y) :=
  ⟨λ xy => match xy with | .inl _ => Hilbert.all_are_test | .inr _ => Hilbert.all_are_test⟩
