import SciLean.Mathlib.Data.PowType
-- import SciLean.Algebra
import SciLean.Categories
import SciLean.Operators


namespace SciLean.PowType

variable (X : Type) (n m : Nat) [PowType X n]

instance [AddSemigroup X]  : AddSemigroup (X^n)  := AddSemigroup.mk sorry
instance [AddMonoid X]     : AddMonoid (X^n)     := AddMonoid.mk sorry sorry nsmul_rec sorry sorry
instance [AddCommMonoid X] : AddCommMonoid (X^n) := AddCommMonoid.mk sorry
instance [SubNegMonoid X]  : SubNegMonoid (X^n)  := SubNegMonoid.mk sorry gsmul_rec sorry sorry sorry
instance [AddGroup X]      : AddGroup (X^n)      := AddGroup.mk sorry
instance [AddCommGroup X]  : AddCommGroup (X^n)  := AddCommGroup.mk sorry

instance [MulAction ℝ X] : MulAction ℝ (X^n) := MulAction.mk sorry sorry
instance [AddMonoid X] [DistribMulAction ℝ X] : DistribMulAction ℝ (X^n) := DistribMulAction.mk sorry sorry
instance [AddCommMonoid X] [DistribMulAction ℝ X] : Module ℝ (X^n) := Module.mk sorry sorry

instance [AddCommGroup X] [DistribMulAction ℝ X] : Vec (X^n) := Vec.mk

instance {R D e} [SemiInner X R D e] [Zero R] [Add R] : SemiInner (X^n) R D e :=
{
  semiInner := λ x y => ∑ i, ⟪x[i], y[i]⟫
  testFunction := λ _ _ => True
}

@[inferTCGoalsRL]
instance {R D e} [Vec R] [SemiHilbert X R D e] : SemiHilbert (X^n) R D e :=
{
  semi_inner_add := sorry
  semi_inner_mul := sorry
  semi_inner_sym := sorry
  semi_inner_pos := sorry
  semi_inner_ext := sorry
}

variable [Vec X]

instance (i : Fin n)  : IsLin (λ c : X^n => c[i]) := sorry
instance : IsLin (λ (c : X^n) (i : Fin n)  => c[i]) := sorry



variable {R D e} [Vec R] [SemiHilbert X R D e]

instance 
  : HasAdjoint (λ (c : X^n) (i : Fin n) => c[i]) := sorry

instance (i : Fin n)
  : HasAdjoint (λ c : X^n => c[i]) := sorry

@[simp]                         
theorem adjoint_of_powtype_get
  : (λ (c : X^n) i => c[i])† = PowType.intro := sorry
