import SciLean.Data.PowType.Basic

import SciLean.Algebra

namespace SciLean.PowType

variable (X : Type) (n m : USize) [PowType X]

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

instance [SemiInner X] : SemiInner (X^n) :=
{
  Domain := 𝓓 X
  domain := default
  semiInner := λ x y Ω => ∑ i, ⟪x[i], y[i]⟫[Ω]
  testFunction := λ _ _ => True
}

instance [SemiHilbert X] : SemiHilbert (X^n) :=
{
  semi_inner_add := sorry
  semi_inner_mul := sorry
  semi_inner_sym := sorry
  semi_inner_pos := sorry
  semi_inner_ext := sorry
  semi_inner_gtr := sorry
}

instance [Hilbert X] : Hilbert (X^n) :=
{
  uniqueDomain := sorry
}

