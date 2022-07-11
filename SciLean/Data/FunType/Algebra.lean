import SciLean.Data.FunType.Basic

namespace SciLean 
namespace FunType

variable (T X Y : Type) [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] [Inhabited Y]

instance [AddSemigroup Y]  : AddSemigroup T  := AddSemigroup.mk sorry
instance [AddMonoid Y]     : AddMonoid T     := AddMonoid.mk sorry sorry nsmul_rec sorry sorry
instance [AddCommMonoid Y] : AddCommMonoid T := AddCommMonoid.mk sorry
instance [SubNegMonoid Y]  : SubNegMonoid T  := SubNegMonoid.mk sorry gsmul_rec sorry sorry sorry
instance [AddGroup Y]      : AddGroup T      := AddGroup.mk sorry
instance [AddCommGroup Y]  : AddCommGroup T  := AddCommGroup.mk sorry

instance [MulAction ℝ Y] : MulAction ℝ T := MulAction.mk sorry sorry
instance [AddMonoid Y] [DistribMulAction ℝ Y] : DistribMulAction ℝ T := DistribMulAction.mk sorry sorry

instance (priority := low) [AddCommMonoid Y] [DistribMulAction ℝ Y] : Module ℝ T := Module.mk sorry sorry
-- The above instance is giving problems in the following example.
-- TOOD: investigate
example {X} [Vec X] : HMul ℝ X X := by infer_instance

instance [AddCommGroup Y] [DistribMulAction ℝ Y] : Vec T := Vec.mk

instance [SemiInner Y] : SemiInner T :=
{
  Domain := 𝓓 Y
  domain := default
  semiInner := λ f g Ω => ∑ x, ⟪toFun f x, toFun g x⟫[Ω]
  testFunction := λ _ _ => True
}

instance [SemiHilbert Y] : SemiHilbert T :=
{
  semi_inner_add := sorry
  semi_inner_mul := sorry
  semi_inner_sym := sorry
  semi_inner_pos := sorry
  semi_inner_ext := sorry
  semi_inner_gtr := sorry
}

instance [Hilbert Y] : Hilbert T :=
{
  uniqueDomain := sorry
}
