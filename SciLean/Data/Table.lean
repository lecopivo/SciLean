import SciLean.Categories
import SciLean.Mathlib.Data.Table

namespace SciLean

variable {C : Type u} {ι : Type v} {α : Type w} [Table C ι α] [Table.Intro C]

-- Vector Space
instance [AddSemigroup α] : AddSemigroup C := AddSemigroup.mk sorry
instance [AddMonoid α]    : AddMonoid C    := AddMonoid.mk sorry sorry nsmul_rec sorry sorry
instance [SubNegMonoid α] : SubNegMonoid C := SubNegMonoid.mk sorry gsmul_rec sorry sorry sorry
instance [AddGroup α]     : AddGroup C     := AddGroup.mk sorry
instance [AddCommGroup α] : AddCommGroup C := AddCommGroup.mk sorry

instance [Monoid β] [MulAction β α] : MulAction β C := MulAction.mk sorry sorry
instance {M} [AddMonoid α] [Monoid M] [DistribMulAction M α] : DistribMulAction M C := DistribMulAction.mk sorry sorry
instance {R} [AddCommGroup α] [Semiring R] [Module R α] : Module R C := Module.mk sorry sorry

set_option synthInstance.maxHeartbeats 5000
instance [Vec α] : Vec C := Vec.mk
set_option synthInstance.maxHeartbeats 500


open Table in
instance {C} [Trait C] [Table C (Index C) (Value C)] [Enumtype (Index C)] 
  [SemiInner (Value C) ℝ Unit (λ r _ => r)]
  : SemiInner C ℝ Unit (λ r _ => r) :=
{
  semiInner := λ x y => (∑ i, ⟪x[i], y[i]⟫)
  testFunction := λ _ _ => True
}

