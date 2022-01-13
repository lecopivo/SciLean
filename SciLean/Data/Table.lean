import SciLean.Categories
import SciLean.Mathlib.Data.Table

namespace SciLean

open Table

variable {C : Type u} [Trait C] [Table C (Index C) (Value C)] [Table.Intro C]

-- Vector Space
instance [AddSemigroup (Value C)] : AddSemigroup C := AddSemigroup.mk sorry
instance [AddMonoid (Value C)]    : AddMonoid C    := AddMonoid.mk sorry sorry nsmul_rec sorry sorry
instance [AddCommMonoid (Value C)] : AddCommMonoid C := AddCommMonoid.mk sorry
instance [SubNegMonoid (Value C)] : SubNegMonoid C := SubNegMonoid.mk sorry gsmul_rec sorry sorry sorry
instance [AddGroup (Value C)]     : AddGroup C     := AddGroup.mk sorry
instance [AddCommGroup (Value C)] : AddCommGroup C := AddCommGroup.mk sorry

instance [Monoid β] [MulAction β (Value C)] : MulAction β C := MulAction.mk sorry sorry
instance {M} [AddMonoid (Value C)] [Monoid M] [DistribMulAction M (Value C)] : DistribMulAction M C := DistribMulAction.mk sorry sorry
instance {R} [AddCommGroup (Value C)] [Semiring R] [Module R (Value C)] : Module R C := Module.mk sorry sorry

set_option synthInstance.maxHeartbeats 5000
instance [Vec (Value C)] : Vec C := Vec.mk
set_option synthInstance.maxHeartbeats 500


open Table in
instance {C} [Trait C] [Table C (Index C) (Value C)] [Enumtype (Index C)] 
  [SemiInner (Value C) ℝ Unit (λ r _ => r)]
  : SemiInner C ℝ Unit (λ r _ => r) :=
{
  semiInner := λ x y => (∑ i, ⟪x[i], y[i]⟫)
  testFunction := λ _ _ => True
}

open Table in
instance {C} [Trait C] [Table C (Index C) (Value C)] [Enumtype (Index C)] [Intro C]
  [Hilbert (Value C)]
  : Hilbert C :=
{
  semi_inner_add := sorry
  semi_inner_mul := sorry
  semi_inner_sym := sorry
  semi_inner_pos := sorry
  semi_inner_ext := sorry
}
 
