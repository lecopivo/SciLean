import SciLean.Data.FunType.Basic

namespace SciLean 
namespace FunType

  -- set_option trace.Meta.synthInstance true in
  -- set_option synthInstance.maxHeartbeats 5000 in
  -- example (x : ℝ) : IsSmooth fun (f : ℝ⟿ℝ) => ∂ f x := by infer_instance

  -- #check  @SciLean.differential

  -- set_option trace.Meta.synthInstance true in
  -- example {X} [Vec X] : IsSmooth fun (x : X) => (SciLean.differential : (X → X) → X → X → X) := by infer_instance
  -- -- SciLean.LinMap.mk.arg_x.isSmooth
  -- example : ∀ (x : { f : ℝ → ℝ // SciLean.IsLin f }), IsSmooth fun (f : ℝ⟿ℝ) => x.val := by infer_instance

variable (T X Y : Type) [FunType T X Y] [HasSet T] [HasIntro T] [Enumtype X] 

instance (priority := low) [AddSemigroup Y]  : AddSemigroup T  := AddSemigroup.mk sorry
instance (priority := low) [AddMonoid Y]     : AddMonoid T     := AddMonoid.mk sorry sorry nsmul_rec sorry sorry
instance (priority := low) [AddCommMonoid Y] : AddCommMonoid T := AddCommMonoid.mk sorry
instance (priority := low) [SubNegMonoid Y]  : SubNegMonoid T  := SubNegMonoid.mk sorry gsmul_rec sorry sorry sorry
instance (priority := low) [AddGroup Y]      : AddGroup T      := AddGroup.mk sorry
instance (priority := low) [AddCommGroup Y]  : AddCommGroup T  := AddCommGroup.mk sorry

instance (priority := low) [MulAction ℝ Y] : MulAction ℝ T := MulAction.mk sorry sorry
local instance (priority := low) [AddMonoid Y] [DistribMulAction ℝ Y] : DistribMulAction ℝ T := DistribMulAction.mk sorry sorry

local instance (priority := low-1) [AddCommMonoid Y] [DistribMulAction ℝ Y] : Module ℝ T := Module.mk sorry sorry
-- The above instance is giving problems in the following examples.
-- TOOD: investigate
example {X} [Vec X] : HMul ℝ X X := by infer_instance
-- This one can't be stated here, but gets messed up by the above instance
-- example : ∀ (i : X), IsSmooth λ (x : T) => ∥x[i]∥² := by infer_instance -- apply λ

-- instance (priority := low) [AddCommGroup Y] [DistribMulAction ℝ Y] : Vec T := Vec.mk
instance (priority := low) [Vec Y] : Vec T := Vec.mk

instance (priority := low) [SemiInner Y] : SemiInner T :=
{
  Domain := 𝓓 Y
  domain := default
  semiInner := λ f g Ω => ∑ x, ⟪f[x], g[x]⟫[Ω]
  testFunction := λ _ _ => True
}

instance (priority := low) [SemiHilbert Y] : SemiHilbert T :=
{
  semi_inner_add := sorry
  semi_inner_mul := sorry
  semi_inner_sym := sorry
  semi_inner_pos := sorry
  semi_inner_ext := sorry
  semi_inner_gtr := sorry
}

instance (priority := low) [Hilbert Y] : Hilbert T :=
{
  uniqueDomain := sorry
}
