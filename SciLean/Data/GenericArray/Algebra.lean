import SciLean.Data.GenericArray.Basic

namespace SciLean 
namespace GenericArray

variable {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam}
variable [GenericArray Cont Idx Elem] [Enumtype Idx] 

instance (priority := low) [AddSemigroup Elem]  : AddSemigroup Cont  := AddSemigroup.mk sorry_proof
instance (priority := low) [AddMonoid Elem]     : AddMonoid Cont     := AddMonoid.mk sorry_proof sorry_proof nsmulRec sorry_proof sorry_proof
instance (priority := low) [AddCommMonoid Elem] : AddCommMonoid Cont := AddCommMonoid.mk sorry_proof
instance (priority := low) [SubNegMonoid Elem]  : SubNegMonoid Cont  := SubNegMonoid.mk sorry_proof zsmulRec sorry_proof sorry_proof sorry_proof
instance (priority := low) [AddGroup Elem]      : AddGroup Cont      := AddGroup.mk sorry_proof
instance (priority := low) [AddCommGroup Elem]  : AddCommGroup Cont  := AddCommGroup.mk sorry_proof

instance (priority := low) [MulAction ℝ Elem] : MulAction ℝ Cont := MulAction.mk sorry_proof sorry_proof
local instance (priority := low) [AddMonoid Elem] [DistribMulAction ℝ Elem] : DistribMulAction ℝ Cont := DistribMulAction.mk sorry_proof sorry_proof

local instance (priority := low-1) [AddCommMonoid Elem] [DistribMulAction ℝ Elem] : Module ℝ Cont := Module.mk sorry_proof sorry_proof
-- The above instance is giving problems in the following examples.
-- TOOD: investigate
example {X} [Vec X] : HMul ℝ X X := by infer_instance
-- This one can't be stated here, but gets messed up by the above instance
-- example : ∀ (i : Idx), IsSmooth λ (x : Cont) => ∥x[i]∥² := by infer_instance -- apply λ

-- instance (priority := low) [AddCommGroup Elem] [DistribMulAction ℝ Elem] : Vec Cont := Vec.mk
instance (priority := low) [Vec Elem] : Vec Cont := Vec.mk

instance (priority := low) [Inner Elem] : Inner Cont where
  inner := λ f g => ∑ x, ⟪f[x], g[x]⟫

instance (priority := low) [Vec Elem] [TestFunctions Elem] 
  : TestFunctions Cont where
  TestFun f := ∀ x, TestFun (f[x])
  is_lin_subspace := sorry_proof

instance (priority := low) [SemiHilbert Elem] 
  : SemiHilbert Cont where
  inner_add := sorry_proof
  inner_mul := sorry_proof
  inner_sym := sorry_proof
  inner_pos := sorry_proof
  inner_ext := sorry_proof

instance (priority := low) [Hilbert Elem] 
  : Hilbert Cont where
  all_are_test := sorry_proof
