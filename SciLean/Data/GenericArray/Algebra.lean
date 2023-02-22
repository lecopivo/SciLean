import SciLean.Data.GenericArray.Basic

namespace SciLean 
namespace GenericArray

variable {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam}
variable [GenericArray Cont Idx Elem] [Enumtype Idx] 

-- The above instance is giving problems in the following examples.
-- TOOD: investigate
example {X} [Vec X] : HMul ℝ X X := by infer_instance
-- This one can't be stated here, but gets messed up by the above instance
-- example : ∀ (i : Idx), IsSmooth λ (x : Cont) => ∥x[i]∥² := by infer_instance -- apply λ

-- instance (priority := low) [AddCommGroup Elem] [DistribMulAction ℝ Elem] : Vec Cont := Vec.mk
instance (priority := low) [Vec Elem] : Vec Cont := Vec.mkSorryProofs -- Vec.mk

instance (priority := low) [Inner Elem] : Inner Cont where
  inner := λ f g => ∑ x, ⟪f[x], g[x]⟫

instance (priority := low) [Vec Elem] [TestFunctions Elem] 
  : TestFunctions Cont where
  TestFun f := ∀ x, TestFun (f[x])

instance (priority := low) [SemiHilbert Elem] 
  : SemiHilbert Cont := SemiHilbert.mkSorryProofs

instance (priority := low) [Hilbert Elem] 
  : Hilbert Cont where
  all_are_test := sorry_proof

instance (priority := low) {κ} {_ : Enumtype κ} [FinVec Elem κ] : Basis Cont (Idx×κ) ℝ where
  basis := λ (i,j) => introElem λ i' => [[i=i']] * 𝕖[Elem] j
  proj := λ (i,j) x => 𝕡 j x[i]

instance (priority := low) {κ} {_ : Enumtype κ} [FinVec Elem κ] : DualBasis Cont (Idx×κ) ℝ where
  dualBasis := λ (i,j) => introElem λ i' => [[i=i']] * 𝕖'[Elem] j
  dualProj := λ (i,j) x => 𝕡' j x[i]

instance (priority := low) {κ : Type} {_ : Enumtype κ} [FinVec Elem κ] : FinVec Cont (Idx×κ) where
  is_basis := sorry_proof
  duality := by intro (i,j) (i',j'); simp[Inner.inner,Basis.basis, DualBasis.dualBasis]; sorry_proof




