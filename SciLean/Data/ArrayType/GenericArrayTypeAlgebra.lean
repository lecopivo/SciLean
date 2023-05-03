import SciLean.Core
import SciLean.Data.ArrayType.GenericArrayType

namespace SciLean 
namespace GenericArrayType

variable {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam}
variable [GenericArrayType Cont Idx Elem] [Index Idx] 

-- The above instance is giving problems in the following examples.
-- TOOD: investigate
example {X} [Vec X] : SMul ℝ X := by infer_instance
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

instance (priority := low-1) {κ} {_ : Index κ} [FinVec Elem κ] : Basis Cont (Idx×κ) ℝ where
  basis := λ (i,j) => introElem λ i' => [[i=i']] • 𝕖[Elem] j
  proj := λ (i,j) x => 𝕡 j x[i]

set_option synthInstance.checkSynthOrder false in
instance (priority := low) instBasisReal [FinVec Elem Unit] : Basis Cont (Idx) ℝ where
  basis := λ i => introElem λ i' => [[i=i']] • 𝕖[Elem] ()
  proj := λ i x => 𝕡 () x[i]

instance (priority := low-1) {κ} {_ : Index κ} [FinVec Elem κ] : DualBasis Cont (Idx×κ) ℝ where
  dualBasis := λ (i,j) => introElem λ i' => [[i=i']] • 𝕖'[Elem] j
  dualProj := λ (i,j) x => 𝕡' j x[i]

set_option synthInstance.checkSynthOrder false in
instance (priority := low) instDualBasisReal [FinVec Elem Unit] : DualBasis Cont Idx ℝ where
  dualBasis := λ i => introElem λ i' => [[i=i']] • 𝕖'[Elem] ()
  dualProj := λ i x => 𝕡' () x[i]

open BasisDuality in
instance (priority := low) {κ} {_ : Index κ} [FinVec Elem κ] : BasisDuality Cont where
  toDual   := GenericArrayType.map toDual
  fromDual := GenericArrayType.map fromDual

set_option synthInstance.checkSynthOrder false in
instance (priority := low) [FinVec Elem Unit] : FinVec Cont Idx where
  is_basis := sorry_proof
  duality := by intro (i) (i'); simp[Inner.inner,Basis.basis, DualBasis.dualBasis]; sorry_proof
  to_dual := sorry_proof
  from_dual := sorry_proof

instance (priority := low-1) {κ : Type} {_ : Index κ} [FinVec Elem κ] : FinVec Cont (Idx×κ) where
  is_basis := sorry_proof
  duality := by intro (i,j) (i',j'); simp[Inner.inner,Basis.basis, DualBasis.dualBasis]; sorry_proof
  to_dual := sorry_proof
  from_dual := sorry_proof



