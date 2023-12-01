import SciLean.Core.Objects.FinVec
import SciLean.Data.ArrayType.Basic
import SciLean.Data.StructType.Algebra

namespace SciLean 
namespace GenericArrayType

variable {Cont : Type _} {Idx : Type _ |> outParam} {Elem : Type _ |> outParam}
variable [EnumType Idx] 

variable {K : Type _} [IsROrC K]

instance (priority := low) [ArrayType Cont Idx Elem] [TopologicalSpace Elem] : TopologicalSpace Cont where
  IsOpen := fun A => ∀ i, IsOpen (fun x : Elem => ∃ a ∈ A, a[i]=x)
  isOpen_univ := sorry_proof
  isOpen_inter := sorry_proof
  isOpen_sUnion := sorry_proof

noncomputable
instance (priority := low) [ArrayType Cont Idx Elem] [UniformSpace Elem] : UniformSpace Cont where
  uniformity := sorry_data
  refl := sorry_proof
  symm := sorry_proof
  comp := sorry_proof
  isOpen_uniformity := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [UniformSpace Elem] [CompleteSpace Elem] : CompleteSpace Cont where
  complete := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [AddGroup Elem] : AddCommGroup Cont where
  sub_eq_add_neg := sorry_proof
  add_comm  := sorry_proof
  add_assoc := sorry_proof
  zero_add  := sorry_proof
  add_zero  := sorry_proof
  add_left_neg := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [Vec K Elem] : Vec K Cont where
  continuous_add := sorry_proof
  continuous_neg := sorry_proof
  one_smul := sorry_proof
  mul_smul := sorry_proof
  smul_zero := sorry_proof
  smul_add := sorry_proof
  add_smul := sorry_proof
  zero_smul := sorry_proof
  continuous_smul := sorry_proof
  scalar_wise_smooth := sorry_proof


instance (priority := low) [ArrayType Cont Idx Elem] [Inner K Elem] : Inner K Cont where
  inner := λ f g => ∑ x, ⟪f[x], g[x]⟫[K]

instance (priority := low) [ArrayType Cont Idx Elem] [Vec K Elem] [TestFunctions Elem] 
  : TestFunctions Cont where
  TestFunction x := ∀ i, TestFunction (x[i])

-- noncomputable
-- instance (priority := low) [ArrayType Cont Idx Elem] [NormedAddCommGroup Elem] 
--   : NormedAddCommGroup Cont where
--   norm := fun x => (∑ i, ‖x[i]‖^2).sqrt
--   dist_self := sorry_proof
--   dist_comm := sorry_proof
--   dist_triangle := sorry_proof
--   edist_dist := sorry_proof
--   eq_of_dist_eq_zero := sorry_proof

-- instance (priority := low) [ArrayType Cont Idx Elem] [NormedAddCommGroup Elem] [NormedSpace K Elem] 
--   : NormedSpace K Cont where
--   one_smul := sorry_proof
--   mul_smul := sorry_proof
--   smul_zero := sorry_proof
--   smul_add := sorry_proof
--   add_smul := sorry_proof
--   zero_smul := sorry_proof
--   norm_smul_le := sorry_proof

-- instance (priority := low) [ArrayType Cont Idx Elem] [NormedAddCommGroup Elem] [InnerProductSpace K Elem] 
--   : InnerProductSpace K Cont where
--   norm_sq_eq_inner := sorry_proof
--   conj_symm := sorry_proof
--   add_left := sorry_proof
--   smul_left := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [SemiInnerProductSpace K Elem] 
  : SemiInnerProductSpace K Cont where
  add_left := sorry_proof
  smul_left := sorry_proof
  conj_sym := sorry_proof
  inner_pos := sorry_proof
  inner_ext := sorry_proof
  is_lin_subspace := sorry_proof
  inner_with_testfun_is_continuous := sorry_proof
  inner_norm2 := by simp[Norm2.norm2]

instance (priority := low) [ArrayType Cont Idx Elem] [SemiHilbert K Elem] 
  : SemiHilbert K Cont where
  test_functions_true := by simp[TestFunction]; intros; apply SemiHilbert.test_functions_true

instance (priority := low) [ArrayType Cont Idx K] : Basis Idx K Cont where
  basis := λ i => introElem λ i' => (if i = i' then 1 else 0)
  proj := λ i x => x[i]

instance (priority := low) [ArrayType Cont Idx K] : DualBasis Idx K Cont where
  dualBasis := λ i => introElem λ i' => (if i = i' then 1 else 0)
  dualProj := λ i x => x[i]

open BasisDuality in
instance (priority := low) [ArrayType Cont Idx K] : BasisDuality Cont where
  toDual   := fun x => x
  fromDual := fun x => x

-- instance (priority := low) [ArrayType Cont Idx K] : FinVec Idx K Cont where
--   is_basis := sorry_proof
--   duality := by intro (i) (i'); simp[Inner.inner,Basis.basis, DualBasis.dualBasis]; sorry_proof
--   to_dual := sorry_proof
--   from_dual := sorry_proof


-- -- These instances might cause problems
-- instance (priority := low-1) [ArrayType Cont Idx Elem] {κ} [Index κ] [FinVec κ K Elem] : Basis (Idx×κ) K Cont where
--   basis := λ (i,j) => introElem λ i' => (if i = i' then ⅇ[Elem] j else 0)
--   proj := λ (i,j) x => ℼ j x[i]

-- instance (priority := low-1) [ArrayType Cont Idx Elem] {κ} [Index κ] [FinVec κ K Elem] : DualBasis (Idx×κ) K Cont where
--   dualBasis := λ (i,j) => introElem λ i' => (if i = i' then ⅇ'[Elem] j else 0)
--   dualProj := λ (i,j) x => ℼ' j x[i]

-- open BasisDuality in
-- instance (priority := low-1) [ArrayType Cont Idx Elem] {κ} [Index κ] [FinVec κ K Elem] : BasisDuality Cont where
--   toDual   := ArrayType.map toDual
--   fromDual := ArrayType.map fromDual

-- instance (priority := low-1) [ArrayType Cont Idx Elem] {κ} [Index κ] [FinVec κ K Elem] : FinVec (Idx×κ) K Cont where
--   is_basis := sorry_proof
--   duality := by intro (i) (i'); simp[Inner.inner,Basis.basis, DualBasis.dualBasis]; sorry_proof
--   to_dual := sorry_proof
--   from_dual := sorry_proof

-- This is causing issues to synthesize `Vec Cont` from `Vec Elem`
-- instance (priority := low-2) {κ : Type} {_ : Index κ} [FinVec Elem κ] : FinVec Cont (Idx×κ) where
--   is_basis := sorry_proof
--   duality := by intro (i,j) (i',j'); simp[Inner.inner,Basis.basis, DualBasis.dualBasis]; sorry_proof
--   to_dual := sorry_proof
--   from_dual := sorry_proof



instance [ArrayType Cont Idx Elem] [Zero Elem] : ZeroStruct Cont Idx (fun _ => Elem) where
  structProj_zero := by intro i; simp[OfNat.ofNat,Zero.zero,ArrayType.introElem_structMake]

instance [ArrayType Cont Idx Elem] [Add Elem] : AddStruct Cont Idx (fun _ => Elem) where
  structProj_add := by intro i; simp[HAdd.hAdd, Add.add,ArrayType.introElem_structMake, ← ArrayType.getElem_structProj]

instance {K} [ArrayType Cont Idx Elem] [SMul K Elem] : SMulStruct K Cont Idx (fun _ => Elem) where
  structProj_smul := by intro i k x; simp[HSMul.hSMul, SMul.smul,ArrayType.introElem_structMake, ← ArrayType.getElem_structProj]

instance {K} [IsROrC K] [ArrayType Cont Idx Elem] [Vec K Elem] : VecStruct K Cont Idx (fun _ => Elem) where
  structProj_continuous := sorry_proof
  structMake_continuous := sorry_proof

instance {K} [IsROrC K] [ArrayType Cont Idx Elem] [SemiInnerProductSpace K Elem] : SemiInnerProductSpaceStruct K Cont Idx (fun _ => Elem) where
  inner_structProj := sorry_proof
  testFun_structProj := sorry_proof
