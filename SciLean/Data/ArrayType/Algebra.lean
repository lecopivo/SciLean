import SciLean.Core.Objects.FinVec
import SciLean.Data.ArrayType.Basic
import SciLean.Data.StructType.Algebra
import SciLean.Core.FloatAsReal


import SciLean.Mathlib.Analysis.AdjointSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

import SciLean.Mathlib.Analysis.MetricSpace

open LeanColls

namespace SciLean
namespace ArrayType

variable {Cont : Type _} {Idx : Type _ |> outParam} {Elem : Type _ |> outParam}
variable {Idx : Type _} [IndexType Idx] [LawfulIndexType Idx] [DecidableEq Idx]

variable {K : Type _} [RCLike K]

instance (priority := low) [ArrayType Cont Idx Elem] [TopologicalSpace Elem] : TopologicalSpace Cont where
  IsOpen := fun A => ∀ i, IsOpen (fun x : Elem => ∃ a ∈ A, a[i]=x)
  isOpen_univ := sorry_proof
  isOpen_inter := sorry_proof
  isOpen_sUnion := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [UniformSpace Elem] : UniformSpace Cont where
  uniformity := default --sorry_proof
  nhds_eq_comap_uniformity := sorry_proof
  symm := sorry_proof
  comp := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [UniformSpace Elem] [CompleteSpace Elem] : CompleteSpace Cont where
  complete := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [AddGroup Elem] : AddGroup Cont where
  sub_eq_add_neg := sorry_proof
  add_assoc := sorry_proof
  zero_add  := sorry_proof
  add_zero  := sorry_proof
  add_left_neg := sorry_proof
  nsmul n x := ArrayType.mapMono (fun xi => n • xi) x
  nsmul_succ := sorry_proof
  nsmul_zero := sorry_proof
  zsmul n x := ArrayType.mapMono (fun xi => n • xi) x
  zsmul_succ' := sorry_proof
  zsmul_neg' := sorry_proof
  zsmul_zero' := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [AddCommGroup Elem] : AddCommGroup Cont where
  add_comm  := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [UniformSpace Elem] [AddGroup Elem] [UniformAddGroup Elem] : UniformAddGroup Cont where
  uniformContinuous_sub := sorry_proof


instance (priority := low) [ArrayType Cont Idx Elem] [TopologicalSpace R] [TopologicalSpace Elem] [SMul R Elem] [ContinuousSMul R Elem] : ContinuousSMul R Cont where
  continuous_smul := sorry_proof


instance (priority := low) {R} [CommSemiring R] [ArrayType Cont Idx Elem] [AddCommGroup Elem] [Module R Elem] : Module R Cont where
  one_smul := sorry_proof
  mul_smul := sorry_proof
  smul_zero := sorry_proof
  smul_add := sorry_proof
  add_smul := sorry_proof
  zero_smul := sorry_proof

open FiniteDimensional IndexType in
@[simp, ftrans_simp]
theorem array_type_finrank {R} [CommSemiring R] [ArrayType Cont Idx Elem] [AddCommGroup Elem] [Module R Elem] :
    finrank R Cont = card Idx * finrank R Elem := sorry_proof

instance (priority := low) {S R} [SMul S Elem] [SMul R Elem] [SMul S R] [IsScalarTower S R Elem]
    [ArrayType Cont Idx Elem] : IsScalarTower S R Cont where
  smul_assoc := by intros; ext; simp

instance (priority := low) [ArrayType Cont Idx Elem] [Vec K Elem] : Vec K Cont where
  scalar_wise_smooth := sorry_proof
  continuous_smul := sorry_proof


instance (priority := low) [ArrayType Cont Idx Elem] [Inner K Elem] : Inner K Cont where
  inner := λ f g => ∑ x, ⟪f[x], g[x]⟫[K]

instance (priority := low) [ArrayType Cont Idx Elem] [Vec K Elem] [TestFunctions Elem] :
    TestFunctions Cont where
  TestFunction x := ∀ i, TestFunction (x[i])


noncomputable
instance (priority := low) {p} [ArrayType Cont Idx Elem] [Dist (WithLp p Elem)] :
    Dist (WithLp p Cont) where
  dist := fun x y =>
    let x := WithLp.equiv _ _ x
    let y := WithLp.equiv _ _ y
    (∑ i, (distP p x[i] y[i])^p.toReal)^(1/p.toReal)

instance (priority := low) [ArrayType Cont Idx Elem] [Dist Elem] :
    Dist Cont where
  dist := fun x y =>
    let x := (∑ i, (dist x[i] y[i])^2)
    let y := Scalar.ofReal Float x -- this ugliness it to dodge noncomputable checker
    Scalar.toReal Float y

noncomputable
instance (priority := low) [ArrayType Cont Idx Elem] [MetricSpace (WithLp p Elem)] :
    MetricSpace (WithLp p Cont) where
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  edist_dist := sorry_proof
  uniformity_dist := sorry_proof
  cobounded_sets := sorry_proof
  eq_of_dist_eq_zero := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [NormedAddCommGroup Elem] :
    NormedAddCommGroup Cont where
  norm := fun x =>
    let x := ∑ i, ‖x[i]‖^2
    let y := Scalar.ofReal Float x  -- this ugliness it to dodge noncomputable checker
    Scalar.toReal Float y
  dist_eq := by simp[dist,NormedAddCommGroup.dist_eq]
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  edist_dist := sorry_proof
  eq_of_dist_eq_zero := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [NormedAddCommGroup Elem] [NormedSpace K Elem] :
    NormedSpace K Cont where
  one_smul := sorry_proof
  mul_smul := sorry_proof
  smul_zero := sorry_proof
  smul_add := sorry_proof
  add_smul := sorry_proof
  zero_smul := sorry_proof
  norm_smul_le := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [NormedAddCommGroup Elem] [AdjointSpace K Elem] :
    AdjointSpace K Cont where
  inner_top_equiv_norm := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [NormedAddCommGroup Elem] [InnerProductSpace K Elem] :
    InnerProductSpace K Cont where
  norm_sq_eq_inner := sorry_proof
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof

instance (priority := low) [ArrayType Cont Idx Elem] [SemiInnerProductSpace K Elem] :
    SemiInnerProductSpace K Cont where
  uniformContinuous_sub := sorry_proof
  continuous_smul := sorry_proof
  scalar_wise_smooth := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof
  conj_sym := sorry_proof
  inner_pos := sorry_proof
  inner_ext := sorry_proof
  is_lin_subspace := sorry_proof
  inner_with_testfun_is_continuous := sorry_proof
  inner_norm2 := by simp[Norm2.norm2]

instance (priority := low) [ArrayType Cont Idx Elem] [SemiHilbert K Elem] :
    SemiHilbert K Cont where
  test_functions_true := by simp[TestFunction]; intros; apply SemiHilbert.test_functions_true

instance (priority := low) [ArrayType Cont Idx K] : Basis Idx K Cont where
  basis := λ i => Indexed.ofFn fun i' => (if i = i' then 1 else 0)
  proj := λ i x => x[i]

instance (priority := low) [ArrayType Cont Idx K] : DualBasis Idx K Cont where
  dualBasis := λ i => Indexed.ofFn fun i' => (if i = i' then 1 else 0)
  dualProj := λ i x => x[i]

open BasisDuality in
instance (priority := low) [ArrayType Cont Idx K] : BasisDuality Cont where
  toDual   := fun x => x
  fromDual := fun x => x

instance [ArrayType Cont Idx K] : OrthonormalBasis Idx K Cont where
  is_orthogonal := sorry_proof
  is_orthonormal := sorry_proof

instance (priority := low) [ArrayType Cont Idx K] : FinVec Idx K Cont where
  is_basis := sorry_proof
  duality := by intro (i) (i'); simp[Inner.inner,Basis.basis, DualBasis.dualBasis]; sorry_proof
  to_dual := sorry_proof
  from_dual := sorry_proof


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
  structProj_zero := by intro i; simp[OfNat.ofNat,Zero.zero]

instance [ArrayType Cont Idx Elem] [Add Elem] : AddStruct Cont Idx (fun _ => Elem) where
  structProj_add := by intro i; simp[HAdd.hAdd, Add.add]

instance {K} [ArrayType Cont Idx Elem] [SMul K Elem] : SMulStruct K Cont Idx (fun _ => Elem) where
  structProj_smul := by intro i k x; simp[HSMul.hSMul, SMul.smul]

instance {K} [RCLike K] [ArrayType Cont Idx Elem] [Vec K Elem] : VecStruct K Cont Idx (fun _ => Elem) where
  structProj_zero := sorry_proof
  structProj_add := sorry_proof
  structProj_smul := sorry_proof
  structProj_continuous := sorry_proof
  structMake_continuous := sorry_proof

instance {K} [RCLike K] [ArrayType Cont Idx Elem] [SemiInnerProductSpace K Elem] : SemiInnerProductSpaceStruct K Cont Idx (fun _ => Elem) where
  inner_structProj := sorry_proof
  testFun_structProj := sorry_proof



-- TODO: provide proper measurable structure by
--       translating measurable structure from product type
instance [ArrayType Cont Idx Elem] [MeasurableSpace Elem] : MeasurableSpace Cont where
  MeasurableSet' := fun _ => True
  measurableSet_empty := sorry_proof
  measurableSet_compl := sorry_proof
  measurableSet_iUnion := sorry_proof

-- TODO: provide proper measurable structure by
--       translating measurable structure from product type
open MeasureTheory in
instance [ArrayType Cont Idx Elem] [MeasureSpace Elem] : MeasureSpace Cont where
  volume := {
    measureOf := fun _ => 0
    empty := sorry_proof
    mono := sorry_proof
    iUnion_nat := sorry_proof
    m_iUnion := sorry_proof
    trim_le := sorry_proof
}

open MeasureTheory in
instance [ArrayType Cont Idx Elem] [MeasurableSpace Elem] [TopologicalSpace Elem] [BorelSpace Elem] :
    BorelSpace Cont where
  measurable_eq := sorry_proof



-- This is problem as `Vec` and `NormedAddCommGroup` provide different topologie on `Elem`
-- example {R} [RCLike R] [ArrayType Cont Idx Elem] [NormedAddCommGroup Elem] [NormedSpace ℝ Elem] [Vec R Elem] :
--   (PseudoEMetricSpace.toUniformSpace : UniformSpace Cont)
--   =
--   (Vec.toUniformSpace R : UniformSpace Cont) := by rfl
