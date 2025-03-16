import SciLean.Algebra.TensorProduct.Basic

import SciLean.Algebra.TensorProduct.BlockMatrixCol
import SciLean.Algebra.TensorProduct.BlockMatrixRow
import SciLean.Algebra.TensorProduct.BlockMatrix

namespace SciLean

variable (R : Type*) [RCLike R]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace R Y]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X]
  {YX : Type*} [AddCommGroup YX] [Module R YX] [TensorProductType R Y X YX]
  {I nI} [IdxType I nI] [IdxType.Fold' I] [IdxType.Fold' I]
  {J nJ} [IdxType J nJ] [IdxType.Fold' J] [IdxType.Fold' J]


-- todo: convert to `structure` to preven defeq abuse
abbrev IndexedMatrixCol (I M : Type*) := I → M
abbrev IndexedMatrixRow (I M : Type*) := I → M
abbrev IndexedMatrix (I J M : Type*) := I → J → M

-- instance : NormedAddCommGroup (IndexedMatrixCol I X) := by unfold IndexedMatrixCol; infer_instance
-- instance : AdjointSpace R (IndexedMatrixCol I X) := by unfold IndexedMatrixCol; infer_instance

-- instance : NormedAddCommGroup (IndexedMatrixRow I X) := by unfold IndexedMatrixRow; infer_instance
-- instance : AdjointSpace R (IndexedMatrixRow I X) := by unfold IndexedMatrixRow; infer_instance

-- instance : NormedAddCommGroup (IndexedMatrix I J X) := by unfold IndexedMatrix; infer_instance
-- instance : AdjointSpace R (IndexedMatrix I J X) := by unfold IndexedMatrix; infer_instance

open TensorProductType

instance : TensorProductType R (I → Y) X (IndexedMatrixCol I YX) where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd := fun r y x A i => tmulAdd r (y i) x (A i)
  matVecMul := fun a A x b y i => matVecMul a (A i) x b (y i)
  matHVecMul := fun a A y b x => ∑ᴵ i, matHVecMul a (A i) (y i) b x
  tmulAdd_eq_tmul := sorry_proof

instance [TensorProductGetYX R Y X YX] : TensorProductGetYX R (I → Y) X (IndexedMatrixCol I YX) := ⟨⟩
instance [TensorProductGetY R Y X YX] : TensorProductGetY R (I → Y) X (IndexedMatrixCol I YX) := ⟨⟩
instance [TensorProductGetX R Y X YX] : TensorProductGetX R (I → Y) X (IndexedMatrixCol I YX) := ⟨⟩

instance : TensorProductType R Y (I → X) (IndexedMatrixRow I YX) where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd := fun r y x A i => tmulAdd r y (x i) (A i)
  matVecMul := fun a A x b y => ∑ᴵ i, matVecMul a (A i) (x i) b y
  matHVecMul := fun a A y b x i => matHVecMul a (A i) y b (x i)
  tmulAdd_eq_tmul := sorry_proof

instance [TensorProductGetYX R Y X YX] : TensorProductGetYX R Y (I → X) (IndexedMatrixRow I YX) := ⟨⟩
instance [TensorProductGetY R Y X YX] : TensorProductGetY R Y (I → X) (IndexedMatrixRow I YX) := ⟨⟩
instance [TensorProductGetX R Y X YX] : TensorProductGetX R Y (I → X) (IndexedMatrixRow I YX) := ⟨⟩


instance : TensorProductType R (I → Y) (J → X) (IndexedMatrix I J YX) where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd := fun r y x A i j => tmulAdd r (y i) (x j) (A i j)
  matVecMul := fun a A x b y i => ∑ᴵ j, matVecMul a (A i j) (x j) b (y i)
  matHVecMul := fun a A y b x i => ∑ᴵ j, matHVecMul a (A j i) (y j) b (x i)
  tmulAdd_eq_tmul := sorry_proof

instance [TensorProductGetYX R Y X YX] : TensorProductGetYX R (I → Y) (J → X) (IndexedMatrix I J YX) := ⟨⟩
instance [TensorProductGetY R Y X YX] : TensorProductGetY R (I → Y) (J → X) (IndexedMatrix I J YX) := ⟨⟩
instance [TensorProductGetX R Y X YX] : TensorProductGetX R (I → Y) (J → X) (IndexedMatrix I J YX) := ⟨⟩
