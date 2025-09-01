import SciLean.Algebra.TensorProduct.Basic
import SciLean.Algebra.TensorProduct.Self

import SciLean.Algebra.TensorProduct.ProdMatrixCol
import SciLean.Algebra.TensorProduct.ProdMatrixRow
import SciLean.Algebra.TensorProduct.ProdMatrix

namespace SciLean

variable (R : Type*) [RCLike R]
  {Y₁ : Type*} [NormedAddCommGroup Y₁] [AdjointSpace R Y₁]
  {X₁ : Type*} [NormedAddCommGroup X₁] [AdjointSpace R X₁]

  {Y₂ : Type*} [NormedAddCommGroup Y₂] [AdjointSpace R Y₂]
  {X₂ : Type*} [NormedAddCommGroup X₂] [AdjointSpace R X₂]

  {YX₁₁ : Type*} [AddCommGroup YX₁₁] [Module R YX₁₁] [TensorProductType R Y₁ X₁ YX₁₁]
  {YX₁₂ : Type*} [AddCommGroup YX₁₂] [Module R YX₁₂] [TensorProductType R Y₁ X₂ YX₁₂]
  {YX₂₁ : Type*} [AddCommGroup YX₂₁] [Module R YX₂₁] [TensorProductType R Y₂ X₁ YX₂₁]
  {YX₂₂ : Type*} [AddCommGroup YX₂₂] [Module R YX₂₂] [TensorProductType R Y₂ X₂ YX₂₂]


open TensorProductType in
instance (priority:=low) : TensorProductType R (Y₁ × Y₂) X₁ (ProdMatrixCol YX₁₁ YX₂₁) where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd := fun r ⟨y₁,y₂⟩ x ⟨A₁,A₂⟩ =>
    ⟨tmulAdd r y₁ x A₁, tmulAdd r y₂ x A₂⟩
  matVecMulAdd := fun a ⟨A₁,A₂⟩ x b ⟨y₁,y₂⟩ =>
    ⟨matVecMulAdd a A₁ x b y₁, matVecMulAdd a A₂ x b y₂⟩
  vecMatMulAdd := fun a ⟨A₁,A₂⟩ ⟨y₁,y₂⟩ b x =>
    vecMatMulAdd a A₂ y₂ 1 (vecMatMulAdd a A₁ y₁ b x)
  tmulAdd_eq_tmul := sorry_proof

instance [TensorProductGetYX R Y₁ X₁ YX₁₁] [TensorProductGetYX R Y₂ X₁ YX₂₁] :
  TensorProductGetYX R (Y₁ × Y₂) X₁ (ProdMatrixCol YX₁₁ YX₂₁) := ⟨⟩
instance [TensorProductGetY R Y₁ X₁ YX₁₁] [TensorProductGetY R Y₂ X₁ YX₂₁] :
  TensorProductGetY R (Y₁ × Y₂) X₁ (ProdMatrixCol YX₁₁ YX₂₁) := ⟨⟩
instance [TensorProductGetX R Y₁ X₁ YX₁₁] [TensorProductGetX R Y₂ X₁ YX₂₁] :
  TensorProductGetX R (Y₁ × Y₂) X₁ (ProdMatrixCol YX₁₁ YX₂₁) := ⟨⟩


open TensorProductType in
instance (priority:=low) : TensorProductType R Y₁ (X₁ × X₂) (ProdMatrixRow YX₁₁ YX₁₂) where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd := fun r y ⟨x₁,x₂⟩ ⟨A₁,A₂⟩ =>
    ⟨tmulAdd r y x₁ A₁, tmulAdd r y x₂ A₂⟩
  matVecMulAdd := fun a ⟨A₁,A₂⟩ ⟨x₁,x₂⟩ b y =>
    matVecMulAdd a A₂ x₂ b (matVecMulAdd a A₁ x₁ b y)
  vecMatMulAdd := fun a y ⟨A₁,A₂⟩ b ⟨x₁,x₂⟩ =>
    ⟨vecMatMulAdd a y A₁ 1 x₁, vecMatMulAdd a y A₂ b x₂⟩
  tmulAdd_eq_tmul := sorry_proof

instance [TensorProductGetYX R Y₁ X₁ YX₁₁] [TensorProductGetYX R Y₁ X₂ YX₁₂] :
  TensorProductGetYX R Y₁ (X₁ × X₂) (ProdMatrixRow YX₁₁ YX₁₂) := ⟨⟩
instance [TensorProductGetY R Y₁ X₁ YX₁₁] [TensorProductGetY R Y₁ X₂ YX₁₂] :
  TensorProductGetY R Y₁ (X₁ × X₂) (ProdMatrixRow YX₁₁ YX₁₂) := ⟨⟩
instance [TensorProductGetX R Y₁ X₁ YX₁₁] [TensorProductGetX R Y₁ X₂ YX₁₂] :
  TensorProductGetX R Y₁ (X₁ × X₂) (ProdMatrixRow YX₁₁ YX₁₂) := ⟨⟩


-- open TensorProductType in
-- instance : TensorProductType R (Y₁ × Y₂) (X₁ × X₂) (ProdMatrix YX₁₁ YX₁₂ YX₂₁ YX₂₂) where
--   equiv := ⟨fun _ => True, sorry_proof⟩
--   tmulAdd := fun r ⟨y₁,y₂⟩ ⟨x₁,x₂⟩ ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ =>
--     {
--       A₁₁ := tmulAdd r y₁ x₁ A₁₁
--       A₁₂ := tmulAdd r y₁ x₂ A₁₂
--       A₂₁ := tmulAdd r y₂ x₁ A₂₁
--       A₂₂ := tmulAdd r y₂ x₂ A₂₂
--     }
--   matVecMulAdd := fun a ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ ⟨x₁,x₂⟩ b ⟨y₁,y₂⟩ =>
--     {
--       fst := matVecMulAdd a A₁₁ x₁ b (matVecMulAdd a A₁₂ x₂ b y₁)
--       snd := matVecMulAdd a A₂₁ x₁ b (matVecMulAdd a A₂₂ x₂ b y₂)
--     }
--   vecMatMulAdd := fun a ⟨y₁,y₂⟩ ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ b ⟨x₁,x₂⟩ =>
--     {
--       fst := vecMatMulAdd a y₁ A₁₁ b (vecMatMulAdd a y₂ A₂₁ b x₁)
--       snd := vecMatMulAdd a y₁ A₁₂ b (vecMatMulAdd a y₂ A₂₂ b x₂)
--     }
--   tmulAdd_eq_tmul := sorry_proof

-- instance
--   [TensorProductGetYX R Y₁ X₁ YX₁₁] [TensorProductGetYX R Y₁ X₂ YX₁₂]
--   [TensorProductGetYX R Y₂ X₁ YX₂₁] [TensorProductGetYX R Y₂ X₂ YX₂₂] :
--   TensorProductGetYX R (Y₁ × Y₂) (X₁ × X₂) (ProdMatrix YX₁₁ YX₁₂ YX₂₁ YX₂₂) := ⟨⟩
-- instance
--   [TensorProductGetY R Y₁ X₁ YX₁₁] [TensorProductGetY R Y₁ X₂ YX₁₂]
--   [TensorProductGetY R Y₂ X₁ YX₂₁] [TensorProductGetY R Y₂ X₂ YX₂₂] :
--   TensorProductGetY R (Y₁ × Y₂) (X₁ × X₂) (ProdMatrix YX₁₁ YX₁₂ YX₂₁ YX₂₂) := ⟨⟩
-- instance
--   [TensorProductGetX R Y₁ X₁ YX₁₁] [TensorProductGetX R Y₁ X₂ YX₁₂]
--   [TensorProductGetX R Y₂ X₁ YX₂₁] [TensorProductGetX R Y₂ X₂ YX₂₂] :
--   TensorProductGetX R (Y₁ × Y₂) (X₁ × X₂) (ProdMatrix YX₁₁ YX₁₂ YX₂₁ YX₂₂) := ⟨⟩


variable
  {X₁₁ : Type*} [AddCommGroup X₁₁] [Module R X₁₁]
  [TensorProductType R X₁ X₁ X₁₁] [TensorProductSelf R X₁ X₁₁]
  {X₂₂ : Type*} [AddCommGroup X₂₂] [Module R X₂₂]
  [TensorProductType R X₂ X₂ X₂₂] [TensorProductSelf R X₂ X₂₂]
  {X₁₂ : Type*} [AddCommGroup X₁₂] [Module R X₁₂]
  [TensorProductType R X₁ X₂ X₁₂]
  {X₂₁ : Type*} [AddCommGroup X₂₁] [Module R X₂₁]
  [TensorProductType R X₂ X₁ X₂₁]


open TensorProductSelf in
instance : TensorProductSelf R (X₁ × X₂) (ProdMatrixCol (ProdMatrixRow X₁₁ X₁₂) (ProdMatrixRow X₂₁ X₂₂)) where
  identityMatrix := ⟨⟨𝐈[R,X₁], 0⟩, ⟨0, 𝐈[R,X₂]⟩⟩
  identityMatrix_spec := sorry_proof
  addIdentityMatrix := fun r ⟨⟨A₁₁,A₁₂⟩,⟨A₂₁,A₂₂⟩⟩ =>
    ⟨⟨addIdentityMatrix X₁ r A₁₁, A₁₂⟩, ⟨A₂₁, addIdentityMatrix X₂ r A₂₂⟩⟩
  addIdentityMatrix_spec := sorry_proof



@[simp,simp_core]
theorem identityMatrix_fst : (identityMatrix R (X₁×X₂)).1 = ⟨𝐈[R,X₁],0⟩ := by rfl

@[simp,simp_core]
theorem identityMatrix_snd : (identityMatrix R (X₁×X₂)).2 = ⟨0, 𝐈[R,X₂]⟩ := by rfl
