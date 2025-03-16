import SciLean.Algebra.TensorProduct.Basic

import SciLean.Algebra.TensorProduct.BlockMatrixCol
import SciLean.Algebra.TensorProduct.BlockMatrixRow
import SciLean.Algebra.TensorProduct.BlockMatrix

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
instance (priority:=low) : TensorProductType R (Y₁ × Y₂) X₁ (BlockMatrixCol YX₁₁ YX₂₁) where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd := fun r ⟨y₁,y₂⟩ x ⟨A₁,A₂⟩ =>
    ⟨tmulAdd r y₁ x A₁, tmulAdd r y₂ x A₂⟩
  matVecMul := fun a ⟨A₁,A₂⟩ x b ⟨y₁,y₂⟩ =>
    ⟨matVecMul a A₁ x b y₁, matVecMul a A₂ x b y₂⟩
  matHVecMul := fun a ⟨A₁,A₂⟩ ⟨y₁,y₂⟩ b x =>
    matHVecMul a A₂ y₂ 1 (matHVecMul a A₁ y₁ b x)
  tmulAdd_eq_tmul := sorry_proof

instance [TensorProductGetYX R Y₁ X₁ YX₁₁] [TensorProductGetYX R Y₂ X₁ YX₂₁] :
  TensorProductGetYX R (Y₁ × Y₂) X₁ (BlockMatrixCol YX₁₁ YX₂₁) := ⟨⟩
instance [TensorProductGetY R Y₁ X₁ YX₁₁] [TensorProductGetY R Y₂ X₁ YX₂₁] :
  TensorProductGetY R (Y₁ × Y₂) X₁ (BlockMatrixCol YX₁₁ YX₂₁) := ⟨⟩
instance [TensorProductGetX R Y₁ X₁ YX₁₁] [TensorProductGetX R Y₂ X₁ YX₂₁] :
  TensorProductGetX R (Y₁ × Y₂) X₁ (BlockMatrixCol YX₁₁ YX₂₁) := ⟨⟩


open TensorProductType in
instance (priority:=low) : TensorProductType R Y₁ (X₁ × X₂) (BlockMatrixRow YX₁₁ YX₁₂) where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd := fun r y ⟨x₁,x₂⟩ ⟨A₁,A₂⟩ =>
    ⟨tmulAdd r y x₁ A₁, tmulAdd r y x₂ A₂⟩
  matVecMul := fun a ⟨A₁,A₂⟩ ⟨x₁,x₂⟩ b y =>
    matVecMul a A₂ x₂ b (matVecMul a A₁ x₁ b y)
  matHVecMul := fun a ⟨A₁,A₂⟩ y b ⟨x₁,x₂⟩ =>
    ⟨matHVecMul a A₁ y 1 x₁, matHVecMul a A₂ y b x₂⟩
  tmulAdd_eq_tmul := sorry_proof

instance [TensorProductGetYX R Y₁ X₁ YX₁₁] [TensorProductGetYX R Y₁ X₂ YX₁₂] :
  TensorProductGetYX R Y₁ (X₁ × X₂) (BlockMatrixRow YX₁₁ YX₁₂) := ⟨⟩
instance [TensorProductGetY R Y₁ X₁ YX₁₁] [TensorProductGetY R Y₁ X₂ YX₁₂] :
  TensorProductGetY R Y₁ (X₁ × X₂) (BlockMatrixRow YX₁₁ YX₁₂) := ⟨⟩
instance [TensorProductGetX R Y₁ X₁ YX₁₁] [TensorProductGetX R Y₁ X₂ YX₁₂] :
  TensorProductGetX R Y₁ (X₁ × X₂) (BlockMatrixRow YX₁₁ YX₁₂) := ⟨⟩


open TensorProductType in
instance : TensorProductType R (Y₁ × Y₂) (X₁ × X₂) (BlockMatrix YX₁₁ YX₁₂ YX₂₁ YX₂₂) where
  equiv := ⟨fun _ => True, sorry_proof⟩
  tmulAdd := fun r ⟨y₁,y₂⟩ ⟨x₁,x₂⟩ ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ =>
    {
      A₁₁ := tmulAdd r y₁ x₁ A₁₁
      A₁₂ := tmulAdd r y₁ x₂ A₁₂
      A₂₁ := tmulAdd r y₂ x₁ A₂₁
      A₂₂ := tmulAdd r y₂ x₂ A₂₂
    }
  matVecMul := fun a ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ ⟨x₁,x₂⟩ b ⟨y₁,y₂⟩ =>
    {
      fst := matVecMul a A₁₁ x₁ b (matVecMul a A₁₂ x₂ b y₁)
      snd := matVecMul a A₂₁ x₁ b (matVecMul a A₂₂ x₂ b y₂)
    }
  matHVecMul := fun a ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ ⟨y₁,y₂⟩ b ⟨x₁,x₂⟩ =>
    {
      fst := matHVecMul a A₁₁ y₁ b (matHVecMul a A₂₁ y₂ b x₁)
      snd := matHVecMul a A₁₂ y₁ b (matHVecMul a A₂₂ y₂ b x₂)
    }
  tmulAdd_eq_tmul := sorry_proof

instance
  [TensorProductGetYX R Y₁ X₁ YX₁₁] [TensorProductGetYX R Y₁ X₂ YX₁₂]
  [TensorProductGetYX R Y₂ X₁ YX₂₁] [TensorProductGetYX R Y₂ X₂ YX₂₂] :
  TensorProductGetYX R (Y₁ × Y₂) (X₁ × X₂) (BlockMatrix YX₁₁ YX₁₂ YX₂₁ YX₂₂) := ⟨⟩
instance
  [TensorProductGetY R Y₁ X₁ YX₁₁] [TensorProductGetY R Y₁ X₂ YX₁₂]
  [TensorProductGetY R Y₂ X₁ YX₂₁] [TensorProductGetY R Y₂ X₂ YX₂₂] :
  TensorProductGetY R (Y₁ × Y₂) (X₁ × X₂) (BlockMatrix YX₁₁ YX₁₂ YX₂₁ YX₂₂) := ⟨⟩
instance
  [TensorProductGetX R Y₁ X₁ YX₁₁] [TensorProductGetX R Y₁ X₂ YX₁₂]
  [TensorProductGetX R Y₂ X₁ YX₂₁] [TensorProductGetX R Y₂ X₂ YX₂₂] :
  TensorProductGetX R (Y₁ × Y₂) (X₁ × X₂) (BlockMatrix YX₁₁ YX₁₂ YX₂₁ YX₂₂) := ⟨⟩
