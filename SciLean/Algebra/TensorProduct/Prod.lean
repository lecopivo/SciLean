module

public import Mathlib.LinearAlgebra.TensorProduct.Prod

public import SciLean.Algebra.TensorProduct.Basic
public import SciLean.Algebra.TensorProduct.Self

public import SciLean.Algebra.TensorProduct.ProdMatrixCol
public import SciLean.Algebra.TensorProduct.ProdMatrixRow
public import SciLean.Algebra.TensorProduct.ProdMatrix

@[expose] public section


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


/-- `ProdMatrixCol M₁ M₂` is linearly isomorphic to `M₁ × M₂`. -/
def ProdMatrixCol.linearEquivProd {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] : ProdMatrixCol M₁ M₂ ≃ₗ[R] M₁ × M₂ where
  toFun A := (A.A₁, A.A₂)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- `ProdMatrixRow M₁ M₂` is linearly isomorphic to `M₁ × M₂`. -/
def ProdMatrixRow.linearEquivProd {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] : ProdMatrixRow M₁ M₂ ≃ₗ[R] M₁ × M₂ where
  toFun A := (A.A₁, A.A₂)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

open TensorProduct in
/-- `ProdMatrixCol (Y₁⊗X₁) (Y₂⊗X₁)` is the tensor product `(Y₁×Y₂) ⊗ X₁`. -/
noncomputable
def prodMatrixColTensorEquiv :
    ProdMatrixCol YX₁₁ YX₂₁ ≃ₗ[R] TensorProduct R (Y₁ × Y₂) X₁ :=
  (ProdMatrixCol.linearEquivProd R).trans
    (((TensorProductType.equiv (R:=R) (Y:=Y₁) (X:=X₁) (YX:=YX₁₁)).out.prodCongr
        (TensorProductType.equiv (R:=R) (Y:=Y₂) (X:=X₁) (YX:=YX₂₁)).out).trans
      (TensorProduct.prodLeft R R Y₁ Y₂ X₁).symm)

open TensorProduct in
/-- `ProdMatrixRow (Y₁⊗X₁) (Y₁⊗X₂)` is the tensor product `Y₁ ⊗ (X₁×X₂)`. -/
noncomputable
def prodMatrixRowTensorEquiv :
    ProdMatrixRow YX₁₁ YX₁₂ ≃ₗ[R] TensorProduct R Y₁ (X₁ × X₂) :=
  (ProdMatrixRow.linearEquivProd R).trans
    (((TensorProductType.equiv (R:=R) (Y:=Y₁) (X:=X₁) (YX:=YX₁₁)).out.prodCongr
        (TensorProductType.equiv (R:=R) (Y:=Y₁) (X:=X₂) (YX:=YX₁₂)).out).trans
      (TensorProduct.prodRight R R Y₁ X₁ X₂).symm)

open TensorProduct TensorProductType in
theorem prodMatrixColTensorEquiv_tmulAdd (r : R) (y₁ : Y₁) (y₂ : Y₂) (x : X₁)
    (A₁ : YX₁₁) (A₂ : YX₂₁) :
    (⟨tmulAdd r y₁ x A₁, tmulAdd r y₂ x A₂⟩ : ProdMatrixCol YX₁₁ YX₂₁)
    =
    (prodMatrixColTensorEquiv R).symm
      (r • ((y₁,y₂) ⊗ₜ[R] x) + prodMatrixColTensorEquiv R ⟨A₁,A₂⟩) := by
  set e₁ := (TensorProductType.equiv (R:=R) (Y:=Y₁) (X:=X₁) (YX:=YX₁₁)).out with he₁
  set e₂ := (TensorProductType.equiv (R:=R) (Y:=Y₂) (X:=X₁) (YX:=YX₂₁)).out with he₂
  have h₁ : e₁ (tmulAdd r y₁ x A₁) = r • (y₁ ⊗ₜ[R] x) + e₁ A₁ := by
    rw [TensorProductType.tmulAdd_eq_tmul, ← he₁, LinearEquiv.apply_symm_apply]
  have h₂ : e₂ (tmulAdd r y₂ x A₂) = r • (y₂ ⊗ₜ[R] x) + e₂ A₂ := by
    rw [TensorProductType.tmulAdd_eq_tmul, ← he₂, LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.eq_symm_apply]
  show (TensorProduct.prodLeft R R Y₁ Y₂ X₁).symm
         (e₁ (tmulAdd r y₁ x A₁), e₂ (tmulAdd r y₂ x A₂))
     = r • ((y₁,y₂) ⊗ₜ[R] x) + (TensorProduct.prodLeft R R Y₁ Y₂ X₁).symm (e₁ A₁, e₂ A₂)
  rw [h₁, h₂]
  have hmk : ((r • (y₁ ⊗ₜ[R] x) + e₁ A₁, r • (y₂ ⊗ₜ[R] x) + e₂ A₂))
           = r • ((y₁ ⊗ₜ[R] x, y₂ ⊗ₜ[R] x)) + (e₁ A₁, e₂ A₂) := rfl
  rw [hmk, map_add, map_smul]
  congr 2
  rw [LinearEquiv.symm_apply_eq]
  simp [TensorProduct.prodLeft]

open TensorProductType in
instance (priority:=low) : TensorProductType R (Y₁ × Y₂) X₁ (ProdMatrixCol YX₁₁ YX₂₁) where
  equiv := .mk (prodMatrixColTensorEquiv R)
  tmulAdd := fun r ⟨y₁,y₂⟩ x ⟨A₁,A₂⟩ =>
    ⟨tmulAdd r y₁ x A₁, tmulAdd r y₂ x A₂⟩
  matVecMulAdd := fun a ⟨A₁,A₂⟩ x b ⟨y₁,y₂⟩ =>
    ⟨matVecMulAdd a A₁ x b y₁, matVecMulAdd a A₂ x b y₂⟩
  vecMatMulAdd := fun a ⟨A₁,A₂⟩ ⟨y₁,y₂⟩ b x =>
    vecMatMulAdd a A₂ y₂ 1 (vecMatMulAdd a A₁ y₁ b x)
  tmulAdd_eq_tmul := by
    intro r x y A
    obtain ⟨y₁,y₂⟩ := y
    obtain ⟨A₁,A₂⟩ := A
    simpa using prodMatrixColTensorEquiv_tmulAdd R r y₁ y₂ x A₁ A₂

instance [TensorProductGetYX R Y₁ X₁ YX₁₁] [TensorProductGetYX R Y₂ X₁ YX₂₁] :
  TensorProductGetYX R (Y₁ × Y₂) X₁ (ProdMatrixCol YX₁₁ YX₂₁) := ⟨⟩
instance [TensorProductGetY R Y₁ X₁ YX₁₁] [TensorProductGetY R Y₂ X₁ YX₂₁] :
  TensorProductGetY R (Y₁ × Y₂) X₁ (ProdMatrixCol YX₁₁ YX₂₁) := ⟨⟩
instance [TensorProductGetX R Y₁ X₁ YX₁₁] [TensorProductGetX R Y₂ X₁ YX₂₁] :
  TensorProductGetX R (Y₁ × Y₂) X₁ (ProdMatrixCol YX₁₁ YX₂₁) := ⟨⟩


open TensorProduct TensorProductType in
theorem prodMatrixRowTensorEquiv_tmulAdd (r : R) (y : Y₁) (x₁ : X₁) (x₂ : X₂)
    (A₁ : YX₁₁) (A₂ : YX₁₂) :
    (⟨tmulAdd r y x₁ A₁, tmulAdd r y x₂ A₂⟩ : ProdMatrixRow YX₁₁ YX₁₂)
    =
    (prodMatrixRowTensorEquiv R).symm
      (r • (y ⊗ₜ[R] (x₁,x₂)) + prodMatrixRowTensorEquiv R ⟨A₁,A₂⟩) := by
  set e₁ := (TensorProductType.equiv (R:=R) (Y:=Y₁) (X:=X₁) (YX:=YX₁₁)).out with he₁
  set e₂ := (TensorProductType.equiv (R:=R) (Y:=Y₁) (X:=X₂) (YX:=YX₁₂)).out with he₂
  have h₁ : e₁ (tmulAdd r y x₁ A₁) = r • (y ⊗ₜ[R] x₁) + e₁ A₁ := by
    rw [TensorProductType.tmulAdd_eq_tmul, ← he₁, LinearEquiv.apply_symm_apply]
  have h₂ : e₂ (tmulAdd r y x₂ A₂) = r • (y ⊗ₜ[R] x₂) + e₂ A₂ := by
    rw [TensorProductType.tmulAdd_eq_tmul, ← he₂, LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.eq_symm_apply]
  show (TensorProduct.prodRight R R Y₁ X₁ X₂).symm
         (e₁ (tmulAdd r y x₁ A₁), e₂ (tmulAdd r y x₂ A₂))
     = r • (y ⊗ₜ[R] (x₁,x₂)) + (TensorProduct.prodRight R R Y₁ X₁ X₂).symm (e₁ A₁, e₂ A₂)
  rw [h₁, h₂]
  have hmk : ((r • (y ⊗ₜ[R] x₁) + e₁ A₁, r • (y ⊗ₜ[R] x₂) + e₂ A₂))
           = r • ((y ⊗ₜ[R] x₁, y ⊗ₜ[R] x₂)) + (e₁ A₁, e₂ A₂) := rfl
  rw [hmk, map_add, map_smul]
  congr 2
  rw [LinearEquiv.symm_apply_eq]
  simp [TensorProduct.prodRight]

open TensorProductType in
instance (priority:=low) : TensorProductType R Y₁ (X₁ × X₂) (ProdMatrixRow YX₁₁ YX₁₂) where
  equiv := .mk (prodMatrixRowTensorEquiv R)
  tmulAdd := fun r y ⟨x₁,x₂⟩ ⟨A₁,A₂⟩ =>
    ⟨tmulAdd r y x₁ A₁, tmulAdd r y x₂ A₂⟩
  matVecMulAdd := fun a ⟨A₁,A₂⟩ ⟨x₁,x₂⟩ b y =>
    matVecMulAdd a A₂ x₂ b (matVecMulAdd a A₁ x₁ b y)
  vecMatMulAdd := fun a y ⟨A₁,A₂⟩ b ⟨x₁,x₂⟩ =>
    ⟨vecMatMulAdd a y A₁ 1 x₁, vecMatMulAdd a y A₂ b x₂⟩
  tmulAdd_eq_tmul := by
    intro r x y A
    obtain ⟨x₁,x₂⟩ := x
    obtain ⟨A₁,A₂⟩ := A
    simpa using prodMatrixRowTensorEquiv_tmulAdd R y x₁ x₂ A₁ A₂ (r:=r)

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
  -- note: false as stated, the `ProdMatrixRow` `matVecMulAdd` above passes `b` to both blocks, so
  -- for `b = 0` the first block is dropped; see `ProdIdentityCounterexample.lean` in this directory
  identityMatrix_spec := sorry_proof
  addIdentityMatrix := fun r ⟨⟨A₁₁,A₁₂⟩,⟨A₂₁,A₂₂⟩⟩ =>
    ⟨⟨addIdentityMatrix X₁ r A₁₁, A₁₂⟩, ⟨A₂₁, addIdentityMatrix X₂ r A₂₂⟩⟩
  addIdentityMatrix_spec := by
    rintro a ⟨⟨A₁₁,A₁₂⟩,⟨A₂₁,A₂₂⟩⟩
    show ProdMatrixCol.mk (ProdMatrixRow.mk (addIdentityMatrix X₁ a A₁₁) A₁₂)
           (ProdMatrixRow.mk A₂₁ (addIdentityMatrix X₂ a A₂₂))
         = ProdMatrixCol.mk (ProdMatrixRow.mk (a • 𝐈[R,X₁] + A₁₁) (a • (0:X₁₂) + A₁₂))
           (ProdMatrixRow.mk (a • (0:X₂₁) + A₂₁) (a • 𝐈[R,X₂] + A₂₂))
    rw [TensorProductSelf.addIdentityMatrix_spec, TensorProductSelf.addIdentityMatrix_spec,
        smul_zero, smul_zero, zero_add, zero_add]



@[simp,simp_core]
theorem identityMatrix_fst : (identityMatrix R (X₁×X₂)).1 = ⟨𝐈[R,X₁],0⟩ := by rfl

@[simp,simp_core]
theorem identityMatrix_snd : (identityMatrix R (X₁×X₂)).2 = ⟨0, 𝐈[R,X₂]⟩ := by rfl
