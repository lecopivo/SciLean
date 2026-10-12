module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import SciLean.Algebra.TensorProduct.Basic

@[expose] public section


namespace SciLean

variable (R : Type*) [RCLike R]
  {Y : Type*} [NormedAddCommGroup Y] [AdjointSpace R Y]
  {X : Type*} [NormedAddCommGroup X] [AdjointSpace R X]
  {YX : Type*} [AddCommGroup YX] [Module R YX] [TensorProductType R Y X YX]
  {I nI} [IndexType I nI] [Fold I] [Fold I]
  {J nJ} [IndexType J nJ] [Fold J] [Fold J]


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

open Classical TensorProduct in
/-- `IndexedMatrixCol I (Y⊗X)` is the tensor product `(I → Y) ⊗ X`. -/
noncomputable
def indexedMatrixColTensorEquiv :
    IndexedMatrixCol I YX ≃ₗ[R] TensorProduct R (I → Y) X :=
  (LinearEquiv.piCongrRight
      (fun _ : I => (TensorProductType.equiv (R:=R) (Y:=Y) (X:=X) (YX:=YX)).out)).trans
    (TensorProduct.piLeft R X (fun _ : I => Y)).symm

open Classical TensorProduct in
theorem indexedMatrixColTensorEquiv_tmulAdd (r : R) (y : I → Y) (x : X) (A : IndexedMatrixCol I YX) :
    (fun i => tmulAdd r (y i) x (A i))
    =
    (indexedMatrixColTensorEquiv R).symm
      (r • (y ⊗ₜ[R] x) + indexedMatrixColTensorEquiv R A) := by
  set e := (TensorProductType.equiv (R:=R) (Y:=Y) (X:=X) (YX:=YX)).out with he
  have h : ∀ i, e (tmulAdd r (y i) x (A i)) = r • (y i ⊗ₜ[R] x) + e (A i) := by
    intro i
    rw [TensorProductType.tmulAdd_eq_tmul, ← he, LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.eq_symm_apply]
  show (TensorProduct.piLeft R X (fun _ : I => Y)).symm (fun i => e (tmulAdd r (y i) x (A i)))
     = r • (y ⊗ₜ[R] x)
       + (TensorProduct.piLeft R X (fun _ : I => Y)).symm (fun i => e (A i))
  have hfun : (fun i => e (tmulAdd r (y i) x (A i)))
            = r • (fun i => y i ⊗ₜ[R] x) + (fun i => e (A i)) := by
    funext i; exact h i
  rw [hfun, map_add, map_smul]
  congr 2
  rw [LinearEquiv.symm_apply_eq]
  funext i
  simp

instance : TensorProductType R (I → Y) X (IndexedMatrixCol I YX) where
  equiv := .mk (indexedMatrixColTensorEquiv R)
  tmulAdd := fun r y x A i => tmulAdd r (y i) x (A i)
  matVecMulAdd := fun a A x b y i => matVecMulAdd a (A i) x b (y i)
  vecMatMulAdd := fun a y A b x => ∑ᴵ i, vecMatMulAdd a (y i) (A i) b x
  tmulAdd_eq_tmul := by
    intro r x y A
    simpa using indexedMatrixColTensorEquiv_tmulAdd R y x A (r:=r)

instance [TensorProductGetYX R Y X YX] : TensorProductGetYX R (I → Y) X (IndexedMatrixCol I YX) := ⟨⟩
instance [TensorProductGetY R Y X YX] : TensorProductGetY R (I → Y) X (IndexedMatrixCol I YX) := ⟨⟩
instance [TensorProductGetX R Y X YX] : TensorProductGetX R (I → Y) X (IndexedMatrixCol I YX) := ⟨⟩

open Classical TensorProduct in
/-- `IndexedMatrixRow I (Y⊗X)` is the tensor product `Y ⊗ (I → X)`. -/
noncomputable
def indexedMatrixRowTensorEquiv :
    IndexedMatrixRow I YX ≃ₗ[R] TensorProduct R Y (I → X) :=
  (LinearEquiv.piCongrRight
      (fun _ : I => (TensorProductType.equiv (R:=R) (Y:=Y) (X:=X) (YX:=YX)).out)).trans
    (TensorProduct.piRight R R Y (fun _ : I => X)).symm

open Classical TensorProduct in
theorem indexedMatrixRowTensorEquiv_tmulAdd (r : R) (y : Y) (x : I → X) (A : IndexedMatrixRow I YX) :
    (fun i => tmulAdd r y (x i) (A i))
    =
    (indexedMatrixRowTensorEquiv R).symm
      (r • (y ⊗ₜ[R] x) + indexedMatrixRowTensorEquiv R A) := by
  set e := (TensorProductType.equiv (R:=R) (Y:=Y) (X:=X) (YX:=YX)).out with he
  have h : ∀ i, e (tmulAdd r y (x i) (A i)) = r • (y ⊗ₜ[R] x i) + e (A i) := by
    intro i
    rw [TensorProductType.tmulAdd_eq_tmul, ← he, LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.eq_symm_apply]
  show (TensorProduct.piRight R R Y (fun _ : I => X)).symm
         (fun i => e (tmulAdd r y (x i) (A i)))
     = r • (y ⊗ₜ[R] x)
       + (TensorProduct.piRight R R Y (fun _ : I => X)).symm (fun i => e (A i))
  have hfun : (fun i => e (tmulAdd r y (x i) (A i)))
            = r • (fun i => y ⊗ₜ[R] x i) + (fun i => e (A i)) := by
    funext i; exact h i
  rw [hfun, map_add, map_smul]
  congr 2
  rw [LinearEquiv.symm_apply_eq]
  simp [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]

instance : TensorProductType R Y (I → X) (IndexedMatrixRow I YX) where
  equiv := .mk (indexedMatrixRowTensorEquiv R)
  tmulAdd := fun r y x A i => tmulAdd r y (x i) (A i)
  matVecMulAdd := fun a A x b y => ∑ᴵ i, matVecMulAdd a (A i) (x i) b y
  vecMatMulAdd := fun a y A b x i => vecMatMulAdd a y (A i) b (x i)
  tmulAdd_eq_tmul := by
    intro r x y A
    simpa using indexedMatrixRowTensorEquiv_tmulAdd R y x A (r:=r)

instance [TensorProductGetYX R Y X YX] : TensorProductGetYX R Y (I → X) (IndexedMatrixRow I YX) := ⟨⟩
instance [TensorProductGetY R Y X YX] : TensorProductGetY R Y (I → X) (IndexedMatrixRow I YX) := ⟨⟩
instance [TensorProductGetX R Y X YX] : TensorProductGetX R Y (I → X) (IndexedMatrixRow I YX) := ⟨⟩


open Classical TensorProduct in
/-- `IndexedMatrix I J (Y⊗X)` is the tensor product `(I → Y) ⊗ (J → X)`. -/
noncomputable
def indexedMatrixTensorEquiv :
    IndexedMatrix I J YX ≃ₗ[R] TensorProduct R (I → Y) (J → X) :=
  (LinearEquiv.piCongrRight (fun _ : I => indexedMatrixRowTensorEquiv (I:=J) R)).trans
    (TensorProduct.piLeft R (J → X) (fun _ : I => Y)).symm

open Classical TensorProduct in
theorem indexedMatrixTensorEquiv_tmulAdd (r : R) (y : I → Y) (x : J → X)
    (A : IndexedMatrix I J YX) :
    (fun i j => tmulAdd r (y i) (x j) (A i j))
    =
    (indexedMatrixTensorEquiv R).symm
      (r • (y ⊗ₜ[R] x) + indexedMatrixTensorEquiv R A) := by
  set E := indexedMatrixRowTensorEquiv (I:=J) (R:=R) (Y:=Y) (X:=X) (YX:=YX) with hE
  have h : ∀ i, E (fun j => tmulAdd r (y i) (x j) (A i j)) = r • (y i ⊗ₜ[R] x) + E (A i) := by
    intro i
    rw [indexedMatrixRowTensorEquiv_tmulAdd R (y i) x (A i) (r:=r), ← hE,
      LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.eq_symm_apply]
  show (TensorProduct.piLeft R (J → X) (fun _ : I => Y)).symm
         (fun i => E (fun j => tmulAdd r (y i) (x j) (A i j)))
     = r • (y ⊗ₜ[R] x)
       + (TensorProduct.piLeft R (J → X) (fun _ : I => Y)).symm (fun i => E (A i))
  have hfun : (fun i => E (fun j => tmulAdd r (y i) (x j) (A i j)))
            = r • (fun i => y i ⊗ₜ[R] x) + (fun i => E (A i)) := by
    funext i; exact h i
  rw [hfun, map_add, map_smul]
  congr 2
  rw [LinearEquiv.symm_apply_eq]
  funext i
  simp

instance : TensorProductType R (I → Y) (J → X) (IndexedMatrix I J YX) where
  equiv := .mk (indexedMatrixTensorEquiv R)
  tmulAdd := fun r y x A i j => tmulAdd r (y i) (x j) (A i j)
  matVecMulAdd := fun a A x b y i => ∑ᴵ j, matVecMulAdd a (A i j) (x j) b (y i)
  vecMatMulAdd := fun a y A b x i => ∑ᴵ j, vecMatMulAdd a (y j) (A j i) b (x i)
  tmulAdd_eq_tmul := by
    intro r x y A
    simpa using indexedMatrixTensorEquiv_tmulAdd R y x A (r:=r)

instance [TensorProductGetYX R Y X YX] : TensorProductGetYX R (I → Y) (J → X) (IndexedMatrix I J YX) := ⟨⟩
instance [TensorProductGetY R Y X YX] : TensorProductGetY R (I → Y) (J → X) (IndexedMatrix I J YX) := ⟨⟩
instance [TensorProductGetX R Y X YX] : TensorProductGetX R (I → Y) (J → X) (IndexedMatrix I J YX) := ⟨⟩
