import SciLean.Data.MatrixType.Base
import SciLean.Data.VectorType.Prod

namespace SciLean

structure BlockMatrix (M₁₁ M₁₂ M₂₁ M₂₂ : Type*) where
  A₁₁ : M₁₁
  A₁₂ : M₁₂
  A₂₁ : M₂₁
  A₂₂ : M₂₂

namespace BlockMatrix

variable
  {R K : Type*} {ir : RealScalar R} {is : Scalar R K}
  {m₁ m₂ : Type*} {_ : IndexType m₁} {_ : IndexType m₂}
  {n₁ n₂ : Type*} {_ : IndexType n₁} {_ : IndexType n₂}
  {X₁ X₂ : Type*} {_ : VectorType.Base X₁ n₁ K} {_ : VectorType.Base X₂ n₂ K}
  {Y₁ Y₂ : Type*} {_ : VectorType.Base Y₁ m₁ K} {_ : VectorType.Base Y₂ m₂ K}
  [MatrixType.Base M₁₁ X₁ Y₁] [MatrixType.Base M₁₂ X₂ Y₁] [MatrixType.Base M₂₁ X₁ Y₂] [MatrixType.Base M₂₂ X₂ Y₂]

open VectorType in
instance : VectorType.Base (BlockMatrix M₁₁ M₁₂ M₂₁ M₂₂) ((m₁⊕m₂)×(n₁⊕n₂)) K where
  getElem := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ (i,j) _ =>
    match i, j with
    | .inl i, .inl j => A₁₁[(i,j)]
    | .inl i, .inr j => A₁₂[(i,j)]
    | .inr i, .inl j => A₂₁[(i,j)]
    | .inr i, .inr j => A₂₂[(i,j)]
  zero := ⟨zero, zero, zero, zero⟩
  zero_spec := sorry_proof
  scal := fun k ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ => ⟨scal k A₁₁, scal k A₁₂, scal k A₂₁, scal k A₂₂⟩
  scal_spec := sorry_proof
  sum := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ => VectorType.sum A₁₁ + VectorType.sum A₁₂ + VectorType.sum A₂₁ + VectorType.sum A₂₂
  sum_spec := sorry_proof
  asum := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ => asum A₁₁ + asum A₁₂ + asum A₂₁ + asum A₂₂
  asum_spec := sorry_proof
  nrm2 := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ => Scalar.sqrt ((nrm2 A₁₁)^2 + (nrm2 A₁₂)^2 + (nrm2 A₂₁)^2 + (nrm2 A₂₂)^2)
  nrm2_spec := sorry_proof
  iamax := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ =>
    let i₁₁ : Option ((m₁⊕m₂)×(n₁⊕n₂)) := iamax? A₁₁ |>.map (fun (i,j) => (.inl i, .inl j))
    let i₁₂ : Option ((m₁⊕m₂)×(n₁⊕n₂)) := iamax? A₁₂ |>.map (fun (i,j) => (.inl i, .inr j))
    let i₂₁ : Option ((m₁⊕m₂)×(n₁⊕n₂)) := iamax? A₂₁ |>.map (fun (i,j) => (.inr i, .inl j))
    let i₂₂ : Option ((m₁⊕m₂)×(n₁⊕n₂)) := iamax? A₂₂ |>.map (fun (i,j) => (.inr i, .inr j))
    let f := fun ((i,j) : (m₁⊕m₂)×(n₁⊕n₂)) =>
      match i, j with
      | .inl i, .inl j => A₁₁[(i,j)]
      | .inl i, .inr j => A₁₂[(i,j)]
      | .inr i, .inl j => A₂₁[(i,j)]
      | .inr i, .inr j => A₂₂[(i,j)]
    let i? : Option ((m₁⊕m₂)×(n₁⊕n₂)) := [i₁₁, i₁₂, i₂₁, i₂₂].foldl (init:=none) (fun i j =>
      match i, j with
      | none, none => none
      | none, some i => some i
      | some i, none => some i
      | some i, some j =>
        if Scalar.abs (f i) > Scalar.abs (f j) then some i else some j)
    i?.get sorry_proof -- here we break consistency if matrix has zero dimension, we have to fix type signature of `iamax`
  iamax_spec := sorry_proof
  imaxRe := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ _h =>
    let i₁₁ : Option ((m₁⊕m₂)×(n₁⊕n₂)) := imaxRe? A₁₁ |>.map (fun (i,j) => (.inl i, .inl j))
    let i₁₂ : Option ((m₁⊕m₂)×(n₁⊕n₂)) := imaxRe? A₁₂ |>.map (fun (i,j) => (.inl i, .inr j))
    let i₂₁ : Option ((m₁⊕m₂)×(n₁⊕n₂)) := imaxRe? A₂₁ |>.map (fun (i,j) => (.inr i, .inl j))
    let i₂₂ : Option ((m₁⊕m₂)×(n₁⊕n₂)) := imaxRe? A₂₂ |>.map (fun (i,j) => (.inr i, .inr j))
    let f := fun ((i,j) : (m₁⊕m₂)×(n₁⊕n₂)) =>
      match i, j with
      | .inl i, .inl j => A₁₁[(i,j)]
      | .inl i, .inr j => A₁₂[(i,j)]
      | .inr i, .inl j => A₂₁[(i,j)]
      | .inr i, .inr j => A₂₂[(i,j)]
    let i? : Option ((m₁⊕m₂)×(n₁⊕n₂)) := [i₁₁, i₁₂, i₂₁, i₂₂].foldl (init:=none) (fun i j =>
      match i, j with
      | none, none => none
      | none, some i => some i
      | some i, none => some i
      | some i, some j =>
        if Scalar.real (f i) > Scalar.real (f j) then some i else some j)
    i?.get sorry_proof -- this should be guaranteed by `h` but proobably tedious to prove
  imaxRe_spec := sorry_proof
  iminRe := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ _h =>
    let i₁₁ : Option ((m₁⊕m₂)×(n₁⊕n₂)) := iminRe? A₁₁ |>.map (fun (i,j) => (.inl i, .inl j))
    let i₁₂ : Option ((m₁⊕m₂)×(n₁⊕n₂)) := iminRe? A₁₂ |>.map (fun (i,j) => (.inl i, .inr j))
    let i₂₁ : Option ((m₁⊕m₂)×(n₁⊕n₂)) := iminRe? A₂₁ |>.map (fun (i,j) => (.inr i, .inl j))
    let i₂₂ : Option ((m₁⊕m₂)×(n₁⊕n₂)) := iminRe? A₂₂ |>.map (fun (i,j) => (.inr i, .inr j))
    let f := fun ((i,j) : (m₁⊕m₂)×(n₁⊕n₂)) =>
      match i, j with
      | .inl i, .inl j => A₁₁[(i,j)]
      | .inl i, .inr j => A₁₂[(i,j)]
      | .inr i, .inl j => A₂₁[(i,j)]
      | .inr i, .inr j => A₂₂[(i,j)]
    let i? : Option ((m₁⊕m₂)×(n₁⊕n₂)) := [i₁₁, i₁₂, i₂₁, i₂₂].foldl (init:=none) (fun i j =>
      match i, j with
      | none, none => none
      | none, some i => some i
      | some i, none => some i
      | some i, some j =>
        if Scalar.real (f i) < Scalar.real (f j) then some i else some j)
    i?.get sorry_proof -- this should be guaranteed by `h` but proobably tedious to prove
  iminRe_spec := sorry_proof
  dot := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ ⟨B₁₁,B₁₂,B₂₁,B₂₂⟩ => dot A₁₁ B₁₁ + dot A₁₂ B₁₂ + dot A₂₁ B₂₁ + dot A₂₂ B₂₂
  dot_spec := sorry_proof
  conj := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ => ⟨conj A₁₁, conj A₁₂, conj A₂₁, conj A₂₂⟩
  conj_spec := sorry_proof
  axpy := fun a ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ ⟨B₁₁,B₁₂,B₂₁,B₂₂⟩ => ⟨axpy a A₁₁ B₁₁, axpy a A₁₂ B₁₂, axpy a A₂₁ B₂₁, axpy a A₂₂ B₂₂⟩
  axpy_spec := sorry_proof
  axpby := fun a ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ b ⟨B₁₁,B₁₂,B₂₁,B₂₂⟩ => ⟨axpby a A₁₁ b B₁₁, axpby a A₁₂ b B₁₂, axpby a A₂₁ b B₂₁, axpby a A₂₂ b B₂₂⟩
  axpby_spec := sorry_proof
  mul := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ ⟨B₁₁,B₁₂,B₂₁,B₂₂⟩ => ⟨mul A₁₁ B₁₁, mul A₁₂ B₁₂, mul A₂₁ B₂₁, mul A₂₂ B₂₂⟩
  mul_spec := sorry_proof


open MatrixType in
example : MatrixType.Base (BlockMatrix M₁₁ M₁₂ M₂₁ M₂₂) (m:=m₁⊕m₂) (n:=n₁⊕n₂) (R:=R) (K:=K) (X₁×X₂) (Y₁×Y₂) where
  toMatrix := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ i j =>
    match i, j with
    | .inl i, .inl j => toMatrix A₁₁ i j
    | .inl i, .inr j => toMatrix A₁₂ i j
    | .inr i, .inl j => toMatrix A₂₁ i j
    | .inr i, .inr j => toMatrix A₂₂ i j
  toVec_eq_toMatrix := sorry_proof

  gemv := fun a b ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ (x₁,x₂) (y₁,y₂) =>
    (gemv a 1 A₁₂ x₂ (gemv a b A₁₁ x₁ y₁), gemv a 1 A₂₂ x₂ (gemv a b A₂₁ x₁ y₂))
  gemv_spec := by
    intro a b ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ (x₁,x₂) (y₁,y₂) i
    cases i <;>
    (simp[matrix_to_spec,vector_to_spec,getElem,
          Matrix.mulVec, dotProduct, add_left_inj,
          ←Finset.univ_disjSum_univ, Finset.sum_product]
     ring)

  gemvT := fun a b ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ (x₁,x₂) (y₁,y₂) =>
    (gemvT a 1 A₁₁ x₁ (gemvT a b A₂₁ x₂ y₁), gemvT a 1 A₁₂ x₁ (gemvT a b A₂₂ x₂ y₂))
  gemvT_spec := by
    intro a b ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ (x₁,x₂) (y₁,y₂) i

    cases i <;>
    (simp[matrix_to_spec,vector_to_spec,getElem,
          Matrix.mulVec, dotProduct, add_left_inj,
          ←Finset.univ_disjSum_univ, Finset.sum_product]
     ring)

  gemvH := fun a b ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ (x₁,x₂) (y₁,y₂) =>
    (gemvH a 1 A₁₁ x₁ (gemvH a b A₂₁ x₂ y₁), gemvH a 1 A₁₂ x₁ (gemvH a b A₂₂ x₂ y₂))
  gemvH_spec := by
    intro a b ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ (x₁,x₂) (y₁,y₂) i
    cases i <;>
    (simp[matrix_to_spec,vector_to_spec,getElem,
          Matrix.mulVec, dotProduct, add_left_inj,
          ←Finset.univ_disjSum_univ, Finset.sum_product]
     ring)


  -- for now we moved row/column to dense matrices
  -- row := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ i =>
  --   match i with
  --   | .inl i => (row A₁₁ i, row A₁₂ i)
  --   | .inr i => (row A₂₁ i, row A₂₂ i)
  -- row_spec := sorry_proof

  -- sumRows := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ => (sumRows A₁₁ + sumRows A₁₂, sumRows A₂₁ + sumRows A₂₂)
  -- sumRows_spec := sorry_proof

  -- col := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ j =>
  --   match j with
  --   | .inl j => (col A₁₁ j, col A₂₁ j)
  --   | .inr j => (col A₁₂ j, col A₂₂ j)
  -- col_spec := sorry_proof

  -- sumCols := fun ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ => (sumCols A₁₁ + sumCols A₂₁, sumCols A₁₂ + sumCols A₂₂)
  -- sumCols_spec := sorry_proof
