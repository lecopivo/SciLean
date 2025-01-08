import SciLean.Data.VectorType.Base

namespace SciLean

open VectorType


instance
  {R K : Type*} {_ : RealScalar R} {_ : Scalar R K}
  {m n : Type*} {_ : IndexType m} {_ : IndexType n}
  {X Y : Type*} [VectorType.Base X m K] [VectorType.Base Y n K]
  : VectorType.Base (X×Y) (m⊕n) K where

  toVec := fun (x,y) ij =>
    match ij with
    | .inl i => toVec x i
    | .inr j => toVec y j
  zero := (zero, zero)
  zero_spec := by funext ij; cases ij <;> simp[vector_to_spec]
  scal := fun k (x,y) => (scal k x, scal k y)
  scal_spec := by intro k (x,y); funext ij; cases ij <;> simp[vector_to_spec]
  scalAdd := fun a b (x,y) => (scalAdd a b x, scalAdd a b y)
  scalAdd_spec := by intro a b (x,y); funext ij; cases ij <;> simp[vector_to_spec]
  sum := fun (x,y) => VectorType.sum x + VectorType.sum y
  sum_spec := by intro (x,y); simp[vector_to_spec]
  asum := fun (x,y) => asum x + asum y
  asum_spec := by intro (x,y); simp[vector_to_spec,Norm.norm]; sorry_proof -- some API for Scalar is missing
  nrm2 := fun (x,y) => Scalar.sqrt ((nrm2 x)^2 + (nrm2 y)^2)
  nrm2_spec := by intro (x,y); simp[vector_to_spec,Norm.norm]; sorry_proof -- some API for Scalar is missing
  iamax := fun (x,y) =>
    if h : 0 < size m ∧ 0 < size n then
      let i := iamax x
      let j := iamax y
      if Scalar.abs (toVec x i) < Scalar.abs (toVec y j) then
        .inr j
      else
        .inl i
    else if h : 0 < size n then
      let j := iamax y
      .inr j
    else if h : 0 < size m then
      let i := iamax x
      .inl i
    else
      .inl (iamax x) -- this is inconsistent!
  iamax_spec := by intro (x,y); simp; sorry_proof
  imaxRe := fun (x,y) h =>
    if h : 0 < size m ∧ 0 < size n then
      let i := imaxRe x h.1
      let j := imaxRe y h.2
      if Scalar.real (toVec x i) < Scalar.real (toVec y j) then
        .inr j
      else
        .inl i
    else if h : 0 < size n then
      let j := imaxRe y h
      .inr j
    else if h : 0 < size m then
      let i := imaxRe x h
      .inl i
    else
      (by simp_all) -- unreachable
  imaxRe_spec := sorry_proof
  iminRe := fun (x,y) h =>
    if h : 0 < size m ∧ 0 < size n then
      let i := iminRe x h.1
      let j := iminRe y h.2
      if Scalar.real (toVec x i) < Scalar.real (toVec y j) then
        .inl i
      else
        .inr j
    else if h : 0 < size n then
      let j := iminRe y h
      .inr j
    else if h : 0 < size m then
      let i := iminRe x h
      .inl i
    else
      (by simp_all) -- unreachable
  iminRe_spec := sorry_proof
  dot := fun (x₁,y₁) (x₂,y₂) => dot x₁ x₂ + dot y₁ y₂
  dot_spec := sorry_proof
  axpy := fun a (x₁,y₁) (x₂,y₂) => (axpy a x₁ x₂, axpy a y₁ y₂)
  axpy_spec := sorry_proof
  axpby := fun a (x₁,y₁) b (x₂,y₂) => (axpby a x₁ b x₂, axpby a y₁ b y₂)
  axpby_spec := sorry_proof
  mul := fun (x₁,y₁) (x₂,y₂) => (mul x₁ x₂, mul y₁ y₂)
  mul_spec := sorry_proof


instance
  {R K : Type*} {_ : RealScalar R} {_ : Scalar R K}
  {m n : Type*} {_ : IndexType m} {_ : IndexType n}
  {X Y : Type*} [VectorType.Base X m K] [VectorType.Base Y n K]
  [VectorType.Dense X] [VectorType.Dense Y]
  : VectorType.Dense (X×Y) where
  fromVec := fun f => (fromVec (fun i => f (.inl i)), fromVec (fun j => f (.inr j)))
  right_inv := by
    intro f; funext ij;
    cases ij
    · have h := fun f => VectorType.Dense.right_inv (X:=X) f
      simp[h,toVec]
    · have h := fun f => VectorType.Dense.right_inv (X:=Y) f
      simp[h,toVec]
  set := fun (x,y) ij v =>
    match ij with
    | .inl i => (set x i v, y)
    | .inr j => (x, set y j v)
  set_spec := by
    intro (x,y) ij k; funext ij';
    cases ij'
    <;> cases ij
    <;> simp[toVec,vector_to_spec]
    <;> split_ifs
    <;> simp_all
  const k := (const k, const k)
  const_spec := by intros; funext i; cases i <;> simp[toVec,vector_to_spec]
  div := fun (x,y) (x',y') => (div x x', div y y')
  div_spec := by intro (x,y) (x',y'); funext i; cases i <;> simp[toVec,vector_to_spec]
  inv := fun (x,y) => (inv x, inv y)
  inv_spec := by intro (x,y); funext i; cases i <;> simp[toVec,vector_to_spec]
  exp := fun (x,y) => (exp x, exp y)
  exp_spec := by intro (x,y); funext i; cases i <;> simp[toVec,vector_to_spec]
