import SciLean.Data.VectorType.Base

namespace SciLean

open VectorType


instance
  {R K : Type*} {_ : RealScalar R} {_ : Scalar R K}
  {m n : Type*} {_ : IndexType m} {_ : IndexType n}
  {X Y : Type*} [VectorType.Base X m K] [VectorType.Base Y n K]
  : VectorType.Base (X×Y) (m⊕n) K where

  getElem := fun (x,y) ij _ =>
    match ij with
    | .inl i => x[i]
    | .inr j => y[j]
  zero := (zero, zero)
  zero_spec := by intro ij; cases ij <;> simp[vector_to_spec]
  scal := fun k (x,y) => (scal k x, scal k y)
  scal_spec := by intro k (x,y); intro ij; cases ij <;> simp[vector_to_spec]
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
      if Scalar.abs (x[i]) < Scalar.abs (y[j]) then
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
      if Scalar.real (x[i]) < Scalar.real (y[j]) then
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
      if Scalar.real (x[i]) < Scalar.real (y[j]) then
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
  conj := fun (x₁,x₂) => (conj x₁, conj x₂)
  conj_spec := sorry_proof
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
  : SetElem (X×Y) (m⊕n) K (fun _ _ => True) where
    setElem := fun (x,y) ij v _ =>
      match ij with
      | .inl i => (setElem (valid:=fun _ _ => True) x i v (True.intro), y)
      | .inr j => (x, setElem y j v (by dsimp))
    setElem_valid := sorry_proof

instance
  {R K : Type*} {_ : RealScalar R} {_ : Scalar R K}
  {m n : Type*} {_ : IndexType m} {_ : IndexType n}
  {X Y : Type*} [VectorType.Base X m K] [VectorType.Base Y n K]
  [VectorType.Dense X] [VectorType.Dense Y]
  : VectorType.Dense (X×Y) where
  fromVec := fun f => (fromVec (fun i => f (.inl i)), fromVec (fun j => f (.inr j)))
  right_inv := by sorry_proof
    -- intro f; funext ij;
    -- cases ij
    -- · have h := fun f => VectorType.Dense.right_inv (X:=X) f
    --   simp[h,toVec]
    -- · have h := fun f => VectorType.Dense.right_inv (X:=Y) f
    --   simp[h,toVec]
  getElem_setElem_eq := by
    intro (x,y) ij k _;
    cases ij
    <;> simp[getElem,vector_to_spec,LawfulSetElem.getElem_setElem_eq]
  getElem_setElem_neq := by
    intro (x,y) ij ij' v _ _ h;
    sorry_proof
    -- cases ij <;> cases ij'
    -- <;> simp[getElem,vector_to_spec,LawfulSetElem.getElem_setElem_neq,h]
    -- sorry_proof
  const k := (const k, const k)
  const_spec := by intros _ i; cases i <;> simp[getElem,vector_to_spec]
  scalAdd := fun a b (x,y) => (scalAdd a b x, scalAdd a b y)
  scalAdd_spec := by intro a b (x,y) ij; cases ij <;> simp[getElem,vector_to_spec]
  div := fun (x,y) (x',y') => (div x x', div y y')
  div_spec := by intro (x,y) (x',y') i; cases i <;> simp[getElem,vector_to_spec]
  inv := fun (x,y) => (inv x, inv y)
  inv_spec := by intro (x,y) i; cases i <;> simp[getElem,vector_to_spec]
  exp := fun (x,y) => (exp x, exp y)
  exp_spec := by intro (x,y) i; cases i <;> simp[getElem,vector_to_spec]
