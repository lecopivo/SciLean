import SciLean.Data.VectorType.Base

namespace SciLean.VectorType

variable
  {X : Type*} {n : Type u} {R K :  Type*}
  [Scalar R R] [Scalar R K] [IndexType n] [VectorType.Base X n K]


--- arithmetic operations to axp(b)y and scal

@[vector_optimize]
theorem add_to_axpy (x y : X) : x+y = axpby 1 1 x y := by
  apply equiv.injective
  simp[vector_to_spec]

@[vector_optimize]
theorem sub_to_axpby (x y : X) : x-y = axpby 1 (-1) x y := by rfl

@[vector_optimize]
theorem neg_to_scal (x : X) : -x = scal (-1) x := by rfl

@[vector_optimize]
theorem smul_to_scal (a : K) (x : X) : a•x = scal a x := by rfl


-- remove axpy

-- We case every  axpy` to `axpby` as the writting out all the combinations of `axp(b)y`
-- was getting too tedious
@[vector_optimize]
theorem axpy_to_axpby (a : K) (x y : X) : axpy a x y = axpby a 1 x y := by
  apply equiv.injective
  simp[vector_to_spec]


-- axpby right associate

/-- Associate `axpby` to the right.

We associated `axpby` to the right as the right hand side can be used destructivelly and not the
left hand side. -/
@[vector_optimize]
theorem axpby_assoc_right (a b c d : K) (x y z: X) :
    axpby a b (axpby c d x y) z  = axpy (a*c) x (axpby (a*d) b y z) := by
  apply equiv.injective
  simp[vector_to_spec,smul_smul,add_assoc]


-- scal composition

@[vector_optimize]
theorem scal_scal (a b : K) (x : X) : scal a (scal b x)  = scal (a*b) x := by
  apply equiv.injective
  simp[vector_to_spec,smul_smul]


-- scal axpy composition

@[vector_optimize]
theorem scal_axpby (a b c : K) (x : X) : scal a (axpby b c x y)  = axpby (a*b) (a*c) x y := by
  apply equiv.injective
  simp[vector_to_spec,smul_smul]


-- axpy scal composition

@[vector_optimize]
theorem axpby_scal_left (a b c : K) (x : X) : (axpby a b (scal c x) y)  = axpby (a*c) b x y := by
  apply equiv.injective
  simp[vector_to_spec,smul_smul]

@[vector_optimize]
theorem axpby_scal_right (a b c : K) (x : X) : (axpby a b x (scal c y))  = axpby a (b*c) x y := by
  apply equiv.injective
  simp[vector_to_spec,smul_smul]


-- dot const

open ComplexConjugate in
@[vector_optimize]
theorem dot_const_left (a : K) (x : X) : dot (const a) x  = conj a * sum x := by
  simp[vector_to_spec,smul_smul,Finset.mul_sum]

open ComplexConjugate in
@[vector_optimize]
theorem dot_const_right (a : K) (x : X) : dot x (const a)  = conj (sum x) * a := by
  simp[vector_to_spec,smul_smul,Finset.sum_mul]
