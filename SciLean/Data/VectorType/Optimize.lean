import SciLean.Data.VectorType.Basic

namespace SciLean.VectorType

variable
  {X : (n : Type u) → [IndexType n] → Type*} {n : Type u} {R K :  Type*}
  [Scalar R K] [IndexType n] [VectorType X K]


--- arithmetic operations to axp(b)y and scal

@[vector_optimize]
theorem add_to_axpy (x y : X n) : x+y = axpy 1 x y := by rfl

@[vector_optimize]
theorem sub_to_axpby (x y : X n) : x-y = axpby 1 (-1) x y := by rfl

@[vector_optimize]
theorem neg_to_scal (x : X n) : -x = scal (-1) x := by rfl

@[vector_optimize]
theorem smul_to_scal (a : K) (x : X n) : a•x = scal a x := by rfl


-- scal composition

@[vector_optimize]
theorem scal_scal (a b : K) (x : X n) : scal a (scal b x)  = scal (a*b) x := by
  apply equiv.injective
  simp[vector_to_spec,smul_smul]


-- scal axpy composition

@[vector_optimize]
theorem scal_axpy (a b : K) (x : X n) : scal a (axpy b x y)  = axpby (a*b) a x y := by
  apply equiv.injective
  simp[vector_to_spec,smul_smul]

@[vector_optimize]
theorem scal_axpby (a b c : K) (x : X n) : scal a (axpby b c x y)  = axpby (a*b) (a*c) x y := by
  apply equiv.injective
  simp[vector_to_spec,smul_smul]


-- axpy scal composition

@[vector_optimize]
theorem axpy_scal_left (a b : K) (x : X n) : (axpy a (scal b x) y)  = axpy (a*b) x y := by
  apply equiv.injective
  simp[vector_to_spec,smul_smul]

@[vector_optimize]
theorem axpy_scal_right (a b : K) (x : X n) : (axpy a x (scal b y))  = axpby a b x y := by
  apply equiv.injective
  simp[vector_to_spec,smul_smul]

@[vector_optimize]
theorem axpby_scal_left (a b c : K) (x : X n) : (axpby a b (scal c x) y)  = axpby (a*c) b x y := by
  apply equiv.injective
  simp[vector_to_spec,smul_smul]

@[vector_optimize]
theorem axpby_scal_right (a b c : K) (x : X n) : (axpby a b x (scal c y))  = axpby a (b*c) x y := by
  apply equiv.injective
  simp[vector_to_spec,smul_smul]
