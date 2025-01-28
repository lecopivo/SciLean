import SciLean.Data.VectorType.Base
-- import SciLean.Data.VectorType.Dense

namespace SciLean.VectorType

variable
  {X : Type*} {n : Type u} {R K :  Type*}
  {_ : RealScalar R} {_ : Scalar R K} {_ : IndexType n} [VectorType.Base X n K] [VectorType.Lawful X]


--- arithmetic operations to axp(b)y and scal

@[vector_optimize]
theorem add_to_axpy (x y : X) : x+y = axpby 1 x 1 y := by
  ext
  simp[vector_to_spec]

-- omit [Lawful X] in
@[vector_optimize]
theorem sub_to_axpby (x y : X) : x-y = axpby 1 x (-1) y := by rfl

-- omit [Lawful X] in
@[vector_optimize]
theorem neg_to_scal (x : X) : -x = scal (-1) x := by rfl

-- omit [Lawful X] in
@[vector_optimize]
theorem smul_to_scal (a : K) (x : X) : a•x = scal a x := by rfl

@[vector_optimize]
theorem inner_to_dot (x y : X) : (Inner.inner (𝕜:=K) x y) = dot x y := by rfl


-- remove axpy

-- We case every  axpy` to `axpby` as the writting out all the combinations of `axp(b)y`
-- was getting too tedious
@[vector_optimize]
theorem axpy_to_axpby (a : K) (x y : X) : axpy a x y = axpby a x 1 y := by
  ext
  simp[vector_to_spec]


-- axpby right associate

/-- Associate `axpby` to the right.

We associated `axpby` to the right as the right hand side can be used destructivelly and not the
left hand side. -/
@[vector_optimize]
theorem axpby_assoc_right (a b c d : K) (x y z: X) :
    axpby a (axpby c x d y) b z  = axpy (a*c) x (axpby (a*d) y b z) := by
  ext
  simp[vector_to_spec,smul_smul,add_assoc]


-- scal composition

@[vector_optimize]
theorem scal_scal (a b : K) (x : X) : scal a (scal b x)  = scal (a*b) x := by
  ext
  simp[vector_to_spec,smul_smul,mul_assoc]


-- scal axpy composition

@[vector_optimize]
theorem scal_axpby (a b c : K) (x : X) : scal a (axpby b x c y)  = axpby (a*b) x (a*c) y := by
  ext
  simp[vector_to_spec,smul_smul,mul_add,mul_assoc]


-- axpy scal composition

@[vector_optimize]
theorem axpby_scal_left (a b c : K) (x : X) : (axpby a (scal c x) b y)  = axpby (a*c) x b y := by
  ext
  simp[vector_to_spec,smul_smul]

@[vector_optimize]
theorem axpby_scal_right (a b c : K) (x : X) : (axpby a x b (scal c y))  = axpby a x (b*c) y := by
  ext
  simp[vector_to_spec,smul_smul]


-- dot const

omit [Lawful X] in
open ComplexConjugate in
@[vector_optimize]
theorem dot_const_left [VectorType.Dense X] (a : K) (x : X) : dot (const a) x  = conj a * sum x := by
  simp[vector_to_spec,smul_smul,Finset.mul_sum]

omit [Lawful X] in
open ComplexConjugate in
@[vector_optimize]
theorem dot_const_right [VectorType.Dense X] (a : K) (x : X) : dot x (const a)  = conj (sum x) * a := by
  simp[vector_to_spec,smul_smul,Finset.sum_mul]


-- axpby scalAdd

@[vector_optimize]
theorem axpby_scalAdd_x [Dense X] (a b c d : K) (x y : X) :
    axpby a (scalAdd c d x) b y = scalAdd 1 (a*d) (axpby (a*c) x b y) := by
  ext i; simp[vector_to_spec]; ring

@[vector_optimize]
theorem axpby_scalAdd_y [Dense X] (a b c d : K) (x y : X) :
    axpby a x b (scalAdd c d y) = scalAdd 1 (b*d) (axpby a x (b*c) y) := by
  ext i; simp[vector_to_spec]; ring

-- axpby const
@[vector_optimize]
theorem axpby_const_x [Dense X] (a b c : K) (y : X) :
  axpby a (const c) b y = scalAdd b (a*c) y := by ext i; simp[vector_to_spec]; ring

@[vector_optimize]
theorem axpby_const_y [Dense X] (a b c : K) (x : X) :
  axpby a x b (const c) = scalAdd a (b*c) x := by ext i; simp[vector_to_spec]


-- scalAdd scalAdd

@[vector_optimize]
theorem scalAdd_scalAdd [Dense X] (a b c d : K) (x : X) :
    scalAdd a b (scalAdd c d x) = scalAdd (a*c) (a*d+b) x := by
  ext i; simp[vector_to_spec]; ring

-- scalAdd scal

@[vector_optimize]
theorem scalAdd_scal [Dense X] (a b c : K) (x : X) :
    scalAdd a b (scal c x) = scalAdd (a*c) b x := by
  ext i; simp[vector_to_spec]; ring
