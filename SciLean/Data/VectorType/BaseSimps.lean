import SciLean.Data.VectorType.Base

namespace SciLean.VectorType

variable
  {X : Type*} {n : Type u} {R K :  Type*}
  {_ : RealScalar R} {_ : Scalar R K} {_ : IndexType n} [VectorType.Base X n K] [InjectiveGetElem X n]


@[simp, simp_core]
theorem scal_one (x : X) :
    scal 1 x = x := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem scal_zero_a (x : X) :
    scal 0 x = 0 := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem scal_zero_x (a : K) :
    scal a (0:X) = 0 := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem axpy_zero_a (x y : X) :
    axpy 0 x y = y := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem axpy_zero_x (a : K) (y : X) :
    axpy a 0 y = y := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem axpy_zero_y (a : K) (x : X) :
    axpy a x 0 = scal a x := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem axpby_zero_a (b : K) (x y : X) :
    axpby 0 x b y = scal b y := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem axpby_zero_b (a : K) (x y : X) :
    axpby a x 0 y = scal a x := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem axpby_zero_x (a b : K) (y : X) :
    axpby a 0 b y = scal b y := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem axpby_zero_y (a b : K) (x : X) :
    axpby a x b 0 = scal a x := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem axpby_self_xy (a b : K) (x : X) :
    axpby a x b x = scal (a+b) x := by ext i; simp[vector_to_spec]; ring

@[simp, simp_core]
theorem scalAdd_zero_a [Dense X] (b : K) (x : X) :
    scalAdd 0 b x = const b := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem scalAdd_zero_b  [Dense X] (a : K) (x : X) :
    scalAdd a 0 x = scal a x := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem scalAdd_zero_x [Dense X] (a b : K) :
    scalAdd a b (0:X) = const b := by ext i; simp[vector_to_spec]

@[simp, simp_core]
theorem dot_zero_x (y : X) :
    dot 0 y = 0 := by simp[vector_to_spec]

@[simp, simp_core]
theorem dot_zero_y (x : X) :
    dot x 0 = 0 := by simp[vector_to_spec]

----------------------------------------------------------------------------------------------------

@[blas_to_module]
theorem scal_to_module (a : K) (x : X) :
   scal a x = a • x := by ext i; simp[vector_to_spec]

@[blas_to_module]
theorem scalAdd_to_module [Dense X] (a b : K) (x : X) :
   scalAdd a b x = a • x + b • (const 1) := by ext i; simp[vector_to_spec]

@[blas_to_module]
theorem dot_to_module (x y : X) :
   dot x y = (Inner.inner (𝕜:=K) x y) := by rfl

@[blas_to_module]
theorem axpby_to_module (a b : K) (x y : X) :
   axpby a x b y = a • x + b • y := by ext i; simp[vector_to_spec]

@[blas_to_module]
theorem axpy_to_module (a : K) (x y : X) :
   axpy a x y = a • x + y := by ext i; simp[vector_to_spec]


----------------------------------------------------------------------------------------------------

@[rsimp]
theorem foldl_updateElem_add [Dense X] (u : n → K) (x : X) :
  IndexType.foldl (fun x i => updateElem x i fun xi => xi + u i) x
  =
  x + fromVec u := sorry_proof

@[rsimp]
theorem foldl_updateElem_add' [Dense X] (u : n → K) (x : X) :
  IndexType.foldl (fun x i => updateElem x i fun xi => u i + xi) x
  =
  x + fromVec u := by simp only [add_comm,foldl_updateElem_add]


----------------------------------------------------------------------------------------------------

@[vector_from_spec]
theorem fromVec_const [Dense X] (k : K) :
    fromVec (X:=X) (fun _ : n => k) = const k := by
  ext i; simp [vector_to_spec]

@[vector_from_spec]
theorem fromVec_mul [Dense X] (x y : n → K) :
    fromVec (X:=X) (x * y) = mul (fromVec x) (fromVec y) := by
  ext i; simp [vector_to_spec]

@[vector_from_spec]
theorem fromVec_mul' [Dense X] (x y : n → K) :
    fromVec (X:=X) (fun i => x i * y i) = mul (fromVec (fun i => x i)) (fromVec (fun i => y i)) := by
  ext i; simp [vector_to_spec]

@[vector_from_spec]
theorem fromVec_exp [Dense X] (x : n → K) :
    fromVec (X:=X) (fun i => Scalar.exp (x i)) = exp (fromVec x) := by
  ext i; simp [vector_to_spec]

@[vector_to_spec]
theorem toVec_finset_sum {I} [Fintype I] (A : Finset I) (f : I → X) (j : n) :
    (A.sum f)[j] = A.sum (fun i => (f i)[j]) := by
  sorry_proof
