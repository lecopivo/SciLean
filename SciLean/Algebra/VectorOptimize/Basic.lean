import SciLean.Algebra.VectorOptimize.Init
import SciLean.Algebra.TensorProduct.Basic
import SciLean.Algebra.MatrixType.Basic

namespace SciLean

/--
Type `X` provides fused multiply add operation
```
axpby a x b y = a • x + b • y
```
for `a b : R`.

Expression involing `•` and `+` can be optimized by running `simp only [vector_optimize]`

For example:
```
-- axpby (a*b) x c (apxby 1 y d z)
#check (a•b•x + c•(y + d•z)) rewrite_by simp only [vector_optimize]
```
Which effectivelly reduces six loops(for every operation) into two loops.
-/
class Axpby (R : outParam Type*) (X : Type*) [Ring R] [AddCommGroup X] [Module R X] where
  /--
  Fused vector add multiply operation
  ```
  axpby a x b y = a • x + b • y
  ```
  Used to optimize expressions involving `•` and `+`.

  You can optimize expression by running `simp only [vector_optimize]`

  For example:
  ```
  -- axpby (a*b) x c (apxby 1 y d z)
  #check (a•b•x + c•(y + d•z)) rewrite_by simp only [vector_optimize]
  ```
  Which effectivelly reduces six loops(for every operation) into two loops.
  -/
  axpby (a : R) (x : X) (b : R) (y : X) : X
  axpby_spec (a : R) (x : X) (b : R) (y : X) :
    axpby a x b y = a•x + b•y

export Axpby (axpby axpby_spec)


variable
  {R Y X YX : Type*} [RCLike R]
  [NormedAddCommGroup Y] [AdjointSpace R Y] [NormedAddCommGroup X] [AdjointSpace R X]
  [AddCommGroup YX] [Module R YX]
  [TensorProductType R Y X YX]


----------------------------------------------------------------------------------------------------
-- Basic simp rules to use for vector_optimize -----------------------------------------------------
----------------------------------------------------------------------------------------------------

attribute [vector_optimize] smul_smul smul_neg one_mul neg_mul
attribute [vector_optimize ←] neg_smul pow_succ pow_succ'


----------------------------------------------------------------------------------------------------
-- Basic axpby optimization  -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section Axpby

variable
  {R : Type*} [Field R]
  {X : Type*} [AddCommGroup X] [Module R X] [Axpby R X]

@[vector_optimize]
theorem add_eq_axpby  (x y : X) :
    x + y = axpby (1:R) x (1:R) y := by simp[axpby_spec]

@[simp, simp_core, vector_optimize]
theorem axpby_smul_x (a b c : R) (x y : X) :
    axpby a (c•x) b y = axpby (a*c) x b y := by simp[axpby_spec]; module

@[simp, simp_core, vector_optimize]
theorem axpby_smul_y (a b c : R) (x y : X) :
    axpby a x b (c•y) = axpby a x (b*c) y := by simp[axpby_spec]; module

@[simp, simp_core, vector_optimize]
theorem axpby_zero_a (b : R) (x y : X) :
    axpby 0 x b y = b•y := by simp[axpby_spec]

@[simp, simp_core, vector_optimize]
theorem axpby_zero_x (a b : R) (y : X) :
    axpby a 0 b y = b•y := by simp[axpby_spec]

@[simp, simp_core, vector_optimize]
theorem axpby_zero_b (a : R) (x y : X) :
    axpby a x 0 y = a•x := by simp[axpby_spec]

@[simp, simp_core, vector_optimize]
theorem axpby_zero_y (a b : R) (x : X) :
    axpby a x b 0 = a•x := by simp[axpby_spec]

@[vector_optimize]
theorem axpby_self (a b : R) (x : X) :
    axpby a x b x = (a+b)•x := by simp[axpby_spec]; module

@[vector_optimize]
theorem axpby_self_y (a b c d : R) (x y : X) :
    axpby a (axpby b x c y) d y = axpby (a*b) x (a*c+d) y := by simp[axpby_spec]; module

@[vector_optimize]
theorem axpby_self_y' (a b c d : R) (x y : X) :
    axpby a (axpby b y c x) d y = axpby (a*c) x (a*b+d) y := by simp[axpby_spec]; module

@[vector_optimize]
theorem axpby_self_x (a b c d : R) (x y : X) :
    axpby a x b (axpby c x d y) = axpby (a+b*c) x (b*d) y := by simp[axpby_spec]; module

@[vector_optimize]
theorem axpby_self_x' (a b c d : R) (x y : X) :
    axpby a x b (axpby c y d x) = axpby (a+b*d) x (b*c) y := by simp[axpby_spec]; module

end Axpby


----------------------------------------------------------------------------------------------------
-- ⊗ optimization  ---------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section TMul

theorem tmulAdd_spec (a : R) (y : Y) (x : X) (A : YX) :
  tmulAdd a y x A = a•(y⊗[R]x) + A := by simp[tmul]; sorry_proof

@[vector_optimize]
theorem tmul_eq_tmulAdd (y : Y) (x : X) :
    y⊗[R]x = tmulAdd (1:R) y x (0:YX) := by  simp [tmulAdd_spec]

@[simp, simp_core, vector_optimize]
theorem tmulAdd_smul_y (a b : R) (y : Y) (x : X) (A : YX) :
    tmulAdd a (b•y) x A = tmulAdd (a*b) y x A := by sorry_proof

@[simp, simp_core, vector_optimize]
theorem tmulAdd_smul_x (a b : R) (y : Y) (x : X) (A : YX) :
    tmulAdd a y (b•x) A = tmulAdd (a*b) y x A := by
  simp [axpby_spec,tmulAdd_spec]
  sorry_proof


variable [Axpby R YX]

@[vector_optimize]
theorem axpby_x_tmulAdd_eq_tmulAdd_axpby (a b c : R) (y : Y) (x : X) (A B : YX) :
    axpby a (tmulAdd b y x A) c B = tmulAdd (a*b) y x (axpby a A c B) := by
  simp [axpby_spec,tmulAdd_spec]; module

@[vector_optimize]
theorem axpby_y_tmulAdd_eq_tmulAdd_axpby (a b c : R) (y : Y) (x : X) (A B : YX) :
    axpby a B b (tmulAdd c y x A) = tmulAdd (b*c) y x (axpby b A a B) := by
  simp [axpby_spec,tmulAdd_spec]; module

end TMul


----------------------------------------------------------------------------------------------------
-- Matrix-vector multiplication  -------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section MatVecMulAdd


attribute [vector_optimize]
  matVecMulAdd_zero_a
  matVecMulAdd_zero_A
  matVecMulAdd_zero_x
  vecMatMulAdd_zero_a
  vecMatMulAdd_zero_A
  vecMatMulAdd_zero_y


theorem matVecMulAdd_spec (a b : R) (A : YX) (x : X) (y : Y) :
    matVecMulAdd a A x b y
    =
    have : MatrixType R Y X YX := ⟨⟩
    have : MatrixMulNotation YX := ⟨⟩
    a•(A*x) + b•y := sorry_proof

@[vector_optimize]
theorem matVecMul_eq_matVecMulAdd
    {M : Type*} [AddCommGroup M] [Module R M] [MatrixType R Y X M] [MatrixMulNotation M]
    (A : M) (x : X) :
    A * x = matVecMulAdd (1:R) A x (0:R) (0:Y) := by simp[matVecMulAdd_spec]

variable [Axpby R Y]

@[vector_optimize]
theorem axpby_x_matVecMulAdd_eq_matVecMulAdd (a b c d : R) (y z : Y) (x : X) (A : YX) :
    axpby a (matVecMulAdd b A x c y) d z
    =
    matVecMulAdd (a*b) A x 1 (axpby (a*c) y d z) := by
  simp [axpby_spec,matVecMulAdd_spec]; module

@[vector_optimize]
theorem axpby_y_matVecMulAdd_eq_matVecMulAdd (a b c d : R) (y z : Y) (x : X) (A : YX) :
    axpby a z d (matVecMulAdd b A x c y)
    =
    matVecMulAdd (d*b) A x 1 (axpby a z (d*c) y) := by
  simp [axpby_spec,matVecMulAdd_spec]; module

end MatVecMulAdd

----------------------------------------------------------------------------------------------------
-- Vector-Matrix Multiplication  -------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section VecMatMulAdd

theorem vecMatMulAdd_spec (a b : R) (A : YX) (x : X) (y : Y) :
    vecMatMulAdd a y A b x
    =
    have : MatrixType R Y X YX := ⟨⟩
    have : MatrixMulNotation YX := ⟨⟩
    a•(y*A) + b•x := sorry_proof

@[vector_optimize]
theorem vecMatMul_eq_vecMatMulAdd
    {M : Type*} [AddCommGroup M] [Module R M] [MatrixType R Y X M] [MatrixMulNotation M]
    (A : M) (y : Y) :
    y * A = vecMatMulAdd (1:R) y A (0:R) (0:X) := by simp[vecMatMulAdd_spec]

variable [Axpby R X]

@[vector_optimize]
theorem axpby_x_vecMatMulAdd_eq_vecMatMulAdd (a b c d : R) (y : Y) (x z : X) (A : YX) :
    axpby a (vecMatMulAdd b y A c x) d z
    =
    vecMatMulAdd (a*b) y A 1 (axpby (a*c) x d z) := by
  simp [axpby_spec,vecMatMulAdd_spec]; module

@[vector_optimize]
theorem axpby_y_vecMatMulAdd_eq_vecMatMulAdd (a b c d : R) (y : Y) (x z : X) (A : YX) :
    axpby a z d (vecMatMulAdd b y A c x)
    =
    vecMatMulAdd (d*b) y A 1 (axpby (d*c) x a z) := by
  simp [axpby_spec,vecMatMulAdd_spec]; module

end VecMatMulAdd

end SciLean
