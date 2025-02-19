import SciLean.Data.MatrixType.Base
import SciLean.Data.MatrixType.Dense

namespace SciLean.MatrixType

variable
  {R K :  Type*} {_ : RealScalar R} {_ : Scalar R K}
  {n : Type*} {_ : IndexType n}
  {m : Type*} {_ : IndexType m}
  {X : Type*} [VectorType.Base X n K] [InjectiveGetElem X n]
  {Y : Type*} [VectorType.Base Y m K] [InjectiveGetElem Y m]
  {M : Type*} [MatrixType.Base M X Y] [InjectiveGetElem M (m×n)]

open VectorType MatrixType


--  gemv and axpby


omit [InjectiveGetElem X n] [InjectiveGetElem M (m × n)] in
@[vector_optimize]
theorem axpby_gemv_zero_left (a b c d : K) (A : M) (x : X) (y : Y) :
    axpby a y b (gemv c d A x 0) = gemv (b*c) a A x y := by
  ext i; simp[vector_to_spec,matrix_to_spec]; ring

omit [InjectiveGetElem X n] [InjectiveGetElem M (m × n)] in
@[vector_optimize]
theorem axpby_gemv_zero_right (a b c d : K) (A : M) (x : X) (y : Y) :
    axpby b (gemv c d A x 0) a y = gemv (b*c) a A x y := by
  ext i; simp[vector_to_spec,matrix_to_spec]; ring


--  gemv and axpby

omit [InjectiveGetElem Y m] [InjectiveGetElem M (m × n)] in
@[vector_optimize]
theorem axpby_gemvH_zero_left (a b c d : K) (A : M) (x : X) (y : Y) :
    axpby a x b (gemvH c d A y 0) = gemvH (b*c) a A y x := by
  ext i; simp[vector_to_spec,matrix_to_spec]; ring

omit [InjectiveGetElem Y m] [InjectiveGetElem M (m × n)] in
@[vector_optimize]
theorem axpby_gemvH_zero_right (a b c d : K) (A : M) (x : X) (y : Y) :
    axpby b (gemvH c d A y 0) a x = gemvH (b*c) a A y x := by
  ext i; simp[vector_to_spec,matrix_to_spec]; ring


-- outerprodAdd and apxby

omit [InjectiveGetElem X n] [InjectiveGetElem Y m] in
-- we expect that offten `a = 1` and `scal` on the rhs will get optimized away
@[vector_optimize]
theorem axpby_outerprodAdd_zero [Dense M] (a b c : K) (A : M) (x : X) (y : Y) :
    axpby a A b (outerprodAdd c y x 0) = outerprodAdd (b*c) y x (scal a A) := by
  ext ij; cases ij
  simp[toMatrix_eq_toVec, vector_to_spec]
  simp[toVec_eq_toMatrix, matrix_to_spec]
  simp[toMatrix_eq_toVec, vector_to_spec]
  ring


-- updateRow and axpby

omit [InjectiveGetElem X n] [InjectiveGetElem Y m] in
open Classical in
@[vector_optimize]
theorem axpby_updateRow_zero [Dense M] (a b : K) (A : M) (x : X) (i : m) :
    axpby a A b (updateRow 0 i x)
    =
    let ri := row A i
    updateRow (scal a A) i (axpby a ri b x) := by
  ext ij'; rcases ij' with ⟨i',j'⟩
  by_cases h : i' = i <;> simp [h, vector_to_spec]


omit [InjectiveGetElem X n] [InjectiveGetElem Y m] in
@[vector_optimize]
theorem axpby_updateCol_zero [DecidableEq n] [Dense M] (a b : K) (A : M) (y : Y) (j : n) :
    axpby a A b (updateCol 0 j y)
    =
    let cj := col A j
    updateCol (scal a A) j (axpby a cj b y) := by
  ext ij'; rcases ij' with ⟨i',j'⟩
  by_cases h : j' = j <;> simp [h, vector_to_spec]
