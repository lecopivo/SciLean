import SciLean.Data.DataArray.DataArray
import SciLean.Data.VectorType.Base
import SciLean.Data.MatrixType.Base
import SciLean.Data.FloatArray

import SciLean.Analysis.Scalar.FloatAsReal

import LeanBLAS
-- import SciLean.Data.FloatVector

namespace SciLean


/-- This class says that `Array` is the canonical `Array` storing sequence of scalars `R`.
It provides BLAS operations on `Array` that are used to implement vector space operations on `X`.

TODO: `Array` should not be `outParam` but we should employ similar trick as with `defaultScalar%`
      This way we could say that we want to for example use arrays on CPU *or* GPU.

      It is `outParam` for now for simplicity.

TODO: Also figure out what to do about complex numbers.
      Probaly ditch `R` *and* `K` type arguments on all BLAS functions. -/
class ScalarArray (R : Type*) (Array : outParam Type*) [PlainDataType R] [RealScalar R]
  extends
    BLAS Array R R
  where
    equiv : DataArray R ≃ Array

namespace ScalarArray

variable {R : Type*} {Array : Type*} [PlainDataType R] [RealScalar R] [ScalarArray R Array]

@[simp]
theorem size_equiv (x : DataArray R) :
    BLAS.LevelOneData.size (ScalarArray.equiv x) = x.size := sorry_proof

@[simp]
theorem size_symm_equiv (x : Array) :
    ((ScalarArray.equiv (R:=R)).symm x).size = BLAS.LevelOneData.size x := sorry_proof


instance : ScalarArray Float FloatArray where
  equiv := {
    toFun x := x.byteData.toFloatArray sorry_proof
    invFun a := ⟨a.toByteArray, a.size, sorry_proof⟩
    left_inv := sorry_proof
    right_inv := sorry_proof
  }

end ScalarArray


/-- This instance says that `X` is equivalent to an array of `size I` scalars and it will
automatically provide vector space structure on `X` through this equivalence. For this purpose
it is expected that this equivalence is cheap at runtime.

The index type `I` is the canonical type to index scalar compotents of `X`. -/
class ScalarArrayEquiv (X : Type*) (Array I R K : outParam Type*)
    [Size I] [BLAS.LevelOneData Array R K] where
  /-- Array of `X` as byte array (this is `DataArray X`) can be converted to an array of scalars
  that has `m*(size I)` elements for appropriate `I`. -/
  equiv : X ≃ { a : Array // BLAS.LevelOneData.size a = size I }

namespace ScalarArrayEquiv

/-- `ScalarArray` implies `ScalarArrayEquiv` -/
instance {R Array I} [RealScalar R] [PlainDataType R] [ScalarArray R Array] [IndexType I]
    [BLAS.LevelOne Array R R] :
    ScalarArrayEquiv (R^[I]) Array I R R where
  equiv := {
    toFun x := ⟨ScalarArray.equiv x.1, by have h := x.2; simp_all⟩
    invFun a := ⟨ScalarArray.equiv.symm a.1, by have := a.2; simp_all⟩
    left_inv := by intro x; simp
    right_inv := by intro x; simp
  }

end ScalarArrayEquiv
