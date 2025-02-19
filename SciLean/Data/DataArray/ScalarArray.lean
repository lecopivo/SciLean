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
    BLAS Array R R,
    LawfulBLAS Array R R
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

instance : BLAS.LevelOneSpec FloatArray Float Float := sorry_proof
instance : LawfulBLAS FloatArray Float Float where

instance : ScalarArray Float FloatArray where
  equiv := {
    toFun x := x.byteData.toFloatArray sorry_proof
    invFun a := ⟨a.toByteArray, a.size, sorry_proof⟩
    left_inv := sorry_proof
    right_inv := sorry_proof
  }

end ScalarArray
