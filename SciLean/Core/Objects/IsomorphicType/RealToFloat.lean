import SciLean.Util.SorryProof
import SciLean.Core.Objects.IsomorphicType

import Mathlib.Data.Real.Basic

namespace SciLean

variable {α α' β β' γ γ' : Type _}
  [IsomorphicType `RealToFloat α α']
  [IsomorphicType `RealToFloat β β']
  [IsomorphicType `RealToFloat γ γ']

/-- This axiom is obviously contradictory. We use it to compile programs that were designed only for reals or proper fields. With this axiom we can plug `Float` to function that would only accept types that have instance of `IsROrC`

-/
axiom realFloatEquiv : ℝ ≃ Float 


scoped instance : IsomorphicType `RealToFloat ℝ Float where
  equiv := 
  {
    toFun  := panic! "attempting to convert real to float"
    invFun := panic! "attempting to convert float to real"
    left_inv := sorry_proof
    right_inv := sorry_proof
  }


scoped instance : IsomorphicType `FloatToReal Float ℝ where
  equiv := 
  {
    toFun  := panic! "attempting to convert float to real"
    invFun := panic! "attempting to convert real to float"
    left_inv := sorry_proof
    right_inv := sorry_proof
  }


abbrev realToFloat (x : ℝ) : Float := IsomorphicType.equiv `RealToFloat x

abbrev floatToReal (x : Float) : ℝ := IsomorphicType.equiv `FloatToReal x


