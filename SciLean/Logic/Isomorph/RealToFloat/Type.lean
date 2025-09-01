import SciLean.Util.SorryProof
import SciLean.Logic.Isomorph.IsomorphicType

import Mathlib.Data.Real.Basic

namespace SciLean

variable {α α' β β' γ γ' : Type _}
  [IsomorphicType `RealToFloat α α']
  [IsomorphicType `RealToFloat β β']
  [IsomorphicType `RealToFloat γ γ']

/-- This axiom is obviously contradictory. We use it to compile programs that were designed only for reals or proper fields. With this axiom we can plug `Float` to function that would only accept types that have instance of `RCLike`

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


instance instIsomorphicTypeRealToFloatProd [IsomorphicType `RealToFloat α α'] [IsomorphicType `RealToFloat β β'] : IsomorphicType `RealToFloat (α×β) (α'×β') where
  equiv :=
  {
    toFun  := fun (a,b) => (IsomorphicType.equiv `RealToFloat a, IsomorphicType.equiv `RealToFloat b)
    invFun := fun (a',b') => ((IsomorphicType.equiv `RealToFloat).symm a', (IsomorphicType.equiv `RealToFloat).symm b')
    left_inv := by intro (a,b); simp
    right_inv := by intro (a',b'); simp
  }


instance [IsomorphicType `RealToFloat α α'] [IsomorphicType `RealToFloat β β'] : IsomorphicType `RealToFloat (α→β) (α'→β') where
  equiv :=
  {
    toFun  := fun f a  => IsomorphicType.equiv `RealToFloat (f ((IsomorphicType.equiv `RealToFloat).symm a))
    invFun := fun f a' => (IsomorphicType.equiv `RealToFloat).symm (f (IsomorphicType.equiv `RealToFloat a'))
    left_inv := by intro f; simp[-isomorph.app]
    right_inv := by intro f; simp
  }

instance (priority := 1) isntIsomorphicTypeId {α : Sort u} : IsomorphicType `RealToFloat α α where
  equiv :=
  {
    toFun := id
    invFun := id
    left_inv := by intro a; simp
    right_inv := by intro a; simp
  }

@[simp high]
theorem isomorphicType_equiv_id {α : Type _} (a : α)
  : (IsomorphicType.equiv `RealToFloat) a = a := by rfl



abbrev realToFloat (x : ℝ) : Float := IsomorphicType.equiv `RealToFloat x

abbrev floatToReal (x : Float) : ℝ := IsomorphicType.equiv `FloatToReal x
