import SciLean.Util.SorryProof
import Mathlib.Order.Defs.PartialOrder
import Std.Tactic.BVDecide

private unsafe def USize.toInt64Impl (x : USize) : Int64 := unsafeCast x.toUInt64

@[implemented_by USize.toInt64Impl]
def USize.toInt64 (x : USize) : Int64 :=
  if x < USize.size/2 then
    .ofNat x.toNat
  else
    (x.1.toInt - USize.size).toInt64

def Int64.toUSize (x : Int64) : USize := x.toISize.toUSize

instance : Preorder Int64 where
  le_refl := by bv_decide
  le_trans := sorry_proof
  lt_iff_le_not_le := sorry_proof
