module

public import SciLean.Util.SorryProof
public import Mathlib.Order.Defs.PartialOrder
public import Std.Tactic.BVDecide

@[expose] public section


private unsafe def USize.toInt64Impl (x : USize) : Int64 := unsafeCast x.toUInt64

@[implemented_by USize.toInt64Impl]
def USize.toInt64 (x : USize) : Int64 :=
  if x.toNat < USize.size/2 then
    .ofNat x.toNat
  else
    (Int.ofNat x.toNat - USize.size).toInt64

def Int64.toUSize (x : Int64) : USize := x.toISize.toUSize

instance : Preorder Int64 where
  le_refl := by bv_decide
  le_trans _ _ _ := Int64.le_trans
  lt_iff_le_not_ge a b := by
    simp only [Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt]
    omega
