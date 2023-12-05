import SciLean.Util.SorryProof

namespace SciLean

structure Int64 : Type where
  val : USize

def Int64.toUSize (x : Int64) : USize := x.val
def Int64.valueMask : USize := ((0:USize)-1) >>> 1
def Int64.signMask : USize := ((0:USize)-(1:USize)) - (((0:USize)-1) >>> 1)
def Int64.isPositive (n : Int64) : Bool := (n.toUSize &&& Int64.signMask) = 0
def Int64.isNegative (n : Int64) : Bool := (n.toUSize &&& Int64.signMask) ≠ 0
def Int64.absValue (n : Int64) : USize := 
  if n.isPositive then
    n.toUSize
  else
    (0:USize) - (n.toUSize)

def Int64.abs (n : Int64) : Int64 := ⟨n.absValue⟩
def Int64.toFloat (n : Int64) : Float := if n.isPositive then n.toUSize.toNat.toFloat else -((0:USize) - (n.toUSize)).toNat.toFloat
def Int64.toNat (n : Int64) : Nat := if n.isPositive then n.toUSize.toNat else 0

def _root_.USize.toInt64 (x : USize) : Int64 := ⟨x⟩
def _root_.Nat.toInt64 (x : Nat) : Int64 := ⟨x.toUSize⟩

instance : ToString Int64 := ⟨fun i => if i.isPositive then toString i.absValue else s!"-{i.absValue}"⟩
instance : OfNat Int64 n := ⟨⟨n.toUSize⟩⟩
instance : Add Int64 := ⟨fun x y => ⟨x.toUSize + y.toUSize⟩⟩
instance : Sub Int64 := ⟨fun x y => ⟨x.toUSize - y.toUSize⟩⟩
instance : Neg Int64 := ⟨fun x   => ⟨(0:USize) - (x.toUSize)⟩⟩
instance : Mul Int64 := ⟨fun x y => ⟨x.toUSize * y.toUSize⟩⟩
instance : Div Int64 := ⟨fun x y => 
  match x.isPositive, y.isPositive with
  | true, true => ⟨x.toUSize / y.toUSize⟩
  | false, true => -⟨(-x).toUSize / y.toUSize⟩
  | true, false => -⟨x.toUSize / (-y).toUSize⟩
  | false, false => ⟨(-x).toUSize / (-y).toUSize⟩⟩

instance : Mod Int64 := ⟨fun x y => 
  match x.isPositive, y.isPositive with
  | true, true => ⟨x.toUSize % y.toUSize⟩
  | false, true => -⟨(-x).toUSize % y.toUSize⟩
  | true, false => ⟨x.toUSize % (-y).toUSize⟩
  | false, false => -⟨(-x).toUSize % (-y).toUSize⟩⟩

def Int64.comp (x y : Int64) : Ordering :=
  match x.isNegative, y.isNegative with
  | true, false => .lt
  | false, true => .gt
  | true, true => compare x.1 y.1
  | false, false => compare x.1 y.1

instance : LE Int64 := ⟨fun x y => x.comp y != .gt⟩
instance : LT Int64 := ⟨fun x y => x.comp y == .lt⟩

instance Int64.decLt (a b : Int64) : Decidable (a < b) := 
  if h : a.comp b == .lt then
    .isTrue h
  else
    .isFalse h

instance Int64.decLe (a b : Int64) : Decidable (a ≤ b) :=
  if h : a.comp b != .gt then
    .isTrue h
  else
    .isFalse h

instance : DecidableEq Int64 := fun x y => if _h : x.1 = y.1 then .isTrue sorry_proof else .isFalse sorry_proof

