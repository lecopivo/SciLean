namespace SciLean

@[unbox]
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

instance : ToString Int64 := ⟨fun i => if i.isPositive then toString i.absValue else s!"-{i.absValue}"⟩
instance : OfNat Int64 n := ⟨⟨n.toUSize⟩⟩
instance : Add Int64 := ⟨fun x y => ⟨x.toUSize + y.toUSize⟩⟩
instance : Sub Int64 := ⟨fun x y => ⟨x.toUSize - y.toUSize⟩⟩
instance : Neg Int64 := ⟨fun x   => ⟨(0:USize) - (x.toUSize)⟩⟩
instance : Mul Int64 := ⟨fun x y => ⟨x.toUSize * y.toUSize⟩⟩






