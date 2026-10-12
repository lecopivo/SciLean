module

public import SciLean.FFI.ByteArray

@[expose] public section

@[simp]
theorem ByteArray.size_uset (b : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < b.size) :
    (b.uset i v h).size = b.size := by
  show (b.data.set i.toNat v h).size = b.data.size
  simp
