import SciLean.Prelude
import SciLean.Data.DataArray.DataArray

namespace SciLean

--------------- Prod -----------------
--------------------------------------

def Prod.bitSize (α β : Type) [ba : ByteType α] [bb : ByteType β] : BitSize :=
  match ba.size, bb.size with
  | .oneBit, .oneBit => .twoBits
  | .oneBit, .twoBits => .fourBits
  | .oneBit, .fourBits => .bytes 1
  | .oneBit, .bytes n => .bytes (n+1)
  | .twoBits, .oneBit => .fourBits
  | .twoBits, .twoBits => .fourBits
  | .twoBits, .fourBits => .bytes 1
  | .twoBits, .fourBits => .bytes 1
  if n ≤ 2^1 then .oneBit
  else if n ≤ 2^2 then .twoBits
  else if n ≤ 2^4 then .fourBits
  else if n ≤ 2^8 then .bytes 1
  else if n ≤ 2^16 then .bytes 2
  else panic! s!"ByteType is not supported for Fin n with n > 2^16. Used with n={n}!"

@[inline]
opaque Fin.getByteData (n : Nat) [Fact (n≠0)] (d : ByteData) (i : Nat) (h : d.InBounds i (Fin.bitSize n)) : Fin n :=
  match (Fin.bitSize n) with
  | .oneBit   => ⟨(UInt1.getByteData d i sorry_proof).1.toNat, sorry_proof⟩
  | .twoBits  => ⟨(UInt2.getByteData d i sorry_proof).1.toNat, sorry_proof⟩
  | .fourBits => ⟨(UInt4.getByteData d i sorry_proof).1.toNat, sorry_proof⟩
  | .bytes 1  => ⟨(UInt8.getByteData d i sorry_proof).toNat, sorry_proof⟩
  | .bytes 2  => ⟨(UInt16.getByteData d i sorry_proof).toNat, sorry_proof⟩
  | .bytes _ => panic! s!"ByteType is not supported for Fin n with n > 2^16. Used with n={n}!"

@[inline]
opaque Fin.setByteData (n : Nat) (d : ByteData) (i : Nat) (h : d.InBounds i (Fin.bitSize n)) (val : Fin n) : ByteData :=
  match (Fin.bitSize n) with
  | .oneBit   => UInt1.setByteData d i sorry_proof ⟨val.1.toUInt8, sorry_proof⟩
  | .twoBits  => UInt2.setByteData d i sorry_proof ⟨val.1.toUInt8, sorry_proof⟩
  | .fourBits => UInt4.setByteData d i sorry_proof ⟨val.1.toUInt8, sorry_proof⟩
  | .bytes 1  => UInt8.setByteData d i sorry_proof val.1.toUInt8
  | .bytes 2  => UInt16.setByteData d i sorry_proof val.1.toUInt16
  | .bytes _ => @panic _ ⟨d⟩ s!"ByteType is not supported for Fin n with n > 2^16. Used with n={n}!"

instance (n) [Fact (n≠0)] : ByteType (Fin n) where
  size := Fin.bitSize n
  get := Fin.getByteData n
  set := Fin.setByteData n
