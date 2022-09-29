import SciLean.Data.DataArray.DataArray

namespace SciLean

--------------- UInt1 ---------------
-------------------------------------

def UInt1.size : Nat := 2

structure UInt1 where
  val : UInt8
  property : val < 2

instance : Inhabited UInt1 := ⟨0, by decide⟩
instance : ToString UInt1 := ⟨λ x => s!"{x.1}"⟩

@[inline]
opaque UInt1.getByteData (d : ByteData) (i : Nat) (h : d.InBounds i .oneBit) : UInt1 :=
  let d : ByteArray := cast sorry_proof d
  let byte := i / 8
  let bit  : UInt8 := (i % 8).toUInt8
  ⟨(d[byte]'sorry_proof &&& (1 <<< bit)) >>> bit, sorry_proof⟩

@[inline]
opaque UInt1.setByteData (d : ByteData) (i : Nat) (h : d.InBounds i .oneBit) (val : UInt1) : ByteData :=
  let d : ByteArray := cast sorry_proof d
  let byte := i / 8
  let bit  : UInt8 := (i % 8).toUInt8
  let byteVal := d[byte]'sorry_proof
  cast sorry_proof (d.set ⟨byte,sorry_proof⟩ (byteVal ||| (val.1 <<< bit)))

instance : ByteType UInt1 where
  size := .oneBit
  get := UInt1.getByteData
  set := UInt1.setByteData

instance : ByteType Bool where
  size := .oneBit
  get := λ d i h => match (UInt1.getByteData d i h) with | ⟨⟨0,_⟩,_⟩ => false | ⟨⟨1,_⟩,_⟩ => true
  set := λ d i h val => UInt1.setByteData d i h (match val with | false => ⟨0, sorry_proof⟩ | true => ⟨1, sorry_proof⟩)

def data1 := DataArray.intro λ i : Fin 7 => UInt1.mk (i.1 % 2).toUInt8 sorry_proof
#eval data1

--------------- UInt2 ---------------
-------------------------------------

def UInt2.size : Nat := 4

structure UInt2 where
  val : UInt8
  property : val < 4

instance : Inhabited UInt2 := ⟨0, by decide⟩
instance : ToString UInt2 := ⟨λ x => s!"{x.1}"⟩

@[inline]
opaque UInt2.getByteData (d : ByteData) (i : Nat) (h : d.InBounds i .twoBits) : UInt2 :=
  let d : ByteArray := cast sorry_proof d
  let byte := i / 4
  let bit  : UInt8 := 2*(i % 4).toUInt8
  ⟨(d[byte]'sorry_proof &&& (3 <<< bit)) >>> bit, sorry_proof⟩

@[inline]
opaque UInt2.setByteData (d : ByteData) (i : Nat) (h : d.InBounds i .twoBits) (val : UInt2) : ByteData :=
  let d : ByteArray := cast sorry_proof d
  let byte := i / 4
  let bit  : UInt8 := 2*(i % 4).toUInt8
  let byteVal := d[byte]'sorry_proof
  let mask : UInt8 := (255 : UInt8) - (3 <<< bit)
  cast sorry_proof (d.set ⟨byte,sorry_proof⟩ ((byteVal &&& mask) + (val.1 <<< bit)))

instance : ByteType UInt2 where
  size := .twoBits
  get := UInt2.getByteData
  set := UInt2.setByteData

def data2 := DataArray.intro λ i : Fin 15 => UInt2.mk (i.1 % 4).toUInt8 sorry_proof
#eval data2

--------------- UInt4 ---------------
-------------------------------------

def UInt4.size : Nat := 4

structure UInt4 where
  val : UInt8
  property : val < 16

instance : Inhabited UInt4 := ⟨0, by decide⟩
instance : ToString UInt4 := ⟨λ x => s!"{x.1}"⟩

@[inline]
opaque UInt4.getByteData (d : ByteData) (i : Nat) (h : d.InBounds i .fourBits) : UInt4 :=
  let d : ByteArray := cast sorry_proof d
  let byte := i / 2
  let bit  : UInt8 := 4*(i % 2).toUInt8
  ⟨(d[byte]'sorry_proof &&& (15 <<< bit)) >>> bit, sorry_proof⟩

@[inline]
opaque UInt4.setByteData (d : ByteData) (i : Nat) (h : d.InBounds i .fourBits) (val : UInt4) : ByteData :=
  let d : ByteArray := cast sorry_proof d
  let byte := i / 2
  let bit  : UInt8 := 4*(i % 2).toUInt8
  let byteVal := d[byte]'sorry_proof
  let mask : UInt8 := (255 : UInt8) - (15 <<< bit)
  cast sorry_proof (d.set ⟨byte,sorry_proof⟩ ((byteVal &&& mask) + (val.1 <<< bit)))

instance : ByteType UInt4 where
  size := .fourBits
  get := UInt4.getByteData
  set := UInt4.setByteData

def data4 := DataArray.intro λ i : Fin 100 => UInt4.mk (i.1 % 16).toUInt8 sorry_proof
#eval data4


--------------- UInt8 ---------------
-------------------------------------

@[inline]
opaque UInt8.getByteData (d : ByteData) (i : Nat) (h : d.InBounds i (.bytes 1)) : UInt8 :=
  let d : ByteArray := cast sorry_proof d
  let byte := i
  d[byte]'sorry_proof

@[inline]
opaque UInt8.setByteData (d : ByteData) (i : Nat) (h : d.InBounds i (.bytes 1)) (val : UInt8) : ByteData :=
  let d : ByteArray := cast sorry_proof d
  cast sorry_proof (d.set ⟨i,sorry_proof⟩ val)

instance : ByteType UInt8 where
  size := .bytes 1
  get := UInt8.getByteData
  set := UInt8.setByteData

def data8 := DataArray.intro λ i : Fin 300 => (i.1 % 256).toUInt8
#eval data8


--------------- UInt16 ---------------
--------------------------------------

-- TODO: Implement this in C
@[inline]
opaque UInt16.getByteData (d : ByteData) (i : Nat) (h : d.InBounds i (.bytes 2)) : UInt16 :=
  let d : ByteArray := cast sorry_proof d
  let byte := 2*i
  (d[byte]'sorry_proof).toUInt16 + ((d[byte+1]'sorry_proof).toUInt16 <<< 8)

@[inline]
opaque UInt16.setByteData (d : ByteData) (i : Nat) (h : d.InBounds i (.bytes 2)) (val : UInt16) : ByteData :=
  let d : ByteArray := cast sorry_proof d
  let byte := 2*i
  cast sorry_proof $ (d.set ⟨byte,sorry_proof⟩ val.toUInt8).set ⟨byte+1,sorry_proof⟩ (val >>> 8).toUInt8

instance : ByteType UInt16 where
  size := .bytes 2
  get := UInt16.getByteData
  set := UInt16.setByteData

def data16 := DataArray.intro λ i : Fin 300 => (i.1*i.1*i.1).toUInt16
#eval data16

#eval ((129 : UInt8) <<< 1) >>> 1

