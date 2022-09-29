import SciLean.Prelude

namespace SciLean

inductive BitSize where | bits (n : UInt8) (h : n < 8) | bytes (n : Nat)
deriving Inhabited

/-- At least `i` elements of size `s` fit into `a` -/
def BitSize.InBounds (s : SciLean.BitSize) (a : ByteArray) (i : Nat)  : Prop :=
match s with
| .bits n _ => i < (8/n).toNat * a.size
| .bytes n  => n*i < a.size

/-- This rougly corresponds to Plain Old Data/Passive Data known from OOP

wiki: https://en.wikipedia.org/wiki/Passive_data_structure

For example and array of fixed length `{a : Array α // a.size = n}` is `PlainDataType` (if `α` is `PlainDataType`)
However, `Array α` is not `PlainDataType` (even if `α` is `PlainDataType`) as it does not have a fixed byte size.
-/
class PlainDataType (α : Type) where
  size : BitSize
  get (d : ByteArray) (i : Nat) (h : size.InBounds d i) : α
  set (d : ByteArray) (i : Nat) (h : size.InBounds d i) (a : α) : ByteArray

  -- get_set       -- setting and getting returns the original
  -- get_set_other -- set does not affects other elements
  -- size_set      -- does not changes ByteData size
  -- ext           -- extensionality of ByteData i.e. if ∀ i h h', get d i h = get d' i h' → d = d'

/- How many bytes are needed to hold n elements of type α -/
def PlainDataType.bytes {α : Type} (pd : PlainDataType α) (n : Nat) : Nat :=
  match pd.size with
  | .bits m _ => (n + ((8/m) - 1).toNat) / (8/m).toNat
  | .bytes m => m * n


--------------- Prod -------------------------------------------------
----------------------------------------------------------------------

def BitSize.ofProd (α β : Type) [pda : PlainDataType α] [pdb : PlainDataType β] : BitSize :=
  match pda.size, pdb.size with
  | .bits n _, .bits m _ => 
    if  h : n + m < 8  then .bits (n+m) h
    else if n + m = 8  then .bytes 1    else .bytes 2
  | .bits _ _, .bytes n | .bytes n, .bits _ _ => .bytes (n+1)
  | .bytes n, .bytes m => .bytes (n+m)

--------------- Fin n ------------------------------------------------
----------------------------------------------------------------------

def BitSize.ofFin (n : Nat) : BitSize :=
  let bits := Nat.log2 n + (n - 2^(Nat.log2 n) != 0).toUInt64.toNat
  if bits < 8 then
    .bits bits.toUInt8 sorry_proof
  else
    .bytes ((bits + 7) / 8)

@[inline]
opaque Fin.getFromByteArray (n : Nat) [Fact (n≠0)] (d : ByteArray) (i : Nat) (h : (BitSize.ofFin n).InBounds d i ) : Fin n :=
  match (BitSize.ofFin n) with
  | .bits m _ => 
    let ones : UInt8 := 255
    let mask := ones - (ones <<< m) -- 00000111  for m = 3
    let perByte := 8/m
    let inByte  := (i % perByte.toNat).toUInt8
    let ofByte  := i / perByte.toNat
    let byte    := d[ofByte]'sorry_proof
    let val     := mask &&& (byte >>> (m*inByte))
    ⟨val.toNat, sorry_proof⟩
  | .bytes m => Id.run do
    let mut val : Nat := 0
    let ofByte := i * m
    for j in [0:m] do
      val := val + ((d[ofByte+j]'sorry_proof).toNat <<< (j*8))
    ⟨val, sorry_proof⟩

@[inline]
opaque Fin.setInByteArray (n : Nat) (d : ByteArray) (i : Nat) (h : (BitSize.ofFin n).InBounds d i) (val : Fin n) : ByteArray :=
  match (BitSize.ofFin n) with
  | .bits m _ => 
    let perByte := 8/m
    let inByte  := (i % perByte.toNat).toUInt8
    let ofByte  := i / perByte.toNat
    let ones : UInt8 := 255
    let mask    := ones - ((ones - (ones <<< m)) <<< (inByte*m))  --- 11000111 for m = 3 and inByte = 1
    let byte    := d[ofByte]'sorry_proof
    let newByte := (mask &&& byte) + (val.1.toUInt8 <<< (inByte*m))
    d.set ⟨ofByte, sorry_proof⟩ newByte
  | .bytes m => Id.run do
    let mut d := d
    let ofByte := i * m
    for j in [0:m] do
      d := d.set ⟨ofByte+j, sorry_proof⟩ (val.1 >>> (j*8)).toUInt8
    d

instance (n) [Fact (n≠0)] : PlainDataType (Fin n) where
  size := BitSize.ofFin n
  get := Fin.getFromByteArray n
  set := Fin.setInByteArray n


-------------- Enumtype ----------------------------------------------
----------------------------------------------------------------------

instance (priority := low) {ι : Type} [Enumtype ι] [Nonempty ι] : PlainDataType ι where
  size := BitSize.ofFin (numOf ι)
  get d i h := fromFin (Fin.getFromByteArray (numOf ι) d i h)
  set d i h val := (Fin.setInByteArray (numOf ι) d i h (toFin val))

def Float.getByteData (d : ByteArray) (i : Nat) (_ : (BitSize.bytes 8).InBounds d i) : Float := 
  let d : FloatArray := cast sorry_proof d
  d.get ⟨i, sorry_proof⟩


-------------- Float -------------------------------------------------
----------------------------------------------------------------------


def Float.setByteData (d : ByteArray) (i : Nat) (_ : (BitSize.bytes 8).InBounds d i) (val : Float) : ByteArray := Id.run do
  let mut d : FloatArray := cast sorry_proof d
  d := d.set ⟨i, sorry_proof⟩ val
  cast sorry_proof d

instance : PlainDataType Float where
  size := .bytes 8
  get := Float.getByteData
  set := Float.setByteData

