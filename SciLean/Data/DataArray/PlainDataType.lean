import SciLean.Prelude
import SciLean.Algebra

namespace SciLean

structure BitType (α : Type) where
  bits : UInt8
  h_size : bits ≤ 8  -- we consider only types fitting into a single byte
  fromByte (b : UInt8) : α
  toByte   (a : α) : UInt8

  -- TODO: Add condition that toByte sets all unused bits to zero
  -- TODO: Add condition that fromByte does not use any of the unused bits
  fromByte_toByte : ∀ a, fromByte (toByte a) = a

structure ByteType (α : Type) where
  bytes : Nat
  h_size : 1 < bytes  -- for one byte types use BitInfo
  fromByteArray (b : ByteArray) (i : Nat) (h : i+bytes ≤ b.size) : α
  toByteArray   (b : ByteArray) (i : Nat) (h : i+bytes ≤ b.size) (a : α) : ByteArray

  -- `toByteArray` does not modify ByteArray size
  toByteArray_size : ∀ b i h a, (toByteArray b i h a).size = b.size
  -- we can recover `a` from bytes
  fromByteArray_toByteArray : ∀ a b i h h', fromByteArray (toByteArray b i h a) i h' = a
  -- `toByteArray` does not affect other bytes
  fromByteArray_toByteArray_other : ∀ a b i j h, (j < i) ∨ (i+size) ≤ j → (toByteArray b i h a).get! j = b.get! j

/-- This rougly corresponds to Plain Old Data(POD)/Passive Data known from OOP

wiki: https://en.wikipedia.org/wiki/Passive_data_structure

We distinguish between two main types of POD. `BitType` a type that is smaller or equal to a byte and `ByteType` that takes up multiple bytes. The main motivation is an efficient storage of `Array Bool` where `Bool` takes up only a single bit, so we can fit 8 bools into a single byte and achieve significant memore reduction.

Potentially surprising edge case is array of fixed length, i.e. the type `{a : Array α // a.size = n}`. It is `PlainDataType` if `α` is `PlainDataType`. However, `Array α` is not `PlainDataType`, even if `α` is `PlainDataType`, as it does not have a fixed byte size. 
-/
class PlainDataType (α : Type) where
  btype : BitType α ⊕ ByteType α

  -- get_set       -- setting and getting returns the original
  -- get_set_other -- set does not affects other elements
  -- size_set      -- does not changes ByteData size
  -- ext           -- extensionality of ByteData i.e. if ∀ i h h', get d i h = get d' i h' → d = d'

/- How many bytes are needed to hold n elements of type α -/
def PlainDataType.bytes {α : Type} (pd : PlainDataType α) (n : Nat) : Nat :=
  match pd.btype with
  | .inl bitType => (n + ((8/bitType.bits) - 1).toNat) / (8/bitType.bits).toNat
  | .inr byteType => byteType.bytes * n


--------------- Prod -------------------------------------------------
----------------------------------------------------------------------

def Prod.bitTypeProd {α β} (ta : BitType α) (tb : BitType β) : BitType (α × β) ⊕ ByteType (α × β) :=
  if h : ta.bits + tb.bits ≤ 8 then
    .inl {
      bits   := ta.bits + tb.bits
      h_size := h

      fromByte := λ byte => 
        -- Maybe the mask is not necessary of `fromByte` correctly ignores unused bits
        let ones  := (255 : UInt8)
        let aMask := ones - (ones <<< ta.bits)               -- e.g. 00000111   
        let bMask := (ones - (ones <<< tb.bits)) <<< ta.bits -- e.g. 00011000
        (ta.fromByte (aMask &&& byte), tb.fromByte ((bMask &&& byte) >>> ta.bits))
      toByte   := λ (a,b) => 
        -- let ones  := (255 : UInt8)
        -- let aMask := ones - (ones <<< ta.bits)               -- e.g. 00000111   
        -- let bMask := (ones - (ones <<< tb.bits)) <<< ta.bits -- e.g. 00011000
        let aByte := ta.toByte a
        let bByte := tb.toByte b
        -- Masking is not necessary if `toByte` correctly sets unused bits to zero
        aByte /- &&& aMask -/ + (bByte <<< ta.bits) /- &&& bMask -/
        
      fromByte_toByte := sorry_proof
    }
  else
    .inr {
      bytes := 2
      h_size := by simp done

      fromByteArray := λ b i _ => 
        let aByte := b[2*i]'sorry_proof
        let bByte := b[2*i+1]'sorry_proof
        (ta.fromByte aByte, tb.fromByte bByte)
      toByteArray := λ arr i _ (a,b) =>
        arr |>.set ⟨  2*i, sorry_proof⟩ (ta.toByte a)
            |>.set ⟨2*i+1, sorry_proof⟩ (tb.toByte b)

      toByteArray_size := sorry_proof
      fromByteArray_toByteArray := sorry_proof
      fromByteArray_toByteArray_other := sorry_proof
    }

def Prod.bitTypeByteTypeProd {α β} (ta : BitType α) (tb : ByteType β) : ByteType (α × β) :=
  {
    bytes := tb.bytes + 1
    h_size := sorry_proof

    fromByteArray := λ arr i _ => 
      let aByte := arr[i]'sorry_proof
      (ta.fromByte aByte, tb.fromByteArray arr (i+1) sorry_proof)
    toByteArray := λ arr i _ (a,b) =>
      arr |>.set ⟨i, sorry_proof⟩ (ta.toByte a)
          |> (tb.toByteArray · (i+1) sorry_proof b)

    toByteArray_size := sorry_proof
    fromByteArray_toByteArray := sorry_proof
    fromByteArray_toByteArray_other := sorry_proof
  }

def Prod.byteTypeBitTypeProd {α β} (ta : ByteType α) (tb : BitType β) : ByteType (α × β) :=
  {
    bytes := ta.bytes + 1
    h_size := sorry_proof

    fromByteArray := λ arr i _ => 
      let bByte := arr[i + ta.bytes]'sorry_proof
      (ta.fromByteArray arr i sorry_proof, tb.fromByte bByte)
    toByteArray := λ arr i _ (a,b) =>
      arr |> (ta.toByteArray · i sorry_proof a)
          |>.set ⟨i + ta.bytes, sorry_proof⟩ (tb.toByte b)

    toByteArray_size := sorry_proof
    fromByteArray_toByteArray := sorry_proof
    fromByteArray_toByteArray_other := sorry_proof
  }


def Prod.byteTypeProd {α β} (ta : ByteType α) (tb : ByteType β) : ByteType (α × β) :=
  {
    bytes := ta.bytes + tb.bytes
    h_size := sorry_proof

    fromByteArray := λ arr i _ => 
      (ta.fromByteArray arr i sorry_proof,
       tb.fromByteArray arr (i+ta.bytes) sorry_proof)
    toByteArray := λ arr i _ (a,b) =>
      arr |> (ta.toByteArray · (i) sorry_proof a)
          |> (tb.toByteArray · (i+ta.bytes) sorry_proof b)

    toByteArray_size := sorry_proof
    fromByteArray_toByteArray := sorry_proof
    fromByteArray_toByteArray_other := sorry_proof
  }

/-- Product of `PlainDataType` is `PlainDataType`

**Instance diamond** This instance is currently prefered over `instPlainDataTypeEnumtype`.

This instance makes a diamond together with `instPlainDataTypeEnumtype`  when `α` and `β` are `Enumtype`. Using this instance is less computationally intensive when writting and reading from `DataArra` but it consumes more memory. The `instPlainDataTypeEnumtype` is doing the exact opposite.

Example: `Fin (2^4+1) × Fin (2^4-1)`
  
As Product:
  The type `Fin (2^4+1)` needs 5 bits.
  The type `Fin (2^4-1)` needs 4 bits.
  Thus `Fin (2^4+1) × Fin (2^4-1)` needs 9 bits, thus 2 bytes, as `instPlainDataTypeProd`

As Enumtype:
  `Fin (2^4+1) × Fin (2^4-1) ≈ Fin (2^8-1)`
  The type `Fin (2^8-1)` needs 8 bits thus only a single byte as `instPlainDataTypeEnumtype`
    
-/
instance instPlainDataTypeProd [ta : PlainDataType α] [tb : PlainDataType β] : PlainDataType (α×β) where
  btype :=
    match ta.btype, tb.btype with
    | .inl aBitType,  .inl bBitType  => Prod.bitTypeProd aBitType bBitType
    | .inl aBitType,  .inr bByteType => .inr <| Prod.bitTypeByteTypeProd aBitType bByteType
    | .inr aByteType, .inl bBitType  => .inr <| Prod.byteTypeBitTypeProd aByteType bBitType 
    | .inr aByteType, .inr bByteType => .inr <| Prod.byteTypeProd aByteType bByteType 

--------------- Fin n ------------------------------------------------
----------------------------------------------------------------------

/-- Number of bits necessary to store `Fin n` -/
def Fin.bitSize  (n : Nat) : Nat := (Nat.log2 n + (n - 2^(Nat.log2 n) != 0).toUInt64.toNat)
def Fin.byteSize (n : Nat) : Nat := (Fin.bitSize n + 7) / 8

-- TODO: IMPORTANT This breaks consistency with (n=0) as we could make `Fin 0` from a byte
-- Adding assumption (n≠0) is really annoying
def Fin.bitType (n : Nat) (_ : n ≤ 2^8) : BitType (Fin n) where
  bits := (bitSize n).toUInt8
  h_size := sorry_proof
  fromByte b := ⟨b.toNat % n, sorry_proof⟩ --- The modulo here is just in case to remove junk bit values, also we need `n≠0` for consistency
  toByte   b := b.1.toUInt8
  fromByte_toByte := sorry_proof

def Fin.byteType (n : Nat) (_ : 2^8 < n) : ByteType (Fin n) where
  bytes := byteSize n
  h_size := sorry_proof

  fromByteArray b i h := Id.run do
    let bytes  := byteSize n
    let ofByte := i * bytes

    let mut val : Nat := 0
    for j in [0:bytes] do
      val := val + ((b[ofByte+j]'sorry_proof).toNat <<< (j*8))
    ⟨val, sorry_proof⟩

  toByteArray b i h val := Id.run do
    let bytes  := byteSize n
    let ofByte := i * bytes

    let mut b := b
    for j in [0:bytes] do
      b := b.set ⟨ofByte+j, sorry_proof⟩ (val.1 >>> (j*8)).toUInt8
    b
    
  toByteArray_size := sorry_proof
  fromByteArray_toByteArray := sorry_proof
  fromByteArray_toByteArray_other := sorry_proof

-- TODO: IMPORTANT This breaks consistency see Fin.bitType
instance (n) : PlainDataType (Fin n) where
  btype := 
    if h : n ≤ 2^8 
    then .inl (Fin.bitType n h) 
    else .inr (Fin.byteType n (by simp at h; apply h))

-------------- Enumtype ----------------------------------------------
----------------------------------------------------------------------

def Enumtype.bitType (α : Type) [Enumtype α] (h : numOf α ≤ 2^8) : BitType α where
  bits := Fin.bitSize (numOf α) |>.toUInt8
  h_size := sorry_proof
  fromByte b := fromFin <| (Fin.bitType (numOf α) h).fromByte b
  toByte a   := (Fin.bitType (numOf α) h).toByte (toFin a)
  fromByte_toByte := sorry_proof

def Enumtype.byteType (α : Type) [Enumtype α] (hn : 2^8 < numOf α ) : ByteType α where
  bytes := Fin.byteSize (numOf α)
  h_size := sorry_proof

  fromByteArray b i h := fromFin <| (Fin.byteType (numOf α) hn).fromByteArray b i h
  toByteArray b i h a := (Fin.byteType (numOf α) hn).toByteArray b i h (toFin a)
    
  toByteArray_size := sorry_proof
  fromByteArray_toByteArray := sorry_proof
  fromByteArray_toByteArray_other := sorry_proof


/-- Enumtype is `PlainDataType` via conversion from/to `Fin n`

**Instance diamond** This instance `instPlainDataTypeProd` is prefered over this one.

This instance makes a diamond together with `instPlainDataTypeProd`. Using this instance is more computationally intensive when writting and reading from `DataArra` but it consumes less memory. The `instPlainDataTypeProd` is doing the exact opposite.

Example: `Fin (2^4+1) × Fin (2^4-1)`
  
As Product:
  The type `Fin (2^4+1)` needs 5 bits.
  The type `Fin (2^4-1)` needs 4 bits.
  Thus `Fin (2^4+1) × Fin (2^4-1)` needs 9 bits, thus 2 bytes, as `instPlainDataTypeProd`

As Enumtype:
  `Fin (2^4+1) × Fin (2^4-1) ≈ Fin (2^8-1)`
  The type `Fin (2^8-1)` needs 8 bits thus only a single byte as `instPlainDataTypeEnumtype`
    
-/
instance (priority := low) instPlainDataTypeEnumtype  {α : Type} [Enumtype α] : PlainDataType α where
  btype := 
    if h : (numOf α) ≤ 2^8 
    then .inl (Enumtype.bitType α h)
    else .inr (Enumtype.byteType α (by simp at h; apply h))

-------------- Float -------------------------------------------------
----------------------------------------------------------------------

def Float.byteType : ByteType Float where
  bytes := 8
  h_size := sorry_proof

  fromByteArray arr i _ := 
    if i % 8 = 0 then
      let arr : FloatArray := cast sorry_proof arr
      arr[i/8]'sorry_proof
    else
      panic! "Can't read float from ByteArray from nonaligned position i={i}! i % 8 = {i%8} ≠ 0. Please implement this case in C!"
  toByteArray arr i _ a :=
    if i % 8 = 0 then
      let arr : FloatArray := cast sorry_proof arr
      cast sorry_proof (arr.set ⟨i/8, sorry_proof⟩ a)
    else
      panic! "Can't write float to ByteArray to nonaligned position i={i}! i % 8 = {i%8} ≠ 0. Please implement this case in C!"

  toByteArray_size := sorry_proof
  fromByteArray_toByteArray := sorry_proof
  fromByteArray_toByteArray_other := sorry_proof


instance : PlainDataType Float where
  btype := .inr Float.byteType

-------------- Real --------------------------------------------------
----------------------------------------------------------------------

def ℝ.byteType : ByteType ℝ where    
  bytes := 8
  h_size := sorry_proof

  fromByteArray b i h := Float.byteType.fromByteArray b i h |>.toReal
  toByteArray b i h a := Float.byteType.toByteArray b i h a.toFloat

  toByteArray_size := sorry_proof
  fromByteArray_toByteArray := sorry_proof
  fromByteArray_toByteArray_other := sorry_proof


instance : PlainDataType ℝ where
  btype := .inr ℝ.byteType
