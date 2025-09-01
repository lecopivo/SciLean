import SciLean.Util.SorryProof
import SciLean.Data.IndexType
import SciLean.Data.ByteArray
import SciLean.Data.Idx
import SciLean.Data.IndexType.Fold
-- import LeanColls.Classes.Ops.Fold

namespace SciLean

structure BitType (α : Type*) where
  bits : UInt8
  h_size : bits ≤ 8  -- we consider only types fitting into a single byte
  fromByte (b : UInt8) : α
  toByte   (a : α) : UInt8
  -- TODO: Add condition that toByte sets all unused bits to zero
  -- TODO: Add condition that fromByte does not use any of the unused bits
  fromByte_toByte : ∀ a, fromByte (toByte a) = a

structure ByteType (α : Type*) where
  bytes : USize
  h_size : 1 < bytes  -- for one byte types use BitInfo
  /-- Read `a : α` from byte array `b` starting at the byte `i` -/
  fromByteArray (b : ByteArray) (i : USize) (h : (i+bytes).toNat ≤ b.size) : α
  /-- Write `a : α` from byte array `b` starting at the byte `i` -/
  toByteArray   (b : ByteArray) (i : USize) (h : (i+bytes).toNat ≤ b.size) (a : α) : ByteArray

  /-- `toByteArray` does not modify ByteArray size -/
  toByteArray_size : ∀ b i h a, (toByteArray b i h a).size = b.size
  /-- we can recover `a` from bytes -/
  fromByteArray_toByteArray : ∀ a b i h h', fromByteArray (toByteArray b i h a) i h' = a
  /-- `toByteArray` does not affect other bytes -/
  fromByteArray_toByteArray_other : ∀ a b i j h, (j < i) ∨ (i + bytes) ≤ j → (toByteArray b i h a).uget j sorry_proof = b.uget j sorry_proof


/-- This rougly corresponds to Plain Old Data(POD)/Passive Data known from OOP

wiki: https://en.wikipedia.org/wiki/Passive_data_structure

We distinguish between two main types of POD. `BitType` a type that is smaller or equal to a byte and `ByteType` that takes up multiple bytes. The main motivation is an efficient storage of `Array Bool` where `Bool` takes up only a single bit, so we can fit 8 bools into a single byte and achieve significant memore reduction.

Potentially surprising edge case is array of fixed length, i.e. the type `{a : Array α // a.size = n}`. It is `PlainDataType` if `α` is `PlainDataType`. However, `Array α` is not `PlainDataType`, even if `α` is `PlainDataType`, as it does not have a fixed byte size.
-/
class PlainDataType (α : Type*) where
  btype : ByteType α

  -- get_set       -- setting and getting returns the original
  -- get_set_other -- set does not affects other elements
  -- size_set      -- does not changes ByteData size
  -- ext           -- extensionality of ByteData i.e. if ∀ i h h', get d i h = get d' i h' → d = d'

/- How many bytes are needed to hold n elements of type α -/
def PlainDataType.bytes {α : Type*} (pd : PlainDataType α) (n : Nat) : Nat :=
  pd.btype.bytes.toNat * n

/-- How many `α` can fit into a buffer with `byteNum` bytes -/
def PlainDataType.capacity {α : Type*} (pd : PlainDataType α) (byteNum : Nat) : Nat :=
  byteNum / pd.btype.bytes.toNat



set_option linter.unusedVariables false in
/-- Get `i`-th element from `ByteArray`.

The index `i` is `i`-th element *not* `i`-th byte!. -/
@[inline]
def PlainDataType.fromByteArray {α : Type*} (pd : PlainDataType α) (data : ByteArray) (i : USize) (hi : i.toNat*pd.bytes < data.size): α :=
  pd.btype.fromByteArray data (i*pd.btype.bytes) sorry_proof
  -- match pd.btype with
  -- | .inl bitType =>
  --   let i := i
  --   let perByte := 8/bitType.bits
  --   let inByte  := (i % perByte.toUSize).toUInt8
  --   let ofByte  := i / perByte.toUSize
  --   let ones : UInt8 := 255
  --   let mask    := (ones - (ones <<< bitType.bits))   -- 00000111
  --   -- masking is note necessary if `fromBytes` correctly ignores unused bits
  --   let byte    := mask &&& (data.uget ofByte sorry_proof >>> (inByte*bitType.bits))
  --   bitType.fromByte byte
  -- | .inr byteType =>
  --   -- todo: add bound check
  --   byteType.

set_option linter.unusedVariables false in
/-- Write `v` to `ByteArray` at `i`-th position. -/
def PlainDataType.toByteArray {α : Type*} (pd : PlainDataType α) (data : ByteArray) (i : Nat) (v : α) (hi : i*pd.bytes < data.size): ByteArray :=
  pd.btype.toByteArray data (i.toUSize*pd.btype.bytes) sorry_proof v

  -- match pd.btype with
  -- | .inl bitType =>
  --   let i := i.toUSize
  --   let perByte := 8/bitType.bits
  --   let inByte  := (i % perByte.toUSize).toUInt8
  --   let ofByte  := i / perByte.toUSize
  --   let ones : UInt8 := 255
  --   let mask    := ones - ((ones - (ones <<< bitType.bits)) <<< (inByte*bitType.bits))  --- 11000111 for bitType.bits = 3 and inByte = 1
  --   let byte    := data.uget ofByte sorry_proof
  --   let newByte := (mask &&& byte) + (bitType.toByte v <<< (inByte*bitType.bits))
  --   data.uset ofByte newByte sorry_proof
  -- | .inr byteType =>
  --   -- todo: add bound check
  --   byteType.toByteArray data (i.toUSize*byteType.bytes) sorry_proof v

/-- Translate `PlainDataType X` along equivalence `f : X ≃ Y` to `PlainDataType Y` -/
def PlainDataType.ofEquiv {X Y : Type*} [pd : PlainDataType X] (f : X ≃ Y) : PlainDataType Y where
  btype := {
      bytes := pd.btype.bytes
      h_size := pd.btype.h_size
      fromByteArray b i h :=
        let x := pd.btype.fromByteArray b i h
        let y := f x
        y
      toByteArray b i h vy :=
        let vx := f.symm vy
        let b := pd.btype.toByteArray b i h vx
        b
      toByteArray_size := sorry_proof
      fromByteArray_toByteArray := sorry_proof
      fromByteArray_toByteArray_other := sorry_proof
      : ByteType Y }

    -- match pd.btype with
    -- | .inl bt => .inl {
    --   bits := bt.bits
    --   h_size := bt.h_size
    --   fromByte b :=
    --     let x := bt.fromByte b
    --     let y := f x
    --     y
    --   toByte vx  :=
    --     let vx := f.symm vx
    --     let b := bt.toByte vx
    --     b
    --   fromByte_toByte := sorry_proof
    --   : BitType Y}
    -- | .inr bt => .inr {
    --   bytes := bt.bytes
    --   h_size := bt.h_size
    --   fromByteArray b i h :=
    --     let x := bt.fromByteArray b i h
    --     let y := f x
    --     y
    --   toByteArray b i h vy :=
    --     let vx := f.symm vy
    --     let b := bt.toByteArray b i h vx
    --     b
    --   toByteArray_size := sorry_proof
    --   fromByteArray_toByteArray := sorry_proof
    --   fromByteArray_toByteArray_other := sorry_proof
    --   : ByteType Y }


--------------- Prod -------------------------------------------------
----------------------------------------------------------------------

@[inline]
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
      h_size := by sorry_proof

      fromByteArray := λ b i _ =>
        let aByte := b[2*i]'sorry_proof
        let bByte := b[2*i+1]'sorry_proof
        (ta.fromByte aByte, tb.fromByte bByte)
      toByteArray := λ arr i _ (a,b) =>
        arr |>.uset (2*i) (ta.toByte a) sorry_proof
            |>.uset (2*i+1) (tb.toByte b) sorry_proof

      toByteArray_size := sorry_proof
      fromByteArray_toByteArray := sorry_proof
      fromByteArray_toByteArray_other := sorry_proof
    }

@[inline]
def Prod.bitTypeByteTypeProd {α β} (ta : BitType α) (tb : ByteType β) : ByteType (α × β) :=
  {
    bytes := tb.bytes + 1
    h_size := sorry_proof

    fromByteArray := λ arr i _ =>
      let aByte := arr[i]'sorry_proof
      (ta.fromByte aByte, tb.fromByteArray arr (i+1) sorry_proof)
    toByteArray := λ arr i _ (a,b) =>
      arr |>.uset i (ta.toByte a) sorry_proof
          |> (tb.toByteArray · (i+1) sorry_proof b)

    toByteArray_size := sorry_proof
    fromByteArray_toByteArray := sorry_proof
    fromByteArray_toByteArray_other := sorry_proof
  }

@[inline]
def Prod.byteTypeBitTypeProd {α β} (ta : ByteType α) (tb : BitType β) : ByteType (α × β) :=
  {
    bytes := ta.bytes + 1
    h_size := sorry_proof

    fromByteArray := λ arr i _ =>
      let bByte := arr[i + ta.bytes]'sorry_proof
      (ta.fromByteArray arr i sorry_proof, tb.fromByte bByte)
    toByteArray := λ arr i _ (a,b) =>
      arr |> (ta.toByteArray · i sorry_proof a)
          |>.uset (i + ta.bytes) (tb.toByte b) sorry_proof

    toByteArray_size := sorry_proof
    fromByteArray_toByteArray := sorry_proof
    fromByteArray_toByteArray_other := sorry_proof
  }

@[inline]
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

**Instance diamond:** This instance is currently prefered over `instPlainDataTypeEnumtype`.

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
  btype := Prod.byteTypeProd ta.btype tb.btype
    -- match ta.btype, tb.btype with
    -- | .inl aBitType,  .inl bBitType  => Prod.bitTypeProd aBitType bBitType
    -- | .inl aBitType,  .inr bByteType => .inr <| Prod.bitTypeByteTypeProd aBitType bByteType
    -- | .inr aByteType, .inl bBitType  => .inr <| Prod.byteTypeBitTypeProd aByteType bBitType
    -- | .inr aByteType, .inr bByteType => .inr <| Prod.byteTypeProd aByteType bByteType



--------------- Sigma -------------------------------------------------
----------------------------------------------------------------------

@[inline]
def Sigma.bitTypeSigma {α β} (ta : BitType α) (tb : BitType β) : BitType ((_ : α) × β) ⊕ ByteType ((_ : α) × β) :=
  if h : ta.bits + tb.bits ≤ 8 then
    .inl {
      bits   := ta.bits + tb.bits
      h_size := h

      fromByte := λ byte =>
        -- Maybe the mask is not necessary of `fromByte` correctly ignores unused bits
        let ones  := (255 : UInt8)
        let aMask := ones - (ones <<< ta.bits)               -- e.g. 00000111
        let bMask := (ones - (ones <<< tb.bits)) <<< ta.bits -- e.g. 00011000
        ⟨ta.fromByte (aMask &&& byte), tb.fromByte ((bMask &&& byte) >>> ta.bits)⟩
      toByte   := λ ⟨a,b⟩ =>
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
      h_size := by sorry_proof

      fromByteArray := λ b i _ =>
        let aByte := b[2*i]'sorry_proof
        let bByte := b[2*i+1]'sorry_proof
        ⟨ta.fromByte aByte, tb.fromByte bByte⟩
      toByteArray := λ arr i _ ⟨a,b⟩ =>
        arr |>.uset (2*i) (ta.toByte a) sorry_proof
            |>.uset (2*i+1) (tb.toByte b) sorry_proof

      toByteArray_size := sorry_proof
      fromByteArray_toByteArray := sorry_proof
      fromByteArray_toByteArray_other := sorry_proof
    }

@[inline]
def Sigma.bitTypeByteTypeSigma {α β} (ta : BitType α) (tb : ByteType β) : ByteType ((_ : α) × β) :=
  {
    bytes := tb.bytes + 1
    h_size := sorry_proof

    fromByteArray := λ arr i _ =>
      let aByte := arr[i]'sorry_proof
      ⟨ta.fromByte aByte, tb.fromByteArray arr (i+1) sorry_proof⟩
    toByteArray := λ arr i _ ⟨a,b⟩ =>
      arr |>.uset i (ta.toByte a) sorry_proof
          |> (tb.toByteArray · (i+1) sorry_proof b)

    toByteArray_size := sorry_proof
    fromByteArray_toByteArray := sorry_proof
    fromByteArray_toByteArray_other := sorry_proof
  }

@[inline]
def Sigma.byteTypeBitTypeSigma {α β} (ta : ByteType α) (tb : BitType β) : ByteType ((_ : α) × β) :=
  {
    bytes := ta.bytes + 1
    h_size := sorry_proof

    fromByteArray := λ arr i _ =>
      let bByte := arr[i + ta.bytes]'sorry_proof
      ⟨ta.fromByteArray arr i sorry_proof, tb.fromByte bByte⟩
    toByteArray := λ arr i _ ⟨a,b⟩ =>
      arr |> (ta.toByteArray · i sorry_proof a)
          |>.uset (i + ta.bytes) (tb.toByte b) sorry_proof

    toByteArray_size := sorry_proof
    fromByteArray_toByteArray := sorry_proof
    fromByteArray_toByteArray_other := sorry_proof
  }

@[inline]
def Sigma.byteTypeSigma {α β} (ta : ByteType α) (tb : ByteType β) : ByteType ((_ : α) × β) :=
  {
    bytes := ta.bytes + tb.bytes
    h_size := sorry_proof

    fromByteArray := λ arr i _ =>
      let a := ta.fromByteArray arr i sorry_proof
      let b := tb.fromByteArray arr (i+ta.bytes) sorry_proof
      ⟨a, b⟩
    toByteArray := λ arr i _ ⟨a,b⟩ =>
      let arr := (ta.toByteArray arr (i) sorry_proof a)
      let arr := (tb.toByteArray arr (i+ta.bytes) sorry_proof b)
      arr

    toByteArray_size := sorry_proof
    fromByteArray_toByteArray := sorry_proof
    fromByteArray_toByteArray_other := sorry_proof
  }

/-- Sigma of `PlainDataType` is `PlainDataType`

**Instance diamond:** This instance is currently prefered over `instPlainDataTypeEnumtype`.

This instance makes a diamond together with `instPlainDataTypeEnumtype`  when `α` and `β` are `Enumtype`. Using this instance is less computationally intensive when writting and reading from `DataArra` but it consumes more memory. The `instPlainDataTypeEnumtype` is doing the exact opposite.

Example: `Fin (2^4+1) × Fin (2^4-1)`

As Sigmauct:
  The type `Fin (2^4+1)` needs 5 bits.
  The type `Fin (2^4-1)` needs 4 bits.
  Thus `Fin (2^4+1) × Fin (2^4-1)` needs 9 bits, thus 2 bytes, as `instPlainDataTypeSigma`

As Enumtype:
  `Fin (2^4+1) × Fin (2^4-1) ≈ Fin (2^8-1)`
  The type `Fin (2^8-1)` needs 8 bits thus only a single byte as `instPlainDataTypeEnumtype`

-/
instance instPlainDataTypeSigma [ta : PlainDataType α] [tb : PlainDataType β] : PlainDataType ((_ : α)×β) where
  btype := Sigma.byteTypeSigma ta.btype tb.btype

    -- match ta.btype, tb.btype with
    -- | .inl aBitType,  .inl bBitType  => Sigma.bitTypeSigma aBitType bBitType
    -- | .inl aBitType,  .inr bByteType => .inr <| Sigma.bitTypeByteTypeSigma aBitType bByteType
    -- | .inr aByteType, .inl bBitType  => .inr <| Sigma.byteTypeBitTypeSigma aByteType bBitType
    -- | .inr aByteType, .inr bByteType => .inr <| Sigma.byteTypeSigma aByteType bByteType


--------------- MProd -------------------------------------------------
----------------------------------------------------------------------
-- TODO: somehow reuse implementation for Prod rather then copy paste

@[inline]
def MProd.bitTypeMProd {α β} (ta : BitType α) (tb : BitType β) : BitType (MProd α β) ⊕ ByteType (MProd α β) :=
  if h : ta.bits + tb.bits ≤ 8 then
    .inl {
      bits   := ta.bits + tb.bits
      h_size := h

      fromByte := λ byte =>
        -- Maybe the mask is not necessary of `fromByte` correctly ignores unused bits
        let ones  := (255 : UInt8)
        let aMask := ones - (ones <<< ta.bits)               -- e.g. 00000111
        let bMask := (ones - (ones <<< tb.bits)) <<< ta.bits -- e.g. 00011000
        ⟨ta.fromByte (aMask &&& byte), tb.fromByte ((bMask &&& byte) >>> ta.bits)⟩
      toByte   := λ ⟨a,b⟩ =>
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
      h_size := by sorry_proof

      fromByteArray := λ b i _ =>
        let aByte := b[2*i]'sorry_proof
        let bByte := b[2*i+1]'sorry_proof
        ⟨ta.fromByte aByte, tb.fromByte bByte⟩
      toByteArray := λ arr i _ ⟨a,b⟩ =>
        arr |>.uset (2*i) (ta.toByte a) sorry_proof
            |>.uset (2*i+1) (tb.toByte b) sorry_proof

      toByteArray_size := sorry_proof
      fromByteArray_toByteArray := sorry_proof
      fromByteArray_toByteArray_other := sorry_proof
    }

@[inline]
def MProd.bitTypeByteTypeMProd {α β} (ta : BitType α) (tb : ByteType β) : ByteType (MProd α β) :=
  {
    bytes := tb.bytes + 1
    h_size := sorry_proof

    fromByteArray := λ arr i _ =>
      let aByte := arr[i]'sorry_proof
      ⟨ta.fromByte aByte, tb.fromByteArray arr (i+1) sorry_proof⟩
    toByteArray := λ arr i _ ⟨a,b⟩ =>
      arr |>.uset i (ta.toByte a) sorry_proof
          |> (tb.toByteArray · (i+1) sorry_proof b)

    toByteArray_size := sorry_proof
    fromByteArray_toByteArray := sorry_proof
    fromByteArray_toByteArray_other := sorry_proof
  }

@[inline]
def MProd.byteTypeBitTypeMProd {α β} (ta : ByteType α) (tb : BitType β) : ByteType (MProd α β) :=
  {
    bytes := ta.bytes + 1
    h_size := sorry_proof

    fromByteArray := λ arr i _ =>
      let bByte := arr[i + ta.bytes]'sorry_proof
      ⟨ta.fromByteArray arr i sorry_proof, tb.fromByte bByte⟩
    toByteArray := λ arr i _ ⟨a,b⟩ =>
      arr |> (ta.toByteArray · i sorry_proof a)
          |>.uset (i + ta.bytes) (tb.toByte b) sorry_proof

    toByteArray_size := sorry_proof
    fromByteArray_toByteArray := sorry_proof
    fromByteArray_toByteArray_other := sorry_proof
  }

@[inline]
def MProd.byteTypeMProd {α β} (ta : ByteType α) (tb : ByteType β) : ByteType (MProd α β) :=
  {
    bytes := ta.bytes + tb.bytes
    h_size := sorry_proof

    fromByteArray := λ arr i _ =>
      ⟨ta.fromByteArray arr i sorry_proof,
       tb.fromByteArray arr (i+ta.bytes) sorry_proof⟩
    toByteArray := λ arr i _ ⟨a,b⟩ =>
      arr |> (ta.toByteArray · (i) sorry_proof a)
          |> (tb.toByteArray · (i+ta.bytes) sorry_proof b)

    toByteArray_size := sorry_proof
    fromByteArray_toByteArray := sorry_proof
    fromByteArray_toByteArray_other := sorry_proof
  }

instance instPlainDataTypeMProd [ta : PlainDataType α] [tb : PlainDataType β] : PlainDataType (MProd α β) where
  btype := MProd.byteTypeMProd ta.btype tb.btype
    -- match ta.btype, tb.btype with
    -- | .inl aBitType,  .inl bBitType  => MProd.bitTypeMProd aBitType bBitType
    -- | .inl aBitType,  .inr bByteType => .inr <| MProd.bitTypeByteTypeMProd aBitType bByteType
    -- | .inr aByteType, .inl bBitType  => .inr <| MProd.byteTypeBitTypeMProd aByteType bBitType
    -- | .inr aByteType, .inr bByteType => .inr <| MProd.byteTypeMProd aByteType bByteType


--------------- Bool n ------------------------------------------------
-----------------------------------------------------------------------

-- @[inline]
-- def Bool.bitType : BitType Bool where
--   bits := 1
--   h_size := by aesop
--   fromByte b := if (b &&& 1) == 1 then true else false
--   toByte b := if b == true then 1 else 0
--   fromByte_toByte := sorry_proof

-- instance : PlainDataType Bool where
--   btype := .inl Bool.bitType


--------------- Fin n ------------------------------------------------
----------------------------------------------------------------------

/-- Number of bits necessary to store `Fin n` -/
@[inline]
def Fin.bitSize  (n : Nat) : Nat := (Nat.log2 n + (n - (1 <<< (Nat.log2 n)) != 0).toUInt64.toNat)
@[inline]
def Fin.byteSize (n : Nat) : Nat := (Fin.bitSize n + 7) / 8


-- INCONSISTENT: This breaks consistency with (n=0) as we could make `Fin 0` from a byte
-- Adding assumption (n≠0) is really annoying, what to do about this?
@[inline]
def Fin.bitType (n : Nat) (_ : n ≤ 256) : BitType (Fin n) where
  bits := (bitSize n).toUInt8
  h_size := sorry_proof
  fromByte b := ⟨b.toNat % n, sorry_proof⟩ --- The modulo here is just in case to remove junk bit values, also we need `n≠0` for consistency
  toByte   b := b.1.toUInt8
  fromByte_toByte := sorry_proof

@[inline]
def Fin.byteType (n : Nat) : ByteType (Fin n) where
  bytes := (byteSize n).toUSize
  h_size := sorry_proof

  fromByteArray b i _ := Id.run do
    let bytes  := byteSize n
    let ofByte := i
    let mut val : Nat := 0
    for j in fullRange (Idx bytes) do
      let val' := ((b.uget (ofByte+j.1) sorry_proof).toNat <<< (j.1*8).toNat)
      val := val + val'
    ⟨val, sorry_proof⟩

  toByteArray b i _ val := Id.run do
    let bytes  := byteSize n
    let ofByte := i

    let mut b := b
    for j in fullRange (Idx bytes) do
      b := b.uset (ofByte+j.1) (val.1.toUSize >>> (j.1*(8:USize))).toUInt8 sorry_proof
    b

  toByteArray_size := sorry_proof
  fromByteArray_toByteArray := sorry_proof
  fromByteArray_toByteArray_other := sorry_proof

-- INCONSISTENT: This breaks consistency see Fin.bitType
instance (n) : PlainDataType (Fin n) where
  btype := Fin.byteType n
    -- if h : n ≤ 256
    -- then .inl (Fin.bitType n h)
    -- else .inr (Fin.byteType n (by simp at h; apply h))


--------------- UInt* ------------------------------------------------
-----------------------------------------------------------------------

-- This implementation is not ideal, we do a round trip through `Nat`
-- instance : PlainDataType UInt8 where
--   btype :=
--     let bt := Fin.bitType UInt8.size (by decide)
--     .inl {
--       bits := bt.bits
--       h_size := bt.h_size
--       fromByte := fun b => ⟨bt.fromByte b⟩
--       toByte   := fun a => bt.toByte a.toNat
--       fromByte_toByte := sorry_proof
--   }


-- This implementation is not ideal, we do a round trip through `Nat`
-- instance : PlainDataType UInt16 where
--   btype :=
--     let bt := Fin.byteType UInt16.size (by decide)
--     {
--     bytes := bt.bytes
--     h_size := bt.h_size
--     fromByteArray := fun b i h => ⟨bt.fromByteArray b i h⟩
--     toByteArray := fun b i h a => bt.toByteArray b i h a.toNat
--     toByteArray_size := sorry_proof
--     fromByteArray_toByteArray := sorry_proof
--     fromByteArray_toByteArray_other := sorry_proof
--   }

-- This implementation is not ideal, we do a round trip through `Nat`
-- instance : PlainDataType UInt32 where
--   btype :=
--     let bt := Fin.byteType UInt32.size (by decide)
--     .inr {
--     bytes := bt.bytes
--     h_size := bt.h_size
--     fromByteArray := fun b i h => ⟨bt.fromByteArray b i h⟩
--     toByteArray := fun b i h a => bt.toByteArray b i h a.toNat
--     toByteArray_size := sorry_proof
--     fromByteArray_toByteArray := sorry_proof
--     fromByteArray_toByteArray_other := sorry_proof
--   }

-- This implementation is not ideal, we do a round trip through `Nat`
-- instance : PlainDataType UInt64 where
--   btype :=
--     let bt := Fin.byteType UInt64.size (by decide)
--     .inr {
--     bytes := bt.bytes
--     h_size := bt.h_size
--     fromByteArray := fun b i h => ⟨bt.fromByteArray b i h⟩
--     toByteArray := fun b i h a => bt.toByteArray b i h a.toNat
--     toByteArray_size := sorry_proof
--     fromByteArray_toByteArray := sorry_proof
--     fromByteArray_toByteArray_other := sorry_proof
--   }


-- This implementation is not ideal, we do a round trip through `Nat`
-- instance : PlainDataType UInt64 where
--   btype :=
--     let bt := Fin.byteType UInt64.size (by decide)
--     .inr {
--     bytes := bt.bytes
--     h_size := bt.h_size
--     fromByteArray := fun b i h => ⟨bt.fromByteArray b i h⟩
--     toByteArray := fun b i h a => bt.toByteArray b i h a.toNat
--     toByteArray_size := sorry_proof
--     fromByteArray_toByteArray := sorry_proof
--     fromByteArray_toByteArray_other := sorry_proof
--   }



-- TODO: change to IndexType
-- -------------- Index ----------------------------------------------
-- ----------------------------------------------------------------------

-- def Index.bitType (α : Type) [Index α] (h : Index.size α ≤ 256) : BitType α where
--   bits := Idx.bitSize (Index.size α) |>.toUInt8
--   h_size := sorry_proof
--   fromByte b := fromIdx <| (Idx.bitType (Index.size α) h).fromByte b
--   toByte a   := (Idx.bitType (Index.size α) h).toByte (toIdx a)
--   fromByte_toByte := sorry_proof

-- def Index.byteType (α : Type) [Index α] (hn : 256 < Index.size α ) : ByteType α where
--   bytes := Idx.byteSize (Index.size α)
--   h_size := sorry_proof

--   fromByteArray b i h := fromIdx <| (Idx.byteType (Index.size α) hn).fromByteArray b i h
--   toByteArray b i h a := (Idx.byteType (Index.size α) hn).toByteArray b i h (toIdx a)

--   toByteArray_size := sorry_proof
--   fromByteArray_toByteArray := sorry_proof
--   fromByteArray_toByteArray_other := sorry_proof


-- /-- Index is `PlainDataType` via conversion from/to `Idx n`

-- **Instance diamond** This instance `instPlainDataTypeProd` is prefered over this one.

-- This instance makes a diamond together with `instPlainDataTypeProd`. Using this instance is more computationally intensive when writting and reading from `DataArra` but it consumes less memory. The `instPlainDataTypeProd` is doing the exact opposite.

-- Example: `Idx (2^4+1) × Idx (2^4-1)`

-- As Product:
--   The type `Idx (2^4+1)` needs 5 bits.
--   The type `Idx (2^4-1)` needs 4 bits.
--   Thus `Idx (2^4+1) × Idx (2^4-1)` needs 9 bits, thus 2 bytes, as `instPlainDataTypeProd`

-- As Index:
--   `Idx (2^4+1) × Idx (2^4-1) ≈ Idx (2^8-1)`
--   The type `Idx (2^8-1)` needs 8 bits thus only a single byte as `instPlainDataTypeIndex`

-- -/
-- instance (priority := low) instPlainDataTypeIndex  {α : Type} [Index α] : PlainDataType α where
--   btype :=
--     if h : (Index.size α) ≤ 256
--     then .inl (Index.bitType α h)
--     else .inr (Index.byteType α (by simp at h; apply h))

-------------- Float -------------------------------------------------
----------------------------------------------------------------------

@[inline]
def Float.byteType : ByteType Float where
  bytes := 8
  h_size := sorry_proof

  fromByteArray arr i _ := arr.ugetFloatAtByte i sorry_proof
  toByteArray arr i _ a :=
    if i % 8 = 0 then
      let arr : FloatArray := cast sorry_proof arr
      cast sorry_proof (arr.uset (i>>>3) a sorry_proof)
    else
      panic! "Can't write float to ByteArray to nonaligned position i={i}! i % 8 = {i%8} ≠ 0. Please implement this case in C!"

  toByteArray_size := sorry_proof
  fromByteArray_toByteArray := sorry_proof
  fromByteArray_toByteArray_other := sorry_proof


instance : PlainDataType Float where
  btype := Float.byteType
