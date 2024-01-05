import SciLean.Data.DataArray.PlainDataType
import SciLean.Data.ArrayType.Basic
import SciLean.Data.ArrayType.Notation

set_option linter.unusedVariables false

namespace SciLean


def _root_.ByteArray.mkArray (n : Nat) (v : UInt8) : ByteArray := Id.run do
  let mut a : ByteArray := .mkEmpty n
  for i in [0:n] do
    a := a.push v
  a

-- TODO: Quotient it out by trailing bits
structure DataArray (α : Type) [pd : PlainDataType α] where
  byteData : ByteArray
  size : USize
  h_size : (pd.bytes size).toNat ≤ byteData.size

variable {α : Type} [pd : PlainDataType α]
variable {ι} [Index.{0,0,0} ι]

@[irreducible]
def DataArray.get (arr : DataArray α) (i : Idx arr.size) : α := -- pd.get a.data i sorry_proof
  match pd.btype with
  | .inl bitType => 
    let perByte := 8/bitType.bits
    let inByte  := (i.1 % perByte.toUSize).toUInt8
    let ofByte  := i.1 / perByte.toUSize
    let ones : UInt8 := 255
    let mask    := (ones - (ones <<< bitType.bits))   -- 00000111 
    -- masking is note necessary if `fromBytes` correctly ignores unused bits
    let byte    := mask &&& (arr.byteData.uget ofByte sorry_proof >>> (inByte*bitType.bits))
    bitType.fromByte byte
  | .inr byteType => 
    byteType.fromByteArray arr.byteData (byteType.bytes * i.1) sorry_proof

@[irreducible]
def DataArray.set (arr : DataArray α) (i : Idx arr.size) (val : α) : DataArray α := -- ⟨pd.set a.byteData i sorry_proof val, a.size, sorry_proof⟩
  match pd.btype with
  | .inl bitType => 
    let perByte := 8/bitType.bits
    let inByte  := (i.1 % perByte.toUSize).toUInt8
    let ofByte  := i.1 / perByte.toUSize
    let ones : UInt8 := 255
    let mask    := ones - ((ones - (ones <<< bitType.bits)) <<< (inByte*bitType.bits))  --- 11000111 for bitType.bits = 3 and inByte = 1
    let byte    := arr.byteData.uget ofByte sorry_proof
    let newByte := (mask &&& byte) + (bitType.toByte val <<< (inByte*bitType.bits))
    ⟨arr.byteData.uset ofByte newByte sorry_proof, arr.size, sorry_proof⟩
  | .inr byteType => 
    ⟨byteType.toByteArray arr.byteData (byteType.bytes * i.1) sorry_proof val, arr.size, sorry_proof⟩


/-- Capacity of an array. The return type is `Squash Nat` as the capacity is is just an implementation detail and should not affect semantics of the program. -/
def DataArray.capacity (arr : DataArray α) : Squash USize := Quot.mk _ (pd.capacity (arr.byteData.size.toUSize))
/-- Makes sure that `arr` fits at least `n` elements of `α` -/
def DataArray.reserve  (arr : DataArray α) (capacity : USize) : DataArray α := 
  if capacity ≤ (pd.capacity (arr.byteData.size.toUSize)) then
    arr
  else Id.run do
    let newBytes := pd.bytes capacity
    let mut arr' : DataArray α := ⟨ByteArray.mkArray newBytes.toNat 0, arr.size, sorry_proof⟩
    -- copy over the old data
    for i in fullRange (Idx arr.size) do
      arr' := arr'.set ⟨i.1,sorry_proof⟩ (arr.get i)
    arr'

def DataArray.mkEmpty (capacity : USize) : DataArray α := Id.run do
  let newBytes := pd.bytes capacity
  { byteData := .mkArray newBytes.toNat 0
    size := 0
    h_size := by sorry_proof }

def DataArray.drop (arr : DataArray α) (k : USize) : DataArray α := ⟨arr.byteData, arr.size - k, sorry_proof⟩

def DataArray.push (arr : DataArray α) (val : α) (k : USize := 1) : DataArray α := Id.run do
  let oldSize := arr.size
  let newSize := arr.size + k
  let mut arr' := arr.reserve newSize
  arr' := ⟨arr'.byteData, newSize, sorry_proof⟩
  for i in [oldSize.toNat:newSize.toNat] do
    arr' := arr'.set ⟨i.toUSize,sorry_proof⟩ val
  arr'

/-- Extensionality of DataArray

Currently this is inconsistent, we need to turn DataArray into quotient!
-/
theorem DataArray.ext (d d' : DataArray α) : (h : d.size = d'.size) → (∀ i, d.get i = d'.get (h ▸ i)) → d = d' := sorry_proof

def DataArray.swap (arr : DataArray α) (i j : Idx arr.size) : DataArray α := 
  let ai := arr.get i
  let aj := arr.get j
  let arr := arr.set i aj
  let arr := arr.set ⟨j.1, sorry_proof⟩ ai
  arr

def DataArray.reverse (arr : DataArray α) : DataArray α := Id.run do
  let mut arr := arr
  let n := arr.size 
  for i in [0:n.toNat/2] do
    let i' : Idx arr.size := ⟨i.toUSize, sorry_proof⟩
    let j' : Idx arr.size := ⟨n - i.toUSize - 1, sorry_proof⟩
    arr := arr.swap i' j'
  arr


@[irreducible]
def DataArray.intro (f : ι → α) : DataArray α := Id.run do
  let bytes := (pd.bytes (Index.size ι))
  let d : ByteArray := ByteArray.mkArray bytes.toNat 0
  let mut d' : DataArray α := ⟨d, (Index.size ι), sorry_proof⟩
  for i in fullRange ι do
    d' := d'.set ⟨(toIdx i).1,sorry_proof⟩ (f i)
  d'

  -- let d' : DataArray α := ⟨d, (Index.size ι), sorry_proof⟩
  -- let rec @[specialize] go : Nat → DataArray α → DataArray α 
  --   | 0, d => d
  --   | n+1, d => 
  --     go n (d.set ⟨n.toUSize, sorry_proof⟩ (f (fromIdx ⟨n.toUSize, sorry_proof⟩)))
  -- go (Index.size ι).toNat d'

structure DataArrayN (α : Type) [pd : PlainDataType α] (ι : Type) [Index ι] where
  data : DataArray α
  h_size : Index.size ι = data.size

@[inline]
instance : GetElem (DataArrayN α ι) ι α (λ _ _ => True) where
  getElem xs i _ := xs.1.get ((toIdx i).cast xs.2)

@[inline]
instance : SetElem (DataArrayN α ι) ι α where
  setElem xs i xi := ⟨xs.1.set ((toIdx i).cast xs.2) xi, sorry_proof⟩

@[inline]
instance : IntroElem (DataArrayN α ι) ι α where
  introElem f := ⟨DataArray.intro f, sorry_proof⟩

instance : StructType (DataArrayN α ι) ι (fun _ => α) where
  structProj x i := x[i]
  structMake f := introElem f
  structModify i f x := modifyElem x i f
  left_inv := sorry_proof
  right_inv := sorry_proof
  structProj_structModify  := sorry_proof
  structProj_structModify' := sorry_proof

instance : ArrayType (DataArrayN α ι) ι α  where
  getElem_structProj   := by intros; rfl
  setElem_structModify := by intros; rfl
  introElem_structMake := by intros; rfl

instance : ArrayTypeNotation (DataArrayN α ι) ι α := ⟨⟩

instance : PushElem (λ n => DataArrayN α (Idx n)) α where
  pushElem k val xs := ⟨xs.1.push val k, sorry_proof⟩

instance : DropElem (λ n => DataArrayN α (Idx n)) α where
  dropElem k xs := ⟨xs.1.drop k, sorry_proof⟩

instance : ReserveElem (λ n => DataArrayN α (Idx n)) α where
  reserveElem k xs := ⟨xs.1.reserve k, sorry_proof⟩

instance : LinearArrayType (λ n => DataArrayN α (Idx n)) α where
  toArrayType := by infer_instance
  pushElem_getElem := sorry_proof
  dropElem_getElem := sorry_proof
  reserveElem_id := sorry_proof

def DataArrayN.reshape (x : DataArrayN α ι) (κ : Type) [Index.{0,0,0} κ] 
  (hs : Index.size κ = Index.size ι)
  : DataArrayN α κ := 
  ⟨x.data, by simp[hs,x.h_size]⟩

instance {Cont ι α : Type} [ArrayType Cont ι α] [Index ι] [Inhabited α] [pd : PlainDataType α] : PlainDataType Cont where
  btype := match pd.btype with
    | .inl αBitType => 
      -- TODO: Fixme !!!!
      .inr {
        bytes := 2
        h_size := sorry_proof

        fromByteArray := λ b i h => 
          introElem (λ j => panic! "not implemented!")
        toByteArray   := λ b i h c => panic! "not implemented!"
        toByteArray_size := sorry_proof
        fromByteArray_toByteArray := sorry_proof
        fromByteArray_toByteArray_other := sorry_proof
      }
    | .inr αByteType => 
      .inr {
        bytes := (Index.size ι) * αByteType.bytes
        h_size := sorry_proof

        fromByteArray := λ b i h => 
          introElem (λ j => 
            let idx := (i + (toIdx j).1*αByteType.bytes)
            αByteType.fromByteArray b idx sorry_proof)
        toByteArray   := λ b i h c => Id.run do
          let mut b := b
          let mut lj : USize := 0
          for j in fullRange ι do
            let idx := (i + lj*αByteType.bytes)
            lj := lj + 1
            b := αByteType.toByteArray b idx sorry_proof c[j]
          b

        toByteArray_size := sorry_proof
        fromByteArray_toByteArray := sorry_proof
        fromByteArray_toByteArray_other := sorry_proof
      }


