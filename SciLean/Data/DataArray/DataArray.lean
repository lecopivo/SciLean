import SciLean.Data.DataArray.PlainDataType
import SciLean.Data.ArrayType

namespace SciLean

-- TODO: Quotient it out by trailing bits
structure DataArray (α : Type) [pd : PlainDataType α] where
  byteData : ByteArray
  size : USize
  h_size : (pd.bytes size).toNat ≤ byteData.size

variable {α : Type} [pd : PlainDataType α]
variable {ι} [Index ι]

def DataArray.get (arr : DataArray α) (i : Idx arr.size) : α := -- pd.get a.data i sorry_proof
  match pd.btype with
  | .inl bitType => 
    let perByte := 8/bitType.bits
    let inByte  := (i.1 % perByte.toUSize).toUInt8
    let ofByte  := i.1 / perByte.toUSize
    let ones : UInt8 := 255
    let mask    := (ones - (ones <<< bitType.bits))   -- 00000111 
    -- masking is note necessary if `fromBytes` correctly ignores unused bits
    let byte    := mask &&& (arr.byteData.uget ofByte sorry >>> (inByte*bitType.bits))
    bitType.fromByte byte
  | .inr byteType => 
    byteType.fromByteArray arr.byteData (byteType.bytes * i.1) sorry_proof

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
def DataArray.reserve  (arr : DataArray α) (n : USize) : DataArray α := 
  if (pd.capacity (arr.byteData.size.toUSize)) ≤ n then
    arr
  else Id.run do
    let newBytes := pd.bytes n
    let mut arr' : DataArray α := ⟨ByteArray.mkEmpty newBytes.toNat, arr.size, sorry_proof⟩
    -- copy over the old data
    for (i,_) in Index.fullRange (Idx arr.size) do
      arr' := ⟨arr'.byteData.push 0, arr.size, sorry_proof⟩
      arr' := arr'.set i (arr.get i)
    arr'


def DataArray.drop (arr : DataArray α) (k : USize) : DataArray α := ⟨arr.byteData, arr.size - k, sorry_proof⟩

def DataArray.push (arr : DataArray α) (k : USize := 1) (val : α) : DataArray α := Id.run do
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

def DataArray.intro (f : ι → α) : DataArray α := Id.run do
  let bytes := (pd.bytes (Index.size ι))
  let mut d : ByteArray := ByteArray.mkEmpty bytes.toNat
  for _ in Index.fullRange (Idx bytes) do
    d := d.push 0
  let mut d' : DataArray α := ⟨d, (Index.size ι), sorry_proof⟩
  for (i,li) in Index.fullRange ι do
    d' := d'.set ⟨li,sorry_proof⟩ (f i)
  d'

structure DataArrayN (α : Type) [pd : PlainDataType α] (ι : Type) [Index ι] where
  data : DataArray α
  h_size : Index.size ι = data.size

instance : GetElem (DataArrayN α ι) ι α (λ _ _ => True) where
  getElem xs i _ := xs.1.get (xs.2 ▸ toIdx i)

instance : SetElem (DataArrayN α ι) ι α where
  setElem xs i xi := ⟨xs.1.set (xs.2 ▸ toIdx i) xi, sorry_proof⟩

instance : IntroElem (DataArrayN α ι) ι α where
  introElem f := ⟨DataArray.intro f, sorry_proof⟩

instance : IntroElem (DataArrayN α ι) ι α where
  introElem f := ⟨DataArray.intro f, sorry_proof⟩

instance : PushElem (λ n => DataArrayN α (Idx n)) α where
  pushElem k val xs := ⟨xs.1.push k val, sorry_proof⟩

instance : DropElem (λ n => DataArrayN α (Idx n)) α where
  dropElem k xs := ⟨xs.1.drop k, sorry_proof⟩

instance : ReserveElem (λ n => DataArrayN α (Idx n)) α where
  reserveElem k xs := ⟨xs.1.reserve k, sorry_proof⟩

instance : ArrayType (DataArrayN α ι) ι α  where
  ext := sorry_proof
  getElem_setElem_eq := sorry_proof
  getElem_setElem_neq := sorry_proof
  getElem_introElem := sorry_proof

instance : LinearArrayType (λ n => DataArrayN α (Idx n)) α where
  toGenericArrayType := by infer_instance
  pushElem_getElem := sorry_proof
  dropElem_getElem := sorry_proof
  reserveElem_id := sorry_proof

@[infer_tc_goals_rl]
instance {Cont ι α : Type} [Index ι] [Inhabited α] [pd : PlainDataType α] [GenericArrayType Cont ι α] : PlainDataType Cont where
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
          for (j,lj) in Index.fullRange ι do
            let idx := (i + lj*αByteType.bytes)
            b := αByteType.toByteArray b idx sorry_proof c[j]
          b

        toByteArray_size := sorry_proof
        fromByteArray_toByteArray := sorry_proof
        fromByteArray_toByteArray_other := sorry_proof
      }


  -- bytes : Nat
  -- h_size : 1 < bytes  -- for one byte types use BitInfo
  -- fromByteArray (b : ByteArray) (i : Nat) (h : i+bytes ≤ b.size) : α
  -- toByteArray   (b : ByteArray) (i : Nat) (h : i+bytes ≤ b.size) (a : α) : ByteArray

  -- -- `toByteArray` does not modify ByteArray size
  -- toByteArray_size : ∀ b i h a, (toByteArray b i h a).size = b.size
  -- -- we can recover `a` from bytes
  -- fromByteArray_toByteArray : ∀ a b i h h', fromByteArray (toByteArray b i h a) i h' = a
  -- -- `toByteArray` does not affect other bytes
  -- fromByteArray_toByteArray_other : ∀ a b i j h, (j < i) ∨ (i+size) ≤ j → (toByteArray b i h a).get! j = b.get! j




-- ShortOptDataArray is prefered for PowType
-- @[defaultInstance]
-- instance : PowType (DataArrayN α (numOf ι)) ι α := PowType.mk 

-- ShortOptDataArray is prefered for PowType
-- @[defaultInstance]
-- instance : LinearPowType (DataArrayN α) α := LinearPowType.mk



-- #check ℝ^(Idx 3)

-- #eval ((λ [i] => i.1.toReal ) : ℝ^(Idx 100)) |>.map Math.sqrt

-- #eval ((λ [i] => i) : (Idx 3 × Idx 5)^(Idx 3 × Idx 5))
-- #eval ((λ [i] => i) : (Idx 3 × Idx 5)^(Idx 3 × Idx 5)).data
-- #eval ((λ [i] => i) : (Idx 3 × Idx 5)^(Idx 3 × Idx 5)).data.byteData

-- #eval (1,2,3,4)

-- #eval ((λ [i] => i) : (Idx 3 × Idx 2 × Idx 2)^(Idx 3 × Idx 2 × Idx 2))
-- #eval ((λ [i] => i) : (Idx 3 × Idx 2 × Idx 2)^(Idx 3 × Idx 2 × Idx 2)).data
-- #eval ((λ [i] => i) : (Idx 3 × Idx 2 × Idx 2)^(Idx 3 × Idx 2 × Idx 2)).data.byteData

-- #eval ((λ [i] => (i.1.toFloat, i.1.toFloat.sqrt)) : (Float × Float)^(Idx 17))

-- variable (x : ℝ^{n,m})

-- #check x
-- #check λ (i,j) => x[i,j]
-- #check ∑ i, x[i]

-- #check Id.run do
--   let mut a : ℝ^{10} := λ [i] => i.1
--   for (i,_) in Enumtype.fullRange a.Index do
--     a[i] *= 1000
--     a[i] += Math.sqrt i.1 + a[i]
--   a

-- #eval Id.run do
--   let mut a : (ℝ×ℝ)^{3,3} := λ [i,j] => (i.1,j.1)
--   for (i,li) in Enumtype.fullRange a.Index do
--     a[li] := (Math.sqrt a[li].1, Math.exp a[li].2)
--   a

-- #eval Id.run do
--   let mut a : ℝ^(Idx 3 × Idx 3) := 0
--   for ((i,j),li) in Enumtype.fullRange a.Index do
--     a[li] := if i = j then 1 else 0
--   a
