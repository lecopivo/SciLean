import SciLean.Data.DataArray.PlainDataType
import SciLean.Data.ArrayType

namespace SciLean

-- TODO: Quotient it out by trailing bits
structure DataArray (α : Type) [pd : PlainDataType α] where
  byteData : ByteArray
  size : Nat 
  h_size : pd.bytes size ≤ byteData.size

variable {α : Type} [pd : PlainDataType α]
variable {ι} [Enumtype ι]

def DataArray.get (arr : DataArray α) (i : Fin arr.size) : α := -- pd.get a.data i sorry_proof
  match pd.btype with
  | .inl bitType => 
    let perByte := 8/bitType.bits
    let inByte  := (i.1 % perByte.toNat).toUInt8
    let ofByte  : Fin arr.byteData.size := ⟨i.1 / perByte.toNat, sorry_proof⟩
    let ones : UInt8 := 255
    let mask    := (ones - (ones <<< bitType.bits))   -- 00000111 
    -- masking is note necessary if `fromBytes` correctly ignores unused bits
    let byte    := mask &&& (arr.byteData[ofByte] >>> (inByte*bitType.bits))
    bitType.fromByte byte
  | .inr byteType => 
    byteType.fromByteArray arr.byteData (byteType.bytes * i.1) sorry_proof

def DataArray.set (arr : DataArray α) (i : Fin arr.size) (val : α) : DataArray α := -- ⟨pd.set a.byteData i sorry_proof val, a.size, sorry_proof⟩
  match pd.btype with
  | .inl bitType => 
    let perByte := 8/bitType.bits
    let inByte  := (i.1 % perByte.toNat).toUInt8
    let ofByte  := ⟨i.1 / perByte.toNat, sorry_proof⟩
    let ones : UInt8 := 255
    let mask    := ones - ((ones - (ones <<< bitType.bits)) <<< (inByte*bitType.bits))  --- 11000111 for bitType.bits = 3 and inByte = 1
    let byte    := arr.byteData[ofByte]
    let newByte := (mask &&& byte) + (bitType.toByte val <<< (inByte*bitType.bits))
    ⟨arr.byteData.set ofByte newByte, arr.size, sorry_proof⟩
  | .inr byteType => 
    ⟨byteType.toByteArray arr.byteData (byteType.bytes * i.1) sorry_proof val, arr.size, sorry_proof⟩


/-- Capacity of an array. The return type is `Squash Nat` as the capacity is is just an implementation detail and should not affect semantics of the program. -/
def DataArray.capacity (arr : DataArray α) : Squash Nat := Quot.mk _ (pd.capacity (arr.byteData.size))
/-- Makes sure that `arr` fits at least `n` elements of `α` -/
def DataArray.reserve  (arr : DataArray α) (n : Nat) : DataArray α := 
  if (pd.capacity (arr.byteData.size)) ≤ n then
    arr
  else Id.run do
    let newBytes := pd.bytes n
    let mut arr' : DataArray α := ⟨ByteArray.mkEmpty newBytes, arr.size, sorry_proof⟩
    -- copy over the old data
    for i in [0:arr.size] do
      arr' := ⟨arr'.byteData.push 0, arr.size, sorry_proof⟩
      arr' := arr'.set ⟨i,sorry_proof⟩ (arr.get ⟨i,sorry_proof⟩)
    arr'


def DataArray.drop (arr : DataArray α) (k : Nat) : DataArray α := ⟨arr.byteData, arr.size - k, sorry_proof⟩

def DataArray.push (arr : DataArray α) (k : Nat := 1) (val : α) : DataArray α := Id.run do
  let oldSize := arr.size
  let newSize := arr.size + k
  let mut arr' := arr.reserve newSize
  arr' := ⟨arr'.byteData, newSize, sorry_proof⟩
  for i in [oldSize:newSize] do
    arr' := arr'.set ⟨i,sorry_proof⟩ val
  arr'

/-- Extensionality of DataArray

Currently this is inconsistent, we need to turn DataArray into quotient!
-/
theorem DataArray.ext (d d' : DataArray α) : (h : d.size = d'.size) → (∀ i, d.get i = d'.get (h ▸ i)) → d = d' := sorry_proof

def DataArray.intro (f : ι → α) : DataArray α := Id.run do
  let bytes := (pd.bytes (numOf ι))
  let mut d : ByteArray := ByteArray.mkEmpty bytes
  for _ in [0:bytes] do
    d := d.push 0
  let mut d' : DataArray α := ⟨d, (numOf ι), sorry_proof⟩
  for (i,li) in Enumtype.fullRange ι do
    d' := d'.set ⟨li,sorry_proof⟩ (f i)
  d'

structure DataArrayN (α : Type) [pd : PlainDataType α] (n : Nat) where
  data : DataArray α
  h_size : n = data.size

instance (n) : GetElem (DataArrayN α n) (Fin n) α (λ _ _ => True) where
  getElem xs i _ := xs.1.get (xs.2 ▸ i)

instance : GetElem (DataArrayN α (numOf ι)) ι α (λ _ _ => True) where
  getElem xs i _ := xs.1.get (xs.2 ▸ toFin i)

instance : SetElem (DataArrayN α n) (Fin n) α where
  setElem xs i xi := ⟨xs.1.set (xs.2 ▸ i) xi, sorry_proof⟩

instance : SetElem (DataArrayN α (numOf ι)) ι α where
  setElem xs i xi := ⟨xs.1.set (xs.2 ▸ toFin i) xi, sorry_proof⟩

instance : IntroElem (DataArrayN α n) (Fin n) α where
  introElem f := ⟨DataArray.intro f, sorry_proof⟩

instance : IntroElem (DataArrayN α (numOf ι)) ι α where
  introElem f := ⟨DataArray.intro f, sorry_proof⟩

instance : PushElem (DataArrayN α) α where
  pushElem k val xs := ⟨xs.1.push k val, sorry_proof⟩

instance : DropElem (DataArrayN α) α where
  dropElem k xs := ⟨xs.1.drop k, sorry_proof⟩

instance : ReserveElem (DataArrayN α) α where
  reserveElem k xs := ⟨xs.1.reserve k, sorry_proof⟩

instance : GenericArray (DataArrayN α n) (Fin n) α  where
  ext := sorry_proof
  getElem_setElem_eq := sorry_proof
  getElem_setElem_neq := sorry_proof
  getElem_introElem := sorry_proof

instance : GenericLinearArray (DataArrayN α) α  where
  toGenericArray := by infer_instance
  pushElem_getElem := sorry_proof
  dropElem_getElem := sorry_proof
  reserveElem_id := sorry_proof

instance : GenericArray (DataArrayN α (numOf ι)) ι α  where
  ext := sorry_proof
  getElem_setElem_eq := sorry_proof
  getElem_setElem_neq := sorry_proof
  getElem_introElem := sorry_proof

@[infer_tc_goals_rl]
instance {Cont ι α : Type} [Enumtype ι] [Inhabited α] [pd : PlainDataType α] [GenericArray Cont ι α] : PlainDataType Cont where
  btype := match pd.btype with
    | .inl αBitType => 
      -- TODO: Fixme !!!!
      .inr {
        bytes := 2
        h_size := sorry_proof

        fromByteArray := λ b i h => 
          introElem (λ j => default)
        toByteArray   := λ b i h c => b
        toByteArray_size := sorry_proof
        fromByteArray_toByteArray := sorry_proof
        fromByteArray_toByteArray_other := sorry_proof
      }
    | .inr αByteType => 
      .inr {
        bytes := (numOf ι) * αByteType.bytes
        h_size := sorry_proof

        fromByteArray := λ b i h => 
          introElem (λ j => 
            let idx := (i + (toFin j).1*αByteType.bytes)
            αByteType.fromByteArray b idx sorry_proof)
        toByteArray   := λ b i h c => Id.run do
          let mut b := b
          for (j,lj) in Enumtype.fullRange ι do
            let idx := (i + lj.1*αByteType.bytes)
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



-- #check ℝ^(Fin 3)

-- #eval ((λ [i] => i.1.toReal ) : ℝ^(Fin 100)) |>.map Math.sqrt

-- #eval ((λ [i] => i) : (Fin 3 × Fin 5)^(Fin 3 × Fin 5))
-- #eval ((λ [i] => i) : (Fin 3 × Fin 5)^(Fin 3 × Fin 5)).data
-- #eval ((λ [i] => i) : (Fin 3 × Fin 5)^(Fin 3 × Fin 5)).data.byteData

-- #eval (1,2,3,4)

-- #eval ((λ [i] => i) : (Fin 3 × Fin 2 × Fin 2)^(Fin 3 × Fin 2 × Fin 2))
-- #eval ((λ [i] => i) : (Fin 3 × Fin 2 × Fin 2)^(Fin 3 × Fin 2 × Fin 2)).data
-- #eval ((λ [i] => i) : (Fin 3 × Fin 2 × Fin 2)^(Fin 3 × Fin 2 × Fin 2)).data.byteData

-- #eval ((λ [i] => (i.1.toFloat, i.1.toFloat.sqrt)) : (Float × Float)^(Fin 17))

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
--   let mut a : ℝ^(Fin 3 × Fin 3) := 0
--   for ((i,j),li) in Enumtype.fullRange a.Index do
--     a[li] := if i = j then 1 else 0
--   a
