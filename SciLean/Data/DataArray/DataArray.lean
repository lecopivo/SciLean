import SciLean.Data.DataArray.PlainDataType
import SciLean.Data.ArrayType.Basic
import SciLean.Data.ArrayType.Notation

set_option linter.unusedVariables false

namespace SciLean
open LeanColls

def _root_.ByteArray.mkArray (n : Nat) (v : UInt8) : ByteArray := Id.run do
  let mut a : ByteArray := .mkEmpty n
  for i in [0:n] do
    a := a.push v
  a

-- TODO: Quotient it out by trailing bits
structure DataArray (α : Type) [pd : PlainDataType α] where
  byteData : ByteArray
  size : Nat
  h_size : pd.bytes size ≤ byteData.size

variable {α : Type} [pd : PlainDataType α]
variable {ι} [IndexType ι]

@[irreducible]
def DataArray.get (arr : DataArray α) (i : Fin arr.size) : α := -- pd.get a.data i sorry_proof
  let i := i.1.toUSize
  match pd.btype with
  | .inl bitType =>
    let perByte := 8/bitType.bits
    let inByte  := (i % perByte.toUSize).toUInt8
    let ofByte  := i / perByte.toUSize
    let ones : UInt8 := 255
    let mask    := (ones - (ones <<< bitType.bits))   -- 00000111
    -- masking is note necessary if `fromBytes` correctly ignores unused bits
    let byte    := mask &&& (arr.byteData.uget ofByte sorry_proof >>> (inByte*bitType.bits))
    bitType.fromByte byte
  | .inr byteType =>
    byteType.fromByteArray arr.byteData (byteType.bytes * i) sorry_proof

instance : GetElem (DataArray α) Nat α (fun a i => i < a.size) where
  getElem := fun x i h => x.get ⟨i,h⟩

@[irreducible]
def DataArray.set (arr : DataArray α) (i : Fin arr.size) (val : α) : DataArray α := -- ⟨pd.set a.byteData i sorry_proof val, a.size, sorry_proof⟩
  let i := i.1.toUSize
  match pd.btype with
  | .inl bitType =>
    let perByte := 8/bitType.bits
    let inByte  := (i % perByte.toUSize).toUInt8
    let ofByte  := i / perByte.toUSize
    let ones : UInt8 := 255
    let mask    := ones - ((ones - (ones <<< bitType.bits)) <<< (inByte*bitType.bits))  --- 11000111 for bitType.bits = 3 and inByte = 1
    let byte    := arr.byteData.uget ofByte sorry_proof
    let newByte := (mask &&& byte) + (bitType.toByte val <<< (inByte*bitType.bits))
    ⟨arr.byteData.uset ofByte newByte sorry_proof, arr.size, sorry_proof⟩
  | .inr byteType =>
    ⟨byteType.toByteArray arr.byteData (byteType.bytes * i) sorry_proof val, arr.size, sorry_proof⟩


/-- Capacity of an array. The return type is `Squash Nat` as the capacity is is just an implementation detail and should not affect semantics of the program. -/
def DataArray.capacity (arr : DataArray α) : Squash Nat := Quot.mk _ (pd.capacity (arr.byteData.size))
/-- Makes sure that `arr` fits at least `n` elements of `α` -/
def DataArray.reserve  (arr : DataArray α) (capacity : Nat) : DataArray α :=
  if capacity ≤ (pd.capacity (arr.byteData.size)) then
    arr
  else Id.run do
    let newBytes := pd.bytes capacity
    let mut arr' : DataArray α := ⟨ByteArray.mkArray newBytes 0, arr.size, sorry_proof⟩
    -- copy over the old data
    for i in IndexType.univ (Fin arr.size) do
      arr' := arr'.set ⟨i.1,sorry_proof⟩ (arr.get i)
    arr'

def DataArray.mkEmpty (capacity : Nat) : DataArray α := Id.run do
  let newBytes := pd.bytes capacity
  { byteData := .mkArray newBytes 0
    size := 0
    h_size := by sorry_proof }

def DataArray.drop (arr : DataArray α) (k : Nat) : DataArray α := ⟨arr.byteData, arr.size - k, sorry_proof⟩

def DataArray.push (arr : DataArray α) (val : α) (k : Nat := 1) : DataArray α := Id.run do
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

def DataArray.swap (arr : DataArray α) (i j : Fin arr.size) : DataArray α :=
  let ai := arr.get i
  let aj := arr.get j
  let arr := arr.set i aj
  let arr := arr.set ⟨j.1, sorry_proof⟩ ai
  arr

def DataArray.reverse (arr : DataArray α) : DataArray α := Id.run do
  let mut arr := arr
  let n := arr.size
  for i in [0:n/2] do
    let i' : Fin arr.size := ⟨i, sorry_proof⟩
    let j' : Fin arr.size := ⟨n - i - 1, sorry_proof⟩
    arr := arr.swap i' j'
  arr


@[irreducible]
def DataArray.intro (f : ι → α) : DataArray α := Id.run do
  let bytes := (pd.bytes (IndexType.card ι))
  let d : ByteArray := ByteArray.mkArray bytes 0
  let mut d' : DataArray α := ⟨d, (IndexType.card ι), sorry_proof⟩
  for i in IndexType.univ ι do
    d' := d'.set ⟨(IndexType.toFin i).1,sorry_proof⟩ (f i)
  d'

structure DataArrayN (α : Type) [pd : PlainDataType α] (ι : Type) [IndexType.{0,0} ι] where
  data : DataArray α
  h_size : IndexType.card ι = data.size

def DataArrayN.get (xs : DataArrayN α ι) (i : ι) : α := (xs.1.get ((IndexType.toFin i).cast xs.2))
def DataArrayN.set (xs : DataArrayN α ι) (i : ι) (xi : α) : DataArrayN α ι :=
  ⟨xs.1.set ((IndexType.toFin i).cast xs.2) xi, sorry_proof⟩
def DataArrayN.modify (xs : DataArrayN α ι) (i : ι) (f : α → α) : DataArrayN α ι :=
  xs.set i (f (xs.get i))

def DataArrayN.toList (xs : DataArrayN α ι) : List α := Id.run do
  let mut l : List α := []
  for i in IndexType.univ ι do
    l := xs.get i :: l
  return l

def DataArrayN.toListIdx (xs : DataArrayN α ι) : List (ι × α) := Id.run do
  let mut l : List (ι × α) := []
  for i in IndexType.univ ι do
    l := (i, xs.get i) :: l
  return l


instance : Membership α (DataArrayN α ι) where
  mem x xs := ∃ i, xs.get i = x

instance : Membership (ι × α) (Indexed.WithIdx (DataArrayN α ι)) where
  mem := fun (i,x) xs => xs.1.get i = x

instance : ToMultiset (DataArrayN α ι) α where
  toMultiset xs := .ofList xs.toList

instance : ToMultiset (Indexed.WithIdx (DataArrayN α ι)) (ι × α) where
  toMultiset xs := .ofList (xs.1.toListIdx)

instance : Fold (DataArrayN α ι) α where
  fold  xs f init := fold (IndexType.univ ι) (fun b i => f b (xs.get i)) init
  foldM xs f init := fold (IndexType.univ ι) (fun b i => do f (← b) (xs.get i)) (pure init)

instance : Fold (Indexed.WithIdx (DataArrayN α ι)) (ι × α) where
  fold  xs f init := fold (IndexType.univ ι) (fun b i => f b (i, xs.1.get i)) init
  foldM xs f init := fold (IndexType.univ ι) (fun b i => do f (← b) (i, xs.1.get i)) (pure init)

instance : Size (DataArrayN α ι) where
  size xs := IndexType.card ι

instance : Size (Indexed.WithIdx (DataArrayN α ι)) where
  size xs := IndexType.card ι

instance : MultiBag.ReadOnly (DataArrayN α ι) α := ⟨⟩
instance : MultiBag.ReadOnly (Indexed.WithIdx (DataArrayN α ι)) (ι × α) := ⟨⟩

instance : Indexed (DataArrayN α ι) ι α where
  toMultiBagWithIdx := inferInstance
  ofFn f := ⟨DataArray.intro f, sorry_proof⟩
  get xs i := xs.get i
  set xs i x := xs.set i x
  update xs i f := xs.modify i f

instance : LawfulIndexed (DataArrayN α ι) ι α where
  get_ofFn := sorry_proof
  get_set_eq := sorry_proof
  get_set_ne := sorry_proof
  get_update_eq := sorry_proof
  get_update_ne := sorry_proof

instance : ArrayType (DataArrayN α ι) ι α where
  get_injective := sorry_proof

-- @[inline]
-- instance : GetElem (DataArrayN α ι) ι α (λ _ _ => True) where
--   getElem xs i _ := xs.1.get ((IndexType.toFin i).cast xs.2)

-- @[inline]
-- instance : SetElem (DataArrayN α ι) ι α where
--   setElem xs i xi := ⟨xs.1.set ((IndexType.toFin i).cast xs.2) xi, sorry_proof⟩

-- @[inline]
-- instance : IntroElem (DataArrayN α ι) ι α where
--   introElem f := ⟨DataArray.intro f, sorry_proof⟩

-- instance : StructType (DataArrayN α ι) ι (fun _ => α) where
--   structProj x i := x.get i
--   structMake f := Indexed.ofFn f
--   structModify i f x := Indexed.update x i f
--   left_inv := sorry_proof
--   right_inv := sorry_proof
--   structProj_structModify  := sorry_proof
--   structProj_structModify' := sorry_proof

instance : ArrayTypeNotation (DataArrayN α ι) ι α := ⟨⟩

-- instance : LinearArrayType (λ n => DataArrayN α (Fin n)) α where
--   toArrayType := by infer_instance
--   pushElem_getElem := sorry_proof
--   dropElem_getElem := sorry_proof
--   reserveElem_id := sorry_proof

def DataArrayN.reshape (x : DataArrayN α ι) (κ : Type) [IndexType κ]
  (hs : IndexType.card κ = IndexType.card ι)
  : DataArrayN α κ :=
  ⟨x.data, by simp[hs,x.h_size]⟩

instance {Cont ι α : Type} [ArrayType Cont ι α] [IndexType ι] [Inhabited α] [pd : PlainDataType α] :
    PlainDataType Cont where
  btype := match pd.btype with
    | .inl αBitType =>
      -- TODO: Fixme !!!!
      .inr {
        bytes := 2
        h_size := sorry_proof

        fromByteArray := λ b i h =>
          Indexed.ofFn (λ j => panic! "not implemented!")
        toByteArray   := λ b i h c => panic! "not implemented!"
        toByteArray_size := sorry_proof
        fromByteArray_toByteArray := sorry_proof
        fromByteArray_toByteArray_other := sorry_proof
      }
    | .inr αByteType =>
      .inr {
        bytes := (IndexType.card ι).toUSize * αByteType.bytes
        h_size := sorry_proof

        fromByteArray := λ b i h =>
          Indexed.ofFn (λ j =>
            let Fin := (i + (IndexType.toFin j).1.toUSize *αByteType.bytes)
            αByteType.fromByteArray b Fin sorry_proof)
        toByteArray   := λ b i h c => Id.run do
          let mut b := b
          let mut lj : USize := 0
          for j in IndexType.univ ι do
            let Fin := (i + lj*αByteType.bytes)
            lj := lj + 1
            b := αByteType.toByteArray b Fin sorry_proof c[j]
          b

        toByteArray_size := sorry_proof
        fromByteArray_toByteArray := sorry_proof
        fromByteArray_toByteArray_other := sorry_proof
      }
