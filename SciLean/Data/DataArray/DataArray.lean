import SciLean.Data.DataArray.PlainDataType
import SciLean.Data.ArrayType.Basic
import SciLean.Data.ArrayType.Notation
import SciLean.Tactic.InferVar
import SciLean.Data.IndexType

set_option linter.unusedVariables false

namespace SciLean

def _root_.ByteArray.mkArray (n : Nat) (v : UInt8) : ByteArray := Id.run do
  let mut a : ByteArray := .mkEmpty n
  for i in [0:n] do
    a := a.push v
  a

-- TODO: Quotient it out by trailing bits
structure DataArray (α : Type*) [pd : PlainDataType α] where
  byteData : ByteArray
  size : Nat
  h_size : pd.bytes size ≤ byteData.size

variable {α : Type*} [pd : PlainDataType α]
variable {ι} [IndexType ι] {κ : Type*} [IndexType κ]

instance [PlainDataType X] : Inhabited (DataArray X) := ⟨.empty, 0, by sorry_proof⟩

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
    for i in fullRange (Fin arr.size) do
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
  let bytes := (pd.bytes (Size.size ι))
  let d : ByteArray := ByteArray.mkArray bytes 0
  let mut d' : DataArray α := ⟨d, (Size.size ι), sorry_proof⟩
  for i in fullRange ι do
    d' := d'.set ⟨(IndexType.toFin i).1,sorry_proof⟩ (f i)
  d'


instance [ToString α] : ToString (DataArray α) := ⟨λ x => Id.run do
  let mut fst := true
  let mut s := "⊞["
  for i in [0:x.size] do
    let i : Fin (x.size) := ⟨i, sorry_proof⟩
    if fst then
      s := s ++ toString x[i]
      fst := false
    else
      s := s ++ ", " ++ toString x[i]
  s ++ "]"⟩


structure DataArrayN (α : Type*) [pd : PlainDataType α] (ι : Type*) [IndexType ι] where
  data : DataArray α
  h_size : Size.size ι = data.size


instance {I} [IndexType I] [PlainDataType X] : Inhabited (DataArrayN X I) := ⟨default, sorry_proof⟩

def DataArrayN.get (xs : DataArrayN α ι) (i : ι) : α := (xs.1.get ((IndexType.toFin i).cast xs.2))

def DataArrayN.linGet (xs : DataArrayN α ι) (i : Fin (Size.size ι)) : α := (xs.1.get ⟨i,by rw[←xs.2]; omega⟩)

def DataArrayN.set (xs : DataArrayN α ι) (i : ι) (xi : α) : DataArrayN α ι :=
  ⟨xs.1.set ((IndexType.toFin i).cast xs.2) xi, sorry_proof⟩


def DataArrayN.modify (xs : DataArrayN α ι) (i : ι) (f : α → α) : DataArrayN α ι :=
  xs.set i (f (xs.get i))


def DataArrayN.toList (xs : DataArrayN α ι) : List α := Id.run do
  let mut l : List α := []
  for i in fullRange ι do
    l := xs.get i :: l
  return l


def DataArrayN.toListIdx (xs : DataArrayN α ι) : List (ι × α) := Id.run do
  let mut l : List (ι × α) := []
  for i in fullRange ι do
    l := (i, xs.get i) :: l
  return l


instance : Membership α (DataArrayN α ι) where
  mem xs x := ∃ i, xs.get i = x


instance : ArrayType (DataArrayN α ι) ι α where
  ofFn f := ⟨DataArray.intro f, sorry_proof⟩
  get xs i := xs.get i
  set xs i x := xs.set i x
  modify xs i f := xs.modify i f
  get_ofFn := sorry_proof
  ofFn_get := sorry_proof
  get_set_eq := sorry_proof
  get_set_neq := sorry_proof
  modify_set := sorry_proof

-- instance : LinearArrayType (λ n => DataArrayN α (Fin n)) α where
--   toArrayType := by infer_instance
--   pushElem_getElem := sorry_proof
--   dropElem_getElem := sorry_proof
--   reserveElem_id := sorry_proof

def DataArrayN.reshape (x : DataArrayN α ι) (κ : Type*) [IndexType κ]
  (hs : size κ = size ι)
  : DataArrayN α κ :=
  ⟨x.data, by simp[hs,x.h_size]⟩

def DataArrayN.flatten (x : DataArrayN α ι)
    {n} (hn : n = size ι := by infer_var) :
    DataArrayN α (Fin n) :=
  x.reshape (Fin n) (by simp[hn])


instance {Cont ι α : Type*} [ArrayType Cont ι α] [IndexType ι] [Inhabited α] [pd : PlainDataType α] :
    PlainDataType Cont where
  btype := match pd.btype with
    | .inl αBitType =>
      -- TODO: Fixme !!!!
      .inr {
        bytes := 2
        h_size := sorry_proof

        fromByteArray := λ b i h =>
          ArrayType.ofFn (λ j => panic! "not implemented!")
        toByteArray   := λ b i h c => panic! "not implemented!"
        toByteArray_size := sorry_proof
        fromByteArray_toByteArray := sorry_proof
        fromByteArray_toByteArray_other := sorry_proof
      }
    | .inr αByteType =>
      .inr {
        bytes := (size ι).toUSize * αByteType.bytes
        h_size := sorry_proof

        fromByteArray := λ b i h =>
          ArrayType.ofFn (λ j =>
            let Fin := (i + (IndexType.toFin j).1.toUSize *αByteType.bytes)
            αByteType.fromByteArray b Fin sorry_proof)
        toByteArray   := λ b i h c => Id.run do
          let mut b := b
          let mut lj : USize := 0
          for j in fullRange ι do
            let Fin := (i + lj*αByteType.bytes)
            lj := lj + 1
            b := αByteType.toByteArray b Fin sorry_proof c[j]
          b

        toByteArray_size := sorry_proof
        fromByteArray_toByteArray := sorry_proof
        fromByteArray_toByteArray_other := sorry_proof
      }



def DataArrayN.curry [Inhabited α] (x : DataArrayN α (ι×κ)) : DataArrayN (DataArrayN α κ) ι :=
  ⟨⟨x.data.byteData, Size.size ι, sorry_proof⟩, sorry_proof⟩

def DataArrayN.uncurry [Inhabited α] (x : DataArrayN (DataArrayN α κ) ι) : DataArrayN α (ι×κ) :=
  ⟨⟨x.data.byteData, Size.size ι, sorry_proof⟩, sorry_proof⟩

theorem DataArrayN.uncurry_def [Inhabited α] (x : DataArrayN (DataArrayN α κ) ι) :
    x.uncurry = ⊞ i j => x[i][j] := sorry_proof

set_option linter.dupNamespace false in
open Lean in
private partial def parseDimProd (s : Syntax) : TSyntaxArray `dimSpec :=
  match s with
  | `(Fin $n)      => #[⟨n.raw⟩]
  | `(Fin $n × $I) => #[⟨n.raw⟩] ++ parseDimProd I
  | `($J × $I)     => #[⟨J.raw⟩] ++ parseDimProd I
  | `($I)          => #[⟨I.raw⟩]

@[app_unexpander DataArrayN]
def unexpandDataArrayN : Lean.PrettyPrinter.Unexpander
  | `($(_) $α $I) =>
    let dims := parseDimProd I
    `($α^[$dims,*])
  | _  => throw ()
