import SciLean.Data.DataArray.PlainDataType
import SciLean.Data.ArrayType.Basic
import SciLean.Data.ArrayType.Notation
import SciLean.Tactic.InferVar
import SciLean.Data.IndexType
import SciLean.Data.IndexType.Basic
import SciLean.Data.IndexType.Fold
import SciLean.Data.ArrayLike

set_option linter.unusedVariables false

namespace SciLean

-- def _root_.ByteArray.replicate (n : Nat) (v : UInt8) : ByteArray := Id.run do
--   let mut a : ByteArray := .mkEmpty n
--   for i in fullRange (Idx n) do
--     a := a.push v
--   a

-- TODO: Quotient it out by trailing bits
structure DataArray (α : Type*) [pd : PlainDataType α] where
  byteData : ByteArray
  h_size : byteData.size % pd.btype.bytes.toNat = 0

variable {α : Type*} [pd : PlainDataType α]
variable {ι n} [IndexType ι n] {κ : Type*} {m} [IndexType κ m]

instance [PlainDataType X] : Inhabited (DataArray X) := ⟨.empty, by sorry_proof⟩

@[inline]
def DataArray.size (xs : DataArray α) : Nat := xs.byteData.size / pd.btype.bytes.toNat

@[inline]
def DataArray.get (arr : DataArray α) (i : Idx arr.size) : α :=
  pd.btype.fromByteArray arr.byteData (pd.btype.bytes * i) sorry_proof

  -- let i := i.1
  -- match pd.btype with
  -- | .inl bitType =>
  --   let perByte := 8/bitType.bits
  --   let inByte  := (i % perByte.toUSize).toUInt8
  --   let ofByte  := i / perByte.toUSize
  --   let ones : UInt8 := 255
  --   let mask    := (ones - (ones <<< bitType.bits))   -- 00000111
  --   -- masking is note necessary if `fromBytes` correctly ignores unused bits
  --   let byte    := mask &&& (arr.byteData.uget ofByte sorry_proof >>> (inByte*bitType.bits))
  --   bitType.fromByte byte
  -- | .inr byteType =>
  --   byteType.fromByteArray arr.byteData (byteType.bytes * i) sorry_proof

instance : GetElem (DataArray α) USize α (fun a i => i.toNat < a.size) where
  getElem := fun x i h => x.get ⟨i,h⟩

@[inline]
def DataArray.set (arr : DataArray α) (i : Idx arr.size) (val : α) : DataArray α := -- ⟨pd.set a.byteData i sorry_proof val, a.size, sorry_proof⟩
  ⟨pd.btype.toByteArray arr.byteData (pd.btype.bytes * i) sorry_proof val, sorry_proof⟩

instance : SetElem (DataArray α) USize α (fun a i => i.toNat < a.size) where
  setElem := fun x i v h => x.set ⟨i,h⟩ v
  setElem_valid := sorry_proof

  -- let i := i.1
  -- match pd.btype with
  -- | .inl bitType =>
  --   let perByte := 8/bitType.bits
  --   let inByte  := (i % perByte.toUSize).toUInt8
  --   let ofByte  := i / perByte.toUSize
  --   let ones : UInt8 := 255
  --   let mask    := ones - ((ones - (ones <<< bitType.bits)) <<< (inByte*bitType.bits))  --- 11000111 for bitType.bits = 3 and inByte = 1
  --   let byte    := arr.byteData.uget ofByte sorry_proof
  --   let newByte := (mask &&& byte) + (bitType.toByte val <<< (inByte*bitType.bits))
  --   ⟨arr.byteData.uset ofByte newByte sorry_proof, arr.size, sorry_proof⟩
  -- | .inr byteType =>
  --   ⟨byteType.toByteArray arr.byteData (byteType.bytes * i) sorry_proof val, arr.size, sorry_proof⟩


/-- Capacity of an array. The return type is `Squash Nat` as the capacity is is just an implementation detail and should not affect semantics of the program. -/
def DataArray.capacity (arr : DataArray α) : Squash Nat := Quot.mk _ (pd.capacity (arr.byteData.size))

-- /-- Makes sure that `arr` fits at least `n` elements of `α` -/
-- def DataArray.reserve  (arr : DataArray α) (capacity : Nat) : DataArray α :=
--   ⟨arr.byteData, sorry_proof⟩
  -- if capacity ≤ (pd.capacity (arr.byteData.size)) then
  --   arr
  -- else Id.run do
  --   let newBytes := pd.bytes capacity
  --   let mut arr' : DataArray α := ⟨ByteArray.mkArray newBytes 0, arr.size, sorry_proof⟩
  --   -- copy over the old data
  --   for i in fullRange (Idx arr.size) do
  --     arr' := arr'.set ⟨i.1,sorry_proof⟩ (arr.get i)
  --   arr'

def DataArray.emptyWithCapacity (capacity : Nat) : DataArray α := Id.run do
  let newBytes := pd.bytes capacity
  { byteData := .emptyWithCapacity newBytes
    h_size := by sorry_proof }

def DataArray.mkZero (n : Nat) : DataArray α := Id.run do
  ⟨ByteArray.replicate (pd.bytes n) 0, sorry_proof⟩

def DataArray.replicate (n : Nat) (v : α) : DataArray α := Id.run do
  -- TODO: make unsafe version that does not zero initialize
  let mut data : DataArray α := .mkZero n
  for i in fullRange (Idx data.size) do
    data := data.set ⟨i,sorry_proof⟩ v
  return data


/-- Push array `y` to array `x` `k`-times  -/
def _root_.SciLean.DataArray.pushArray (x y : DataArray α) (k : Nat := 1) : DataArray α := Id.run do
  let mut data := x.1 -- todo: reserve enough memory upfront
  let ydata := y.1
  let offset := data.size.toUSize
  let width := ydata.size.toUSize
  for i in fullRange (Idx k) do
    let idx := offset + i*width
    data := ydata.copySlice 0 data idx.toNat width.toNat
  return ⟨data, sorry_proof⟩

/-- Push element `v` to array `x` `k`-times  -/
def _root_.SciLean.DataArray.push (x : DataArray α) (v : α) (k : Nat := 1) : DataArray α := Id.run do
  let v' := DataArray.replicate 1 v
  x.pushArray v' k


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
  for i in fullRange (Idx (n/2)) do
    let i' : Idx arr.size := ⟨i, sorry_proof⟩
    let j' : Idx arr.size := ⟨n.toUSize - i - 1, sorry_proof⟩
    arr := arr.swap i' j'
  arr


-- @[inline, specialize]
-- def DataArray.intro {ι n} [IndexType ι n] [Fold ι]
--     (f : ι → α) : DataArray α := Id.run do
--   let mut d' : DataArray α := .mkZero n
--   for i in fullRange ι do
--     d' := d'.set ⟨toIdx i, sorry_proof⟩ (f i)
--   d'

@[inline]
def DataArray.intro {ι n} [IndexType ι n] [Fold ι]
    (f : ι → α) : DataArray α := aux toIdx
where
  @[specialize]
  aux (toIdx : ι → Idx n) : DataArray α := Id.run do
    let mut d' : DataArray α := .mkZero n
    for i in fullRange ι do
      d' := d'.set ⟨toIdx i, sorry_proof⟩ (f i)
    d'


instance [ToString α] : ToString (DataArray α) := ⟨λ x => Id.run do
  let mut fst := true
  let mut s := "⊞["
  for i in fullRange (Idx x.size) do
    -- let i : Idx (x.size) := ⟨i, sorry_proof⟩
    if fst then
      s := s ++ toString (x.get i)
      fst := false
    else
      s := s ++ ", " ++ toString (x.get i)
  s ++ "]"⟩


structure DataArrayN (α : Type*) [pd : PlainDataType α] (ι : Type*) {n : outParam ℕ} [Size' ι n] : Type where
  data : DataArray α
  h_size : n = data.size


instance {I n} [IndexType I n] [PlainDataType X] : Inhabited (DataArrayN X I) := ⟨default, sorry_proof⟩

@[inline]
def DataArrayN.get (xs : DataArrayN α ι) (i : ι) : α := (xs.1.get ((toIdx i).cast xs.2))

@[inline]
def DataArrayN.linGet (xs : DataArrayN α ι) (i : Idx n) : α := (xs.1.get (i.cast xs.2))

@[inline]
def DataArrayN.linSet (xs : DataArrayN α ι) (i : Idx n) (xi : α) : DataArrayN α ι :=
  ⟨xs.1.set (i.cast xs.2) xi, sorry_proof⟩

@[inline]
def DataArrayN.set (xs : DataArrayN α ι) (i : ι) (xi : α) : DataArrayN α ι :=
  xs.linSet (toIdx i) xi

@[inline]
def DataArrayN.modify (xs : DataArrayN α ι) (i : ι) (f : α → α) : DataArrayN α ι :=
  xs.set i (f (xs.get i))

instance : GetElem (α^[ι]) ι α (fun _ _ => True) where
  getElem x i _ := x.get i

instance : InjectiveGetElem (α^[ι]) ι where
  getElem_injective := sorry_proof

instance : DefaultIndex (α^[ι]) ι where
instance : DefaultIndexOfRank (α^[ι]) 1 ι where
instance {r} [DefaultIndexOfRank (α^[κ]) r κ] : DefaultIndexOfRank (α^[ι,κ]) (r+1) (ι×κ) where

instance : SetElem (α^[ι]) ι α (fun _ _ => True) where
  setElem x i v _ := x.set i v
  setElem_valid := sorry_proof

instance : LawfulSetElem (α^[ι]) ι where
  getElem_setElem_eq  := sorry_proof
  getElem_setElem_neq := sorry_proof

instance [Fold ι] : OfFn (α^[ι]) ι α where
  ofFn f := ⟨DataArray.intro f, sorry_proof⟩

instance [Fold ι] : LawfulOfFn (α^[ι]) ι where
  getElem_ofFn := sorry_proof

instance {α} [PlainDataType α] {ι n} [IndexType ι n] : DefaultCollection (α^[ι]) ι α where

def DataArrayN.toList [Fold ι] (xs : DataArrayN α ι) : List α := Id.run do
  let mut l : List α := []
  for i in fullRange ι do
    l := xs.get i :: l
  return l


def DataArrayN.toListIdx [Fold ι] (xs : DataArrayN α ι) : List (ι × α) := Id.run do
  let mut l : List (ι × α) := []
  for i in fullRange ι do
    l := (i, xs.get i) :: l
  return l


instance : Membership α (DataArrayN α ι) where
  mem xs x := ∃ i, xs.get i = x

instance [Fold ι] : ArrayType (DataArrayN α ι) ι α where
  ofFn f := ⟨DataArray.intro f, sorry_proof⟩
  get xs i := xs.get i
  set xs i x := xs.set i x
  modify xs i f := xs.modify i f
  get_ofFn := sorry_proof
  ofFn_get := sorry_proof
  get_set_eq := sorry_proof
  get_set_neq := sorry_proof
  modify_set := sorry_proof

-- instance : LinearArrayType (λ n => DataArrayN α (Idx n)) α where
--   toArrayType := by infer_instance
--   pushElem_getElem := sorry_proof
--   dropElem_getElem := sorry_proof
--   reserveElem_id := sorry_proof

@[inline]
unsafe def DataArrayN.reshapeUnsafe {ι n} [IndexType ι n] (x : DataArrayN α ι) (κ : Type*) {m} [IndexType κ m]
  (hs : m = n) : DataArrayN α κ := unsafeCast x

@[inline, implemented_by DataArrayN.reshapeUnsafe]
def DataArrayN.reshape {I nI} [IndexType I nI] (x : DataArrayN α I) (J : Type*) {nJ} [IndexType J nJ]
  (hs : nJ = nI) : DataArrayN α J :=
  ⟨x.data, by rw[hs]; exact x.h_size⟩

def DataArrayN.flatten {ι n} [IndexType ι n] (x : DataArrayN α ι) :
    DataArrayN α (Idx n) :=
  x.reshape (Idx n) rfl


instance {ι α : Type*} {n} [IndexType ι n] [pd : PlainDataType α] :
    PlainDataType (DataArrayN α ι) where

  btype := {
    bytes := (pd.bytes n).toUSize
    h_size := sorry_proof

    fromByteArray := λ b i h =>
      let N := pd.bytes n
      let bi := b.copySlice (i.toNat) (ByteArray.emptyWithCapacity N) 0 N
      ⟨⟨bi,sorry_proof⟩,sorry_proof⟩
    toByteArray   := λ b i h c => Id.run do
      let N := pd.bytes n
      let b := c.1.1.copySlice 0 b (i.toNat) N
      b
    toByteArray_size := sorry_proof
    fromByteArray_toByteArray := sorry_proof
    fromByteArray_toByteArray_other := sorry_proof
  }


-- def ArrayType.instPlainDataType {Cont ι α : Type*} [ArrayType Cont ι α] [IndexType ι] [pd : PlainDataType α] :
--     PlainDataType Cont where
--   btype := match pd.btype with
--     | .inl αBitType =>
--       -- TODO: Fixme !!!!
--       .inr {
--         bytes := 2
--         h_size := sorry_proof

--         fromByteArray := λ b i h =>
--           ArrayType.ofFn (λ j =>
--             dbg_trace "fix me! instance implementation in DataArray.lean"
--             αBitType.fromByte 0)
--         toByteArray   := λ b i h c =>
--           dbg_trace "fix me! instance implementation in DataArray.lean"
--           b
--         toByteArray_size := sorry_proof
--         fromByteArray_toByteArray := sorry_proof
--         fromByteArray_toByteArray_other := sorry_proof
--       }
--     | .inr αByteType =>
--       .inr {
--         bytes := (size ι).toUSize * αByteType.bytes
--         h_size := sorry_proof

--         fromByteArray := λ b i h =>
--           ArrayType.ofFn (λ j =>
--             let Idx := (i + (IndexType.toIdx j).1.toUSize *αByteType.bytes)
--             αByteType.fromByteArray b Idx sorry_proof)
--         toByteArray   := λ b i h c => Id.run do
--           let mut b := b
--           let mut lj : USize := 0
--           for j in fullRange ι do
--             let Idx := (i + lj*αByteType.bytes)
--             lj := lj + 1
--             b := αByteType.toByteArray b Idx sorry_proof c[j]
--           b

--         toByteArray_size := sorry_proof
--         fromByteArray_toByteArray := sorry_proof
--         fromByteArray_toByteArray_other := sorry_proof
--       }

variable
  {X : Type u} [pd : PlainDataType X]
  {I : Type v} {nI : ℕ} [IndexType I nI]
  {J : Type w} {nJ : ℕ} [IndexType J nJ]

@[inline]
def DataArrayN.curry (x :  X^[I,J]) : X^[J]^[I] :=
  cast sorry_proof x -- this is slow at runtime ⟨⟨x.data.byteData, sorry_proof⟩, sorry_proof⟩

@[inline]
def DataArrayN.uncurry (x : X^[J]^[I]) : X^[I,J] :=
  cast sorry_proof x -- this is slow at runtime ⟨⟨x.data.byteData, sorry_proof⟩, sorry_proof⟩


theorem DataArrayN.uncurry_def [Fold.{_,0} I] [Fold.{_,0} J]
    (x : DataArrayN (DataArrayN X J) I) :
    -- x.uncurry = ⊞ i j => x[i][j] := sorry_proof
    x.uncurry = ofFn (↿fun i j => x[i][j]) := sorry_proof

theorem DataArrayN.uncurry_getElem
    (x : DataArrayN (DataArrayN X J) I) (i : I) (j : J) :
    x.uncurry[i,j] = x[i][j] := sorry_proof

theorem DataArrayN.curry_def [Fold.{_,0} I] [Fold.{_,0} J]
    (x : DataArrayN X (I×J)) :
    x.curry = ⊞ i => ⊞ j => x[i,j] := by
  sorry_proof

@[simp, simp_core]
theorem DataArrayN.curry_getElem (x : DataArrayN X (I×J)) (i : I) (j : J) :
    x.curry[i][j] = x[i,j] := by
  sorry_proof


@[inline]
def DataArrayN.row (x : X^[I,J]) (i : I) := x.curry[i]

def DataArrayN.col (x : X^[I,J]) (j : J) : X^[I] := Id.run do
  let xdata := x.1.1
  let mut data := ByteArray.emptyWithCapacity (pd.bytes nI)
  let offset := (toIdx j).1
  let width := (pd.bytes 1).toUSize
  let stride := (pd.bytes nJ).toUSize
  for i in fullRange (Idx nI) do
    let srcIdx := i.1*stride + offset*width
    let dstIdx := i.1*width
    data := xdata.copySlice srcIdx.toNat data dstIdx.toNat width.toNat
  return ⟨⟨data,sorry_proof⟩,sorry_proof⟩

@[simp, simp_core]
theorem DataArrayN.getElem_row (x : X^[I,J]) (i : I) (j : J) :
    (x.row i)[j] = x[i,j] := by simp[row,curry_getElem]

@[simp, simp_core]
theorem DataArrayN.getElem_col (x : X^[I,J]) (i : I) (j : J) :
    (x.col j)[i] = x[i,j] := by sorry_proof


def DataArrayN.transpose [Fold.{_,0} I] [Fold.{_,0} J] (x : X^[I,J]) : X^[J,I] := ⊞ j i => x[i,j]

@[simp, simp_core]
theorem DataArrayN.transpose_transpose [Fold.{_,0} I] [Fold.{_,0} J] (x : X^[I,J]) :
    x.transpose.transpose = x := by
  ext ⟨i,j⟩
  simp[transpose,Function.HasUncurry.uncurry]
  -- duh, why doesn't simp do this?
  exact (getElem_ofFn (coll:=X^[I,J]) (f :=_) (i:=(i,j)))



-- open IndexType in
-- /-- This instance is for convenience and for other type classes realted to `VectorType`.

-- But `x[i,j]` for `x : X^[J]^[I]` is considered to be confusing so the simp normal form of it is
-- `x.uncurry[i,j]`.  -/
-- instance : GetElem (X^[J]^[I]) (I×J) X (fun _ _ => True) where
--   getElem x ij _ := x.uncurry[ij]

-- /-- Expression `x[i,j]` for `x : X^[J]^[I]` is not considered to be in simp normal form so we
-- transform it to `x.uncurry[i,j]` -/
-- @[simp, simp_core]
-- theorem DataAraryN.getElem_uncurry (x : X^[J]^[I]) (i : I) (j : J) :
--     x[i,j] = x.uncurry[i,j] := rfl

-- instance : InjectiveGetElem (X^[J]^[I]) (I×J) where
--   getElem_injective := by
--     intro x y h
--     apply getElem_injective (idx:=I); funext i
--     apply getElem_injective (idx:=J); funext j
--     simp [← DataArrayN.uncurry_getElem]
--     exact congrFun h (i,j)

-- open IndexType
-- instance : SetElem (X^[J]^[I]) (I×J) X (fun _ _ => True) where
--   setElem x ij v _ := (setElem x.uncurry ij v .intro).curry
--   setElem_valid := sorry_proof

-- instance : LawfulSetElem (X^[J]^[I]) (I×J)  where
--   getElem_setElem_eq  := sorry_proof
--   getElem_setElem_neq := sorry_proof

-- instance : OfFn (X^[J]^[I]) (I×J) X  where
--   ofFn f := (ofFn (coll:=X^[I,J]) f).curry

-- /-- Expression `ofFn (coll:=X^[J]^[I]) f` is not considerd to be in simp normal form so we
-- immediatelly simplify it to `(ofFn (coll:=X^[I×J]) f).curry` -/
-- @[simp, simp_core]
-- theorem DataAraryN.ofFn_curry (f : I×J → X) :
--     (ofFn (coll:=X^[J]^[I]) f) = (ofFn (coll:=X^[I×J]) f).curry := rfl

-- instance : LawfulOfFn (X^[J]^[I]) (I×J)  where
--   getElem_ofFn := by
--     intro f (i,j)
--     simp[DataArrayN.uncurry_getElem,DataArrayN.curry_getElem]


set_option linter.dupNamespace false in
open Lean in
partial def parseDimProd (s : Syntax) : Lean.PrettyPrinter.UnexpandM (TSyntaxArray `dimSpec) := do
  match s with
  | .node _ ``coeNotation #[.atom _ "↑", .node _ ``Lean.Parser.Term.app #[.ident _ _ ``Set.Icc _,.node _ _ #[a,b]]] =>
    let a : Term := ⟨a⟩
    let b : Term := ⟨b⟩
    return #[← `(dimSpec| [$a :$b])]
  | _ =>
    match s with
    | `(Idx $n)      => return #[⟨n.raw⟩]
    | `($J × $I)     =>
      let js ← parseDimProd J
      let is ← parseDimProd I
      if js.size = 1 then
        return js ++ is
      else
        return #[← `(dimSpec| [$js,*])] ++ is
    | `($I)          => return #[⟨I.raw⟩]


@[app_unexpander DataArrayN]
def unexpandDataArrayN : Lean.PrettyPrinter.Unexpander
  | `($(_) $X $I) => do
    let dims ← parseDimProd I
    `($X^[$dims,*])
  | _  => throw ()
