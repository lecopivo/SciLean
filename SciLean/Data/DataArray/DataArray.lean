import SciLean.Data.DataArray.PlainDataType
import SciLean.Data.PowType

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



/-- Extensionality of DataArray

Currently this is inconsistent, we need to turn DataArray into quotient!
-/
theorem DataArray.ext (d d' : DataArray α) : (h : d.size = d'.size) → (∀ i, d.get i = d'.get (h ▸ i)) → d = d' := sorry_proof

def DataArray.intro (f : Fin n → α) : DataArray α := Id.run do
  let bytes := (pd.bytes n)
  let mut d : ByteArray := ByteArray.mkEmpty bytes
  for _ in [0:bytes] do
    d := d.push 0
  let mut d' : DataArray α := ⟨cast sorry_proof d, n, sorry_proof⟩
  for i in [0:n] do
    d' := d'.set ⟨i,sorry_proof⟩ (f ⟨i,sorry_proof⟩)
  d'

def DataArray.intro' (f : ι → α) : DataArray α := Id.run do
  let bytes := (pd.bytes (numOf ι))
  let mut d : ByteArray := ByteArray.mkEmpty bytes
  for _ in [0:bytes] do
    d := d.push 0
  let mut d' : DataArray α := ⟨cast sorry_proof d, (numOf ι), sorry_proof⟩
  for (i,li) in Enumtype.fullRange ι do
    d' := d'.set ⟨li,sorry_proof⟩ (f i)
  d'

instance [PlainDataType α] [ToString α] : ToString (DataArray α) := ⟨λ a => Id.run do
  if a.size = 0 then
    return "[]"
  else 
    let mut s : String := s!"[{a.get ⟨0,sorry_proof⟩}"
    for i in [1:a.size] do
      s := s ++ s!", {a.get ⟨i,sorry_proof⟩}"
    s ++ "]"⟩

structure DataArrayN (α : Type) (n : Nat) [pd : PlainDataType α] where
  data : DataArray α
  h_size : n = data.size

instance (n) : GetElem (DataArrayN α n) (Fin n) α (λ _ _ => True) where
  getElem xs i _ := xs.1.get (xs.2 ▸ i)

instance : GetElem (DataArrayN α (numOf ι)) (ι) α (λ _ _ => True) where
  getElem xs i _ := xs.1.get (xs.2 ▸ toFin i)

instance : SetElem (DataArrayN α n) (Fin n) α where
  setElem xs i xi := ⟨xs.1.set (xs.2 ▸ i) xi, sorry_proof⟩

instance : SetElem (DataArrayN α (numOf ι)) ι α where
  setElem xs i xi := ⟨xs.1.set (xs.2 ▸ toFin i) xi, sorry_proof⟩

instance : FunType (DataArrayN α n) (Fin n) α  where
  ext := sorry_proof

instance : FunType (DataArrayN α (numOf ι)) ι α  where
  ext := sorry_proof

instance : FunType.HasSet (DataArrayN α n) where
    toFun_set_eq  := sorry_proof
    toFun_set_neq := sorry_proof

instance : FunType.HasSet (DataArrayN α (numOf ι)) where
    toFun_set_eq  := sorry_proof
    toFun_set_neq := sorry_proof

instance : FunType.HasIntro (DataArrayN α n) where
    intro f := ⟨DataArray.intro f, sorry_proof⟩
    toFun_intro := sorry_proof

instance : FunType.HasIntro (DataArrayN α (numOf ι)) where
    intro f := ⟨DataArray.intro' f, sorry_proof⟩
    toFun_intro := sorry_proof

instance : PowType (DataArrayN α (numOf ι)) ι α := ⟨⟩

#check ℝ^(Fin 3)

#eval ((λ [i] => i.1.toReal ) : ℝ^(Fin 100)) |>.map Math.sqrt

#eval ((λ [i] => i) : (Fin 3 × Fin 5)^(Fin 3 × Fin 5))
#eval ((λ [i] => i) : (Fin 3 × Fin 5)^(Fin 3 × Fin 5)).data
#eval ((λ [i] => i) : (Fin 3 × Fin 5)^(Fin 3 × Fin 5)).data.byteData

#eval (1,2,3,4)

#eval ((λ [i] => i) : (Fin 3 × Fin 2 × Fin 2)^(Fin 3 × Fin 2 × Fin 2))
#eval ((λ [i] => i) : (Fin 3 × Fin 2 × Fin 2)^(Fin 3 × Fin 2 × Fin 2)).data
#eval ((λ [i] => i) : (Fin 3 × Fin 2 × Fin 2)^(Fin 3 × Fin 2 × Fin 2)).data.byteData

#eval ((λ [i] => (i.1.toFloat, i.1.toFloat.sqrt)) : (Float × Float)^(Fin 17))

#check Id.run do
  let mut a : ℝ^{10} := λ [i] => i.1
  for (i,_) in Enumtype.fullRange a.Index do
    a[i] *= 1000
    a[i] += Math.sqrt i.1 + a[i]
  a

#eval Id.run do
  let mut a : (ℝ×ℝ)^{3,3} := λ [i,j] => (i.1,j.1)
  for (i,li) in Enumtype.fullRange a.Index do
    a[li] := (Math.sqrt a[li].1, Math.exp a[li].2)
  a
