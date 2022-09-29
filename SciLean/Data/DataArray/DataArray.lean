import SciLean.Data.DataArray.ByteType


namespace SciLean

-- TODO: make opaque or make it quotient - we have redundant trailing bits
structure DataArray (α : Type) [bt : ByteType α] where
  data : ByteData
  size : Nat 
  h_size : bt.bytes size ≤ data.size


variable {α : Type} [bt : ByteType α]

def DataArray.get (a : DataArray α) (i : Fin a.size) : α := ByteType.get a.data i sorry_proof
def DataArray.set (a : DataArray α) (i : Fin a.size) (val : α) : DataArray α := ⟨ByteType.set a.data i sorry_proof val, a.size, sorry_proof⟩

-- Extensionality -- currently this is inconsistent. We should either make DataArray opaque or Quotient it out by trailing bit values
theorem DataArray.ext (d d' : DataArray α) : (h : d.size = d'.size) → (∀ i, d.get i = d'.get (h ▸ i)) → d = d' := sorry_proof

def DataArray.intro (f : Fin n → α) : DataArray α := Id.run do
  let bytes := (bt.bytes n)
  let mut d : ByteArray := ByteArray.mkEmpty bytes
  for _ in [0:bytes] do
    d := d.push 0
  let mut d' : DataArray α := ⟨cast sorry_proof d, n, sorry_proof⟩
  for i in [0:n] do
    d' := d'.set ⟨i,sorry_proof⟩ (f ⟨i,sorry_proof⟩)
  d'

instance [ByteType α] [ToString α] : ToString (DataArray α) := ⟨λ a => Id.run do
  if a.size = 0 then
    return "[]"
  else 
    let mut s : String := s!"[{a.get ⟨0,sorry_proof⟩}"
    for i in [1:a.size] do
      s := s ++ s!", {a.get ⟨i,sorry_proof⟩}"
    s ++ "]"⟩
