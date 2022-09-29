import SciLean.Prelude

namespace SciLean

opaque ByteData : Type := ByteArray

-- Number of bytes
opaque ByteData.size (d : ByteData) : Nat := 
  let d : ByteArray := cast sorry_proof d
  d.size

inductive BitSize where | oneBit | twoBits | fourBits | bytes (n : Nat) 
deriving Inhabited

inductive BitSize' where | bits (n : Nat) (h : n < 8) | bytes (n : Nat)
deriving Inhabited


def ByteData.InBounds (d : ByteData) (i : Nat) (s : BitSize) : Prop :=
match s with
| .oneBit   => i < 8*d.size
| .twoBits  => i < 4*d.size
| .fourBits => i < 2*d.size
| .bytes n  => n*i < d.size

/-- At least `i` elements of size `s` fit into `a` -/
def BitSize'.InBounds (s : SciLean.BitSize') (a : ByteArray) (i : Nat)  : Prop :=
match s with
| .bits n _ => i < 8/n * a.size
| .bytes n  => n*i < a.size

class ByteType (α : Type) where
  size : BitSize
  get (d : ByteData) (i : Nat) (h : d.InBounds i size) : α
  set (d : ByteData) (i : Nat) (h : d.InBounds i size) (a : α) : ByteData

class PlainDataType (α : Type) where
  size : BitSize'
  get (d : ByteArray) (i : Nat) (h : size.InBounds d i) : α
  set (d : ByteArray) (i : Nat) (h : size.InBounds d i) (a : α) : ByteArray

  -- get_set       -- setting and getting returns the original
  -- get_set_other -- set does not affects other elements
  -- size_set      -- does not changes ByteData size
  -- ext           -- extensionality of ByteData i.e. if ∀ i h h', get d i h = get d' i h' → d = d'

/- How many bytes are needed to hold n elements of type α -/
def ByteType.bytes {α : Type} (_ : ByteType α) (n : Nat) : Nat :=
  match ByteType.size α with
  | .oneBit => (n + 7) / 8 
  | .twoBits => (n + 3) / 4
  | .fourBits => (n + 1) / 2
  | .bytes m => m * n

/- How many bytes are needed to hold n elements of type α -/
def PlainDataType.bytes {α : Type} (pd : PlainDataType α) (n : Nat) : Nat :=
  match pd.size with
  | .bits m _ => (n + ((8/m) - 1)) / (8/m) 
  | .bytes m => m * n


