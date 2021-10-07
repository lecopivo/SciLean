import SciLean.Prelude

def List.product {α} [Mul α] [Inhabited α] (l : List α) : α := 
  match l with
    | nil => arbitrary
    | head::tail => head * tail.product

structure NDVector (dims : List Nat) where
  (data : FloatArray)
  (h_size : data.size = dims.product)

namespace NDVector

  variable (dims : List Nat)

  def rank (v : NDVector dims) : Nat := dims.length

  def dim (v : NDVector dims) (i : Nat) : Nat := dims.get! i

  -- get using linear index
  def lget! (v : NDVector dims) (i : Nat) : ℝ := v.data.get! i

  -- get using linear index
  def lset! (v : NDVector dims) (i : Nat) (val : ℝ) : NDVector dims := ⟨v.data.set! i val, sorry⟩

  --  map 
  --  map₂ -- this might require specialized C implementation to handle reference conting properly

  --  def getVec2 (v : NDVector [2, n]) (i : Nat) : Vec2 := 
  --  def getVec3 (v : NDVector [3, n]) (i : Nat) : Vec3 := 
  --  def getVec4 (v : NDVector [4, n]) (i : Nat) : Vec4 := 

  --  def getMat2 (v : NDVector [2, 2, n]) (i : Nat) : Mat2 := 
  --  def getMat3 (v : NDVector [3, 3, n]) (i : Nat) : Mat3 := 
  --  def getMat4 (v : NDVector [4, 4, n]) (i : Nat) : Mat4 := 

end NDVector

abbrev Vector (n : Nat) := NDVector [n]
abbrev Matrix (n m : Nat) := NDVector [n, m]
