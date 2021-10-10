import SciLean.Prelude

def List.product {α} [Mul α] [Inhabited α] (l : List α) : α := 
  match l with
    | nil => arbitrary
    | head::tail => head * tail.product

structure NDVector (dims : List Nat) where
  (data : FloatArray)
  (h_size : data.size = dims.product)

namespace NDVector

  variable {dims : List Nat}

  @[inline]
  def rank (v : NDVector dims) : Nat := dims.length

  @[inline]
  def dim (v : NDVector dims) (i : Nat) : Nat := dims.get! i

  @[inline]
  def size (v : NDVector dims) : Nat := dims.product
  
  -- get using linear index
  def lget! (v : NDVector dims) (i : Nat) : ℝ := v.data.get! i

  -- get using linear index
  def lset! (v : NDVector dims) (i : Nat) (val : ℝ) : NDVector dims := ⟨v.data.set! i val, sorry⟩

  def map (f : ℝ → ℝ) (v : NDVector dims) : NDVector dims := 
  do
    let mut v := v
    for i in [0:v.size] do
      let val := v.lget! i
      v := v.lset! i (f val)
    v

  def map₂ (f : ℝ → ℝ → ℝ) (u v : NDVector dims) : NDVector dims := 
  do
    let mut u := u
    for i in [0:v.size] do
      let val₁ := u.lget! i
      let val₂ := v.lget! i
      u := u.lset! i (f val₁ val₂)
    u

  def foldl (v : NDVector dims) (f : ℝ → ℝ → ℝ) (init : ℝ) : ℝ :=
  do
    let mut x := init
    for i in [0:v.size] do
      x := f x (v.lget! i)
    x
  
  section Operations
    
    instance : Add (NDVector dims) := ⟨λ u v => map₂ (λ x y => x + y) u v⟩
    instance : Sub (NDVector dims) := ⟨λ u v => map₂ (λ x y => x - y) u v⟩

    instance : HMul ℝ (NDVector dims) (NDVector dims) := ⟨λ r v => map (λ x => r * x) v⟩

    instance : Neg (NDVector dims) := ⟨λ v => map (λ x => -x) v⟩

    -- This is slow as it creates intermediary (Array Float)
    instance : Zero (NDVector dims) := ⟨⟨mkArray dims.product 0⟩, (by simp[FloatArray.size])⟩

  end Operations


  section VectorSpace

    instance : Vec (NDVector dims) := 
    {
      add_assoc := sorry,
      add_comm := sorry,
      add_zero := sorry,
      zero_add := sorry
    }

    instance : Inner (NDVector dims) := 
      ⟨λ u v =>
        do
          let mut r : ℝ := 0
          for i in [0:u.size] do
            r := r + (u.lget! i) * (v.lget! i)
          r⟩

    instance : Hilbert (NDVector dims) := 
    {
      inner_symm := sorry,
      inner_pos := sorry,
      inner_add := sorry,
      inner_mul := sorry
    }

  end VectorSpace


  section FunctionProps

    -- Linear Get
    instance : IsLin (lget! : NDVector dims → Nat → ℝ) := sorry

    -- Linear Set
    instance : IsDiff (lset! : NDVector dims → Nat → ℝ → NDVector dims) := sorry
    instance (v : NDVector dims) (i : Nat) : IsDiff (lset! v i : ℝ → NDVector dims) := sorry
  
    @[simp]
    def lset_differential_1 (v dv : NDVector dims) (i : Nat) (x : ℝ) : δ lset! v dv i x = lset! dv i 0 := sorry

    @[simp]
    def lset_differential_2 (v : NDVector dims) (i : Nat) (x dx : ℝ) : δ (lset! v i) x dx = lset! 0 i dx := sorry

    -- Map
    instance : IsLin (map : (ℝ → ℝ) → NDVector dims → NDVector dims) := sorry
    instance (f : ℝ → ℝ) [IsDiff f] : IsDiff (map f : NDVector dims → NDVector dims) := sorry

    @[simp]
    def map_differential_2 (f : ℝ → ℝ) [IsDiff f] (v dv : NDVector dims) : δ (map f) v dv = map₂ (δ f) v dv := sorry

    


  end FunctionProps
    
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
