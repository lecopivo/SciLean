import SciLean.Prelude

-- @[reducible]
def List.product {α} [Mul α] [Inhabited α] (l : List α) : α := 
  match l with
    | nil => arbitrary
    | head::tail => head * tail.product

structure NDVector (dims : List Nat) where
  (data : FloatArray)
  (h_size : data.size = dims.product)

namespace NDVector

  variable {dims : List Nat}

  abbrev N := dims.product

  @[inline]
  def rank (v : NDVector dims) : Nat := dims.length

  @[inline]
  def dim (v : NDVector dims) (i : Nat) : Nat := dims.get! i

  @[inline]
  def size (v : NDVector dims) : Nat := dims.product

  -- linear index make
  def lmk (f : (Fin dims.product) → ℝ) : NDVector dims := ⟨⟨(mkArray dims.product 0).mapIdx (λ i _ => f ⟨i.1, sorry⟩)⟩, sorry⟩

  -- get using linear index
  def lget! (v : NDVector dims) (i : Nat) : ℝ := v.data.get! i
  def lget (v : NDVector dims) (i : Fin dims.product) : ℝ := v.data.get ⟨i.1, by rw [v.h_size]; apply i.2; done⟩ 

  -- set using linear index
  def lset! (v : NDVector dims) (i : Nat) (val : ℝ) : NDVector dims := ⟨v.data.set! i val, sorry⟩

  -- set using linear index
  def lset (v : NDVector dims) (i : Fin dims.product) (val : ℝ) : NDVector dims := ⟨v.data.set ⟨i.1, by rw [v.h_size]; apply i.2; done⟩ val, sorry⟩

  -- TODO: @[extern ndvector_map]  -  is it worth it? 
  def mapIdx (f : Nat → ℝ → ℝ) (v : NDVector dims) : NDVector dims := 
  do
    let mut v := v
    for i in [0:v.size] do
      let val := v.lget! i
      v := v.lset! i (f i val)
    v

  def map (f : ℝ → ℝ) (v : NDVector dims) : NDVector dims := mapIdx (λ i => f) v

  -- This should have specialized implementation in C to handle reference counting in the most efficient way
  -- i.e. modify `v` in place if possible
  -- if `u` and `v` are the same, and ref counter is 2 then you can modify it in place too.
  -- TODO: @[extern ndvector_map2]
  def map₂ (f : ℝ → ℝ → ℝ) (u v : NDVector dims) : NDVector dims := mapIdx (λ i ui => f ui (v.lget! i)) u

  def foldIdx {n : Nat} {α} (f : Fin n → α → α) (a₀ : α) : α :=
  do
    let mut a := a₀
    for i in [0:n] do
      a := (f ⟨i, sorry⟩ a)
    a
  
  def foldlIdx (f : Nat → ℝ → ℝ → ℝ) (v : NDVector dims) (init : ℝ) : ℝ :=
    let F : Fin v.size → ℝ → ℝ := λ i y => f i y (v.lget! i)
    foldIdx F init

  def foldl (f : ℝ → ℝ → ℝ) (v : NDVector dims) (init : ℝ) : ℝ := foldlIdx (λ i => f) v init
  
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


  section FunctionProperties

    -- Linear Get
    instance : IsLin (lget! : NDVector dims → Nat → ℝ) := sorry
    instance : IsLin (lget : NDVector dims → Fin dims.product → ℝ) := sorry

    @[simp] def lget_adjoint : adjoint (lget : NDVector dims → Fin dims.product → ℝ) = lmk := sorry

    -- Linear Set
    instance : IsDiff (lset! : NDVector dims → Nat → ℝ → NDVector dims) := sorry
    instance (v : NDVector dims) (i : Nat) : IsDiff (lset! v i : ℝ → NDVector dims) := sorry

    instance : IsDiff (lset : NDVector dims → Fin dims.product → ℝ → NDVector dims) := sorry
    instance (v : NDVector dims) (i : Fin dims.product) : IsDiff (lset v i : ℝ → NDVector dims) := sorry
  
    @[simp]
    def lset!_differential_1 (v dv : NDVector dims) (i : Nat) (x : ℝ) : δ lset! v dv i x = lset! dv i 0 := sorry

    @[simp]
    def lset!_differential_2 (v : NDVector dims) (i : Nat) (x dx : ℝ) : δ (lset! v i) x dx = lset! 0 i dx := sorry

    @[simp]
    def lset_differential_1 (v dv : NDVector dims) (i : Fin dims.product) (x : ℝ) : δ lset v dv i x = lset! dv i 0 := sorry

    @[simp]
    def lset_differential_2 (v : NDVector dims) (i : Fin dims.product) (x dx : ℝ) : δ (lset v i) x dx = lset! 0 i dx := sorry

    -- Map
    instance : IsLin (map : (ℝ → ℝ) → NDVector dims → NDVector dims) := sorry
    instance (f : ℝ → ℝ) [IsDiff f] : IsDiff (map f : NDVector dims → NDVector dims) := sorry

    @[simp]
    def map_differential_2 (f : ℝ → ℝ) [IsDiff f] (v dv : NDVector dims) : δ (map f) v dv = map₂ (δ f) v dv := sorry

    -- Map₂
    instance : IsLin (map₂ : (ℝ → ℝ → ℝ) → NDVector dims → NDVector dims → NDVector dims) := sorry
    instance (f : ℝ → ℝ → ℝ) [IsDiff f] : IsDiff (map₂ f : NDVector dims → NDVector dims → NDVector dims) := sorry
    instance (f : ℝ → ℝ → ℝ) [∀ x, IsDiff (f x)] : IsDiff (map₂ f u : NDVector dims → NDVector dims) := sorry
      
    @[simp] 
    def map2_differential_2 (f : ℝ → ℝ → ℝ) (u du v : NDVector dims) [IsDiff f] 
      : δ (map₂ f) u du v = mapIdx (λ i ui => δ f ui (du.lget! i) (v.lget! i)) u := sorry

    @[simp] 
    def map2_differential_3 (f : ℝ → ℝ → ℝ) (u v dv : NDVector dims) [∀ x, IsDiff (f x)] 
      : δ (map₂ f) u v dv = mapIdx (λ i vi => δ (f (u.lget! i)) vi (dv.lget! i)) v := sorry
    
    -- FoldlIdx
    -- once morphisms are in place
    -- instance : IsDiff ((comp foldlIdx coe) : (Nat → ℝ ⟿ ℝ → ℝ) → NDVector dims → ℝ → ℝ) := sorry
    instance (f : Nat → ℝ → ℝ → ℝ) [∀ i, IsDiff (f i)] [∀ i y, IsDiff (f i y)] : IsDiff (foldlIdx f : NDVector dims → ℝ → ℝ) := sorry
    instance (f : Nat → ℝ → ℝ → ℝ) [∀ i, IsDiff (f i)] (v : NDVector dims) : IsDiff (foldlIdx f v : ℝ → ℝ) := sorry

    @[simp]
    def foldlIdx_differential_1 (f df : Nat → ℝ → ℝ → ℝ) [∀ i, IsDiff (f i)] (v : NDVector dims) (init : ℝ) 
      : δ foldlIdx f df v init
        =
        (let F := 
           λ (i : Fin v.size) (ydy : ℝ × ℝ) => 
             let y := ydy.1
             let dy := ydy.2
             let vi := v.lget! i
             (f i y vi, δ (f i) y dy vi + df i y vi)
         (foldIdx F (init, 0)).2) := sorry

    @[simp]
    def foldlIdx_differential_2 (f : Nat → ℝ → ℝ → ℝ) [∀ i, IsDiff (f i)] [∀ i y, IsDiff (f i y)] (v dv : NDVector dims) (init : ℝ) 
      : δ (foldlIdx f) v dv init
        =
        (let F := 
           λ (i : Fin v.size) (ydy : ℝ × ℝ) => 
             let y := ydy.1
             let dy := ydy.2
             let vi := v.lget! i
             let dvi := dv.lget! i
             (f i y vi, δ (f i) y dy vi + δ (f i y) vi dvi)
         (foldIdx F (init, 0)).2) := sorry

    @[simp]
    def foldlIdx_differential_3 (f : Nat → ℝ → ℝ → ℝ) [∀ i, IsDiff (f i)] (v: NDVector dims) (init dinit : ℝ) 
      : δ (foldlIdx f v) init dinit
        =
        (let F := 
           λ (i : Fin v.size) (ydy : ℝ × ℝ) => 
             let y := ydy.1
             let dy := ydy.2
             let vi := v.lget! i
             (f i y vi, δ (f i) y dy vi)
         (foldIdx F (init, dinit)).2) := sorry

  end FunctionProperties
    
  --  def getVec2 (v : NDVector [2, n]) (i : Nat) : Vec2 := 
  --  def getVec3 (v : NDVector [3, n]) (i : Nat) : Vec3 := 
  --  def getVec4 (v : NDVector [4, n]) (i : Nat) : Vec4 := 

  --  def getMat2 (v : NDVector [2, 2, n]) (i : Nat) : Mat2 := 
  --  def getMat3 (v : NDVector [3, 3, n]) (i : Nat) : Mat3 := 
  --  def getMat4 (v : NDVector [4, 4, n]) (i : Nat) : Mat4 := 

end NDVector

abbrev Vector (n : Nat) := NDVector [n]
abbrev Matrix (n m : Nat) := NDVector [n, m]
