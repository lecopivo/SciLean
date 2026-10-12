module

public import SciLean.Data.DataArray.DataArray
public import SciLean.Data.DataArray.DataArrayEquiv
public import SciLean.Data.DataArray.Float
public import SciLean.Data.Instances.Sigma

public import SciLean.Tactic.SimpleProxyType
public import SciLean.Tactic.LSimp
public import Mathlib.Data.Fintype.Sum

@[expose] public section


namespace SciLean

/-- Case analysis on `Idx 2`. -/
theorem idx2_cases (i : Idx 2) : i = 0 ∨ i = 1 := by
  have hn : (2:ℕ) < USize.size := usize_size_gt 2 (by omega)
  have h : i.1.toNat < 2 := i.2
  by_cases h0 : i.1.toNat = 0
  · exact .inl (Idx.eq_of_toNat 0 (by omega) hn h0)
  · exact .inr (Idx.eq_of_toNat 1 (by omega) hn (by omega))

/-- Case analysis on `Idx 3`. -/
theorem idx3_cases (i : Idx 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have hn : (3:ℕ) < USize.size := usize_size_gt 3 (by omega)
  have h : i.1.toNat < 3 := i.2
  by_cases h0 : i.1.toNat = 0
  · exact .inl (Idx.eq_of_toNat 0 (by omega) hn h0)
  · by_cases h1 : i.1.toNat = 1
    · exact .inr (.inl (Idx.eq_of_toNat 1 (by omega) hn h1))
    · exact .inr (.inr (Idx.eq_of_toNat 2 (by omega) hn (by omega)))

/-- Case analysis on `Idx 4`. -/
theorem idx4_cases (i : Idx 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hn : (4:ℕ) < USize.size := usize_size_gt 4 (by omega)
  have h : i.1.toNat < 4 := i.2
  by_cases h0 : i.1.toNat = 0
  · exact .inl (Idx.eq_of_toNat 0 (by omega) hn h0)
  · by_cases h1 : i.1.toNat = 1
    · exact .inr (.inl (Idx.eq_of_toNat 1 (by omega) hn h1))
    · by_cases h2 : i.1.toNat = 2
      · exact .inr (.inr (.inl (Idx.eq_of_toNat 2 (by omega) hn h2)))
      · exact .inr (.inr (.inr (Idx.eq_of_toNat 3 (by omega) hn (by omega))))

/-- The value of the numeral `k : Idx n` is `k`. -/
theorem idx_toNat_lit {n : ℕ} [NeZero n] (k : ℕ) (hk : k < n) (hn : n < 4294967296 := by omega) :
    ((OfNat.ofNat k : Idx n) : USize).toNat = k :=
  Idx.toNat_ofNat k hk (usize_size_gt n hn)

/-- Numerals `0,1 : Idx 2` are distinct. -/
theorem idx2_ne : (1 : Idx 2) ≠ 0 := Idx.ofNat_ne_ofNat 1 0

/-- Numerals `0,1,2 : Idx 3` are pairwise distinct. -/
theorem idx3_ne : (1 : Idx 3) ≠ 0 ∧ (2 : Idx 3) ≠ 0 ∧ (2 : Idx 3) ≠ 1 :=
  ⟨Idx.ofNat_ne_ofNat 1 0, Idx.ofNat_ne_ofNat 2 0, Idx.ofNat_ne_ofNat 2 1⟩

/-- Numerals `0,1,2,3 : Idx 4` are pairwise distinct. -/
theorem idx4_ne : (1 : Idx 4) ≠ 0 ∧ (2 : Idx 4) ≠ 0 ∧ (2 : Idx 4) ≠ 1 ∧
    (3 : Idx 4) ≠ 0 ∧ (3 : Idx 4) ≠ 1 ∧ (3 : Idx 4) ≠ 2 :=
  ⟨Idx.ofNat_ne_ofNat 1 0, Idx.ofNat_ne_ofNat 2 0, Idx.ofNat_ne_ofNat 2 1,
   Idx.ofNat_ne_ofNat 3 0, Idx.ofNat_ne_ofNat 3 1, Idx.ofNat_ne_ofNat 3 2⟩

structure Float2 where
  (x y : Float)
  deriving Inhabited

namespace Float2

  instance : ToString Float2 where
    toString v := s!"⊞[{v.x}, {v.y}]"

  instance : Size Float2 where
    size := 2

  inductive Index | x | y

  instance : Fintype Index := Fintype.ofEquiv _ (simple_proxy_equiv% Index)
  instance : IndexType Index 2 := IndexType.ofEquiv _ (simple_proxy_equiv% Index)

  -- Array Operations with `Index` ---
  instance : GetElem' Float2 Index Float where
    getElem v i _ :=
      match i with
      | .x => v.x
      | .y => v.y

  instance : InjectiveGetElem Float2 (Index) where
    getElem_injective := by
      rintro ⟨x,y⟩ ⟨x',y'⟩ h
      have := congrFun h .x
      have := congrFun h .y
      simp_all [getElem]

  instance : SetElem' Float2 (Index) Float where
    setElem v i vi _ :=
      match i with
      | .x => ⟨vi, v.y⟩
      | .y => ⟨v.x, vi⟩
    setElem_valid := by simp

  instance : LawfulSetElem Float2 Index where
    getElem_setElem_eq := by rintro v (_|_) x _ <;> rfl
    getElem_setElem_neq := by
      rintro v (_|_) (_|_) x _ _ hij <;> first | rfl | exact absurd rfl hij

  instance : OfFn Float2 (Index) Float where
    ofFn f := ⟨f .x, f .y⟩

  instance : LawfulOfFn Float2 (Index) where
    getElem_ofFn := by intro f i; cases i <;> rfl

  /-- The index `Index.x` is the zeroth linear index. -/
  theorem toIdx_index_x : (toIdx Index.x) = (0 : Idx 2) := by decide

  /-- The index `Index.y` is the first linear index. -/
  theorem toIdx_index_y : (toIdx Index.y) = (1 : Idx 2) := by
    apply Idx.eq_of_toNat 1 (by omega) (usize_size_gt 2 (by omega))
    have h2 : (1:ℕ) < 2 ^ System.Platform.numBits := usize_size_gt 1 (by omega)
    simp [IndexType.toIdx,
      show (Index.simpleProxyTypeEquiv.symm Index.y) = Sum.inr () from rfl,
      idx_toNat_lit (n:=1) 0 (by omega), Nat.mod_eq_of_lt h2]

  theorem getElem_reshape_index_x (x y : Float) :
      (⊞[x, y].reshape Index (by decide))[Index.x] = x := by
    have h1 : (⊞[x, y] : Float^[Idx 2])[(0 : Idx 2)] = x := by
      simp [Idx.toFin, idx_toNat_lit (n:=2) 0 (by omega)]
    simp [DataArrayN.reshape, getElem, DataArrayN.get, toIdx_index_x] at h1 ⊢
    exact h1

  theorem getElem_reshape_index_y (x y : Float) :
      (⊞[x, y].reshape Index (by decide))[Index.y] = y := by
    have h1 : (⊞[x, y] : Float^[Idx 2])[(1 : Idx 2)] = y := by
      simp [Idx.toFin, idx_toNat_lit (n:=2) 1 (by omega)]
    simp [DataArrayN.reshape, getElem, DataArrayN.get, toIdx_index_y] at h1 ⊢
    exact h1

 instance : DataArrayEquiv Float2 Index Float where
    toKn := fun v => ⊞[v.x, v.y] |>.reshape Index (by decide)
    fromKn := fun v => ⟨v[.x], v[.y]⟩
    left_inv := by
      rintro ⟨x,y⟩
      simp only [getElem_reshape_index_x, getElem_reshape_index_y]
    right_inv := by
      intro u
      apply getElem_injective (idx := Index)
      funext i
      cases i <;> simp only [getElem_reshape_index_x, getElem_reshape_index_y]

  -- Array Operations with `Idx 2` ---
  instance : GetElem' Float2 (Idx 2) Float where
    getElem v i _ := if i = 0 then v.x else v.y

  instance : DefaultIndex Float2 (Idx 2) where
  instance : DefaultIndexOfRank Float2 1 (Idx 2) where

  instance : InjectiveGetElem Float2 (Idx 2) where
    getElem_injective := by
      have h10 := idx2_ne
      rintro ⟨x,y⟩ ⟨x',y'⟩ h
      have := congrFun h 0
      have := congrFun h 1
      simp_all [getElem]

  instance : SetElem' Float2 (Idx 2) Float where
    setElem v i vi _ := if i = 0 then ⟨vi, v.y⟩ else ⟨v.x, vi⟩
    setElem_valid := by simp

  instance : LawfulSetElem Float2 (Idx 2) where
    getElem_setElem_eq := by
      have h10 := idx2_ne
      intro v i x _
      rcases idx2_cases i with rfl | rfl <;> simp [getElem, setElem, h10]
    getElem_setElem_neq := by
      have h10 := idx2_ne
      intro v i j x _ _ hij
      rcases idx2_cases i with rfl | rfl <;> rcases idx2_cases j with rfl | rfl <;>
        simp_all [getElem, setElem]

  instance : OfFn Float2 (Idx 2) Float where
    ofFn f := ⟨f 0, f 1⟩

  instance : LawfulOfFn Float2 (Idx 2) where
    getElem_ofFn := by
      have h10 := idx2_ne
      intro f i
      rcases idx2_cases i with rfl | rfl <;> simp [getElem, ofFn, h10]

  instance : DataArrayEquiv Float2 (Idx 2) Float where
    toKn := fun v => ⊞[v.x, v.y]
    fromKn := fun v => ⟨v[0], v[1]⟩
    left_inv := by
      intro v
      simp [Idx.toFin, idx_toNat_lit (n:=2) 0 (by omega), idx_toNat_lit (n:=2) 1 (by omega)]
    right_inv := by
      intro u
      apply getElem_injective (idx := Idx 2)
      funext i
      rcases idx2_cases i with rfl | rfl <;>
        simp [Idx.toFin, idx_toNat_lit (n:=2) 0 (by omega), idx_toNat_lit (n:=2) 1 (by omega)]


  -- Byte Level Operations
  -- todo: this should be derived from `PlainDataType.ofEquiv`
  instance : PlainDataType Float2 := (PlainDataType.ofEquiv (simple_proxy_equiv% Float2))
    rewrite_by
      lsimp[Float2.simpleProxyTypeEquiv,PlainDataType.ofEquiv,Prod.byteTypeProd]

  --- Default Operations
  -- we prefer indexing `Float2` by `Float2.Index`
  instance : DefaultIndex Float2 Index where
  instance : DefaultIndexOfRank Float2 1 Index where
  instance {I n} [IndexType I n] : HasRnEquiv (Float2^[I]) (I × Index) Float where

  instance : Add Float2 := Add.ofEquiv (proxy_equiv% Float2)
  instance : Sub Float2 := Sub.ofEquiv (proxy_equiv% Float2)
  instance : Neg Float2 := Neg.ofEquiv (proxy_equiv% Float2)
  instance : Mul Float2 := Mul.ofEquiv (proxy_equiv% Float2)
  instance : Div Float2 := Div.ofEquiv (proxy_equiv% Float2)
  instance : SMul Float Float2 := SMul.ofEquiv Float (proxy_equiv% Float2)
  instance : Zero Float2 := Zero.ofEquiv (proxy_equiv% Float2)
  instance : Norm Float2 := Norm.ofEquiv (proxy_equiv% Float2)
  instance : Inner Float Float2 := Inner.ofEquiv (R:=Float) (proxy_equiv% Float2)

  instance : AddCommGroup Float2 := AddCommGroup.ofEquiv (proxy_equiv% Float2)
  instance : Module Float Float2 := Module.ofEquiv (proxy_equiv% Float2)

  instance : MetricSpace Float2 := MetricSpace.ofEquiv (proxy_equiv% Float2)
  instance : NormedAddCommGroup Float2 := NormedAddCommGroup.ofEquiv (proxy_equiv% Float2)
  instance : NormedSpace Float Float2 := NormedSpace.ofEquiv' (proxy_equiv% Float2)
  instance : AdjointSpace Float Float2 := AdjointSpace.ofEquiv (proxy_equiv% Float2)

end Float2


structure Float3 where
  (x y z : Float)
  deriving Inhabited

namespace Float3

  instance : ToString Float3 where
    toString v := s!"⊞[{v.x}, {v.y}, {v.z}]"

  instance : Size Float3 where
    size := 3

  instance : GetElem' Float3 (Idx 3) Float where
    getElem v i _ := if i = 0 then v.x else if i = 1 then v.y else v.z

  instance : DefaultIndex Float3 (Idx 3) where
  instance : DefaultIndexOfRank Float3 1 (Idx 3) where

  instance : InjectiveGetElem Float3 (Idx 3) where
    getElem_injective := by
      obtain ⟨h10,h20,h21⟩ := idx3_ne
      rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ h
      have := congrFun h 0
      have := congrFun h 1
      have := congrFun h 2
      simp_all [getElem]

  instance : SetElem' Float3 (Idx 3) Float where
    setElem v i vi _ := if i = 0 then ⟨vi, v.y, v.z⟩ else if i = 1 then ⟨v.x, vi, v.z⟩ else ⟨v.x, v.y, vi⟩
    setElem_valid := by simp

  instance : LawfulSetElem Float3 (Idx 3) where
    getElem_setElem_eq := by
      obtain ⟨h10,h20,h21⟩ := idx3_ne
      intro v i x _
      rcases idx3_cases i with rfl | rfl | rfl <;> simp [getElem, setElem, h10, h20, h21]
    getElem_setElem_neq := by
      obtain ⟨h10,h20,h21⟩ := idx3_ne
      intro v i j x _ _ hij
      rcases idx3_cases i with rfl | rfl | rfl <;> rcases idx3_cases j with rfl | rfl | rfl <;>
        simp_all [getElem, setElem]

  instance : OfFn Float3 (Idx 3) Float where
    ofFn f := ⟨f 0, f 1, f 2⟩

  instance : LawfulOfFn Float3 (Idx 3) where
    getElem_ofFn := by
      obtain ⟨h10,h20,h21⟩ := idx3_ne
      intro f i
      rcases idx3_cases i with rfl | rfl | rfl <;> simp [getElem, ofFn, h10, h20, h21]

  instance : PlainDataType Float3 where
    btype := {
      bytes := 24
      h_size := by rw [USize.lt_iff_toNat_lt]; simp
      fromByteArray b i _ :=
        let b := b.toFloatArray sorry_proof
        let x := b.get (i/8).toNat sorry_proof
        let y := b.get (i/8 + 1).toNat sorry_proof
        let z := b.get (i/8 + 2).toNat sorry_proof
        ⟨x,y,z⟩
      toByteArray b i _ v :=
        let b := b.toFloatArray sorry_proof
        let b := b.set (i/8).toNat v.x sorry_proof
        let b := b.set (i/8 + 1).toNat v.y sorry_proof
        let b := b.set (i/8 + 2).toNat v.z sorry_proof
        b.toByteArray
      toByteArray_size := sorry_proof
      fromByteArray_toByteArray := sorry_proof
      fromByteArray_toByteArray_other := sorry_proof
    }

  instance : DataArrayEquiv Float3 (Idx 3) Float where
    toKn := fun v => ⊞[v.x, v.y, v.z]
    fromKn := fun v => ⟨v[0], v[1], v[2]⟩
    left_inv := by
      intro v
      simp [Idx.toFin, idx_toNat_lit (n:=3) 0 (by omega), idx_toNat_lit (n:=3) 1 (by omega),
        idx_toNat_lit (n:=3) 2 (by omega)]
    right_inv := by
      intro u
      apply getElem_injective (idx := Idx 3)
      funext i
      rcases idx3_cases i with rfl | rfl | rfl <;>
        simp [Idx.toFin, idx_toNat_lit (n:=3) 0 (by omega), idx_toNat_lit (n:=3) 1 (by omega),
          idx_toNat_lit (n:=3) 2 (by omega)]

  instance {I n} [IndexType I n] : HasRnEquiv (Float3^[I]) (I × Idx 3) Float where

  instance : Add Float3 := Add.ofEquiv (proxy_equiv% Float3)
  instance : Sub Float3 := Sub.ofEquiv (proxy_equiv% Float3)
  instance : Neg Float3 := Neg.ofEquiv (proxy_equiv% Float3)
  instance : Mul Float3 := Mul.ofEquiv (proxy_equiv% Float3)
  instance : Div Float3 := Div.ofEquiv (proxy_equiv% Float3)
  instance : SMul Float Float3 := SMul.ofEquiv Float (proxy_equiv% Float3)
  instance : Zero Float3 := Zero.ofEquiv (proxy_equiv% Float3)
  instance : Norm Float3 := Norm.ofEquiv (proxy_equiv% Float3)
  instance : Inner Float Float3 := Inner.ofEquiv (R:=Float) (proxy_equiv% Float3)

  instance : AddCommGroup Float3 := AddCommGroup.ofEquiv (proxy_equiv% Float3)
  instance : Module Float Float3 := Module.ofEquiv (proxy_equiv% Float3)

  instance : MetricSpace Float3 := MetricSpace.ofEquiv (proxy_equiv% Float3)
  instance : NormedAddCommGroup Float3 := NormedAddCommGroup.ofEquiv (proxy_equiv% Float3)
  instance : NormedSpace Float Float3 := NormedSpace.ofEquiv' (proxy_equiv% Float3)
  instance : AdjointSpace Float Float3 := AdjointSpace.ofEquiv (proxy_equiv% Float3)

  def cross (u v : Float3) : Float3 :=
    ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩

end Float3


structure Float4 where
  (x y z w : Float)
  deriving Inhabited

namespace Float4

  instance : ToString Float4 where
    toString v := s!"⊞[{v.x}, {v.y}, {v.z}, {v.w}]"

  instance : Size Float4 where
    size := 4

  instance : GetElem' Float4 (Idx 4) Float where
    getElem v i _ := if i = 0 then v.x else if i = 1 then v.y else if i = 2 then v.z else v.w

  instance : DefaultIndex Float4 (Idx 4) where
  instance : DefaultIndexOfRank Float4 1 (Idx 4) where

  instance : InjectiveGetElem Float4 (Idx 4) where
    getElem_injective := by
      obtain ⟨h10,h20,h21,h30,h31,h32⟩ := idx4_ne
      rintro ⟨x,y,z,w⟩ ⟨x',y',z',w'⟩ h
      have := congrFun h 0
      have := congrFun h 1
      have := congrFun h 2
      have := congrFun h 3
      simp_all [getElem]

  instance : SetElem' Float4 (Idx 4) Float where
    setElem v i vi _ :=
      if i = 0 then ⟨vi, v.y, v.z, v.w⟩
      else if i = 1 then ⟨v.x, vi, v.z, v.w⟩
      else if i = 2 then ⟨v.x, v.y, vi, v.w⟩
      else ⟨v.x, v.y, v.z, vi⟩
    setElem_valid := by simp

  instance : LawfulSetElem Float4 (Idx 4) where
    getElem_setElem_eq := by
      obtain ⟨h10,h20,h21,h30,h31,h32⟩ := idx4_ne
      intro v i x _
      rcases idx4_cases i with rfl | rfl | rfl | rfl <;>
        simp [getElem, setElem, h10, h20, h21, h30, h31, h32]
    getElem_setElem_neq := by
      obtain ⟨h10,h20,h21,h30,h31,h32⟩ := idx4_ne
      intro v i j x _ _ hij
      rcases idx4_cases i with rfl | rfl | rfl | rfl <;>
        rcases idx4_cases j with rfl | rfl | rfl | rfl <;>
        simp_all [getElem, setElem]

  instance : OfFn Float4 (Idx 4) Float where
    ofFn f := ⟨f 0, f 1, f 2, f 3⟩

  instance : LawfulOfFn Float4 (Idx 4) where
    getElem_ofFn := by
      obtain ⟨h10,h20,h21,h30,h31,h32⟩ := idx4_ne
      intro f i
      rcases idx4_cases i with rfl | rfl | rfl | rfl <;>
        simp [getElem, ofFn, h10, h20, h21, h30, h31, h32]

  instance : PlainDataType Float4 where
    btype := {
      bytes := 32
      h_size := by rw [USize.lt_iff_toNat_lt]; simp
      fromByteArray b i _ :=
        let b := b.toFloatArray sorry_proof
        let x := b.get (i/8).toNat sorry_proof
        let y := b.get (i/8 + 1).toNat sorry_proof
        let z := b.get (i/8 + 2).toNat sorry_proof
        let w := b.get (i/8 + 3).toNat sorry_proof
        ⟨x,y,z,w⟩
      toByteArray b i _ v :=
        let b := b.toFloatArray sorry_proof
        let b := b.set (i/8).toNat v.x sorry_proof
        let b := b.set (i/8 + 1).toNat v.y sorry_proof
        let b := b.set (i/8 + 2).toNat v.z sorry_proof
        let b := b.set (i/8 + 3).toNat v.w sorry_proof
        b.toByteArray
      toByteArray_size := sorry_proof
      fromByteArray_toByteArray := sorry_proof
      fromByteArray_toByteArray_other := sorry_proof
    }

  instance : DataArrayEquiv Float4 (Idx 4) Float where
    toKn := fun v => ⊞[v.x, v.y, v.z, v.w]
    fromKn := fun v => ⟨v[0], v[1], v[2], v[3]⟩
    left_inv := by
      intro v
      simp [Idx.toFin, idx_toNat_lit (n:=4) 0 (by omega), idx_toNat_lit (n:=4) 1 (by omega),
        idx_toNat_lit (n:=4) 2 (by omega), idx_toNat_lit (n:=4) 3 (by omega)]
    right_inv := by
      intro u
      apply getElem_injective (idx := Idx 4)
      funext i
      rcases idx4_cases i with rfl | rfl | rfl | rfl <;>
        simp [Idx.toFin, idx_toNat_lit (n:=4) 0 (by omega), idx_toNat_lit (n:=4) 1 (by omega),
          idx_toNat_lit (n:=4) 2 (by omega), idx_toNat_lit (n:=4) 3 (by omega)]

  instance {I n} [IndexType I n] : HasRnEquiv (Float4^[I]) (I × Idx 4) Float where

  instance : Add Float4 := Add.ofEquiv (proxy_equiv% Float4)
  instance : Sub Float4 := Sub.ofEquiv (proxy_equiv% Float4)
  instance : Neg Float4 := Neg.ofEquiv (proxy_equiv% Float4)
  instance : Mul Float4 := Mul.ofEquiv (proxy_equiv% Float4)
  instance : Div Float4 := Div.ofEquiv (proxy_equiv% Float4)

end Float4
