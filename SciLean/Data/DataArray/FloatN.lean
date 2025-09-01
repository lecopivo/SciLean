import SciLean.Data.DataArray.DataArray
import SciLean.Data.DataArray.DataArrayEquiv
import SciLean.Data.DataArray.Float
import SciLean.Data.Instances.Sigma

import SciLean.Tactic.SimpleProxyType
import SciLean.Tactic.LSimp

namespace SciLean

structure Float2 where
  (x y : Float)
  deriving Inhabited

namespace Float2

  instance : ToString Float2 where
    toString v := s!"⊞[{v.x}, {v.y}]"

  instance : Size Float2 where
    size := 2

  inductive Index | x | y
    deriving Fintype

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
    getElem_setElem_eq := sorry_proof
    getElem_setElem_neq := sorry_proof

  instance : OfFn Float2 (Index) Float where
    ofFn f := ⟨f .x, f .y⟩

  instance : LawfulOfFn Float2 (Index) where
    getElem_ofFn := by intro f i; cases i <;> rfl

 instance : DataArrayEquiv Float2 Index Float where
    toKn := fun v => ⊞[v.x, v.y] |>.reshape Index sorry_proof
    fromKn := fun v => ⟨v[.x], v[.y]⟩
    left_inv := sorry_proof
    right_inv := sorry_proof

  -- Array Operations with `Idx 2` ---
  instance : GetElem' Float2 (Idx 2) Float where
    getElem v i _ := if i = 0 then v.x else v.y

  instance : DefaultIndex Float2 (Idx 2) where
  instance : DefaultIndexOfRank Float2 1 (Idx 2) where

  instance : InjectiveGetElem Float2 (Idx 2) where
    getElem_injective := by
      rintro ⟨x,y⟩ ⟨x',y'⟩ h
      have := congrFun h 0
      have := congrFun h 1
      simp_all [getElem]
      sorry_proof

  instance : SetElem' Float2 (Idx 2) Float where
    setElem v i vi _ := if i = 0 then ⟨vi, v.y⟩ else ⟨v.x, vi⟩
    setElem_valid := by simp

  instance : LawfulSetElem Float2 (Idx 2) where
    getElem_setElem_eq := sorry_proof
    getElem_setElem_neq := sorry_proof

  instance : OfFn Float2 (Idx 2) Float where
    ofFn f := ⟨f 0, f 1⟩

  instance : LawfulOfFn Float2 (Idx 2) where
    getElem_ofFn := by
      intro f i
      sorry_proof

  instance : DataArrayEquiv Float2 (Idx 2) Float where
    toKn := fun v => ⊞[v.x, v.y]
    fromKn := fun v => ⟨v[0], v[1]⟩
    left_inv := sorry_proof
    right_inv := sorry_proof


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

  instance : Add Float2 := (Add.ofEquiv (proxy_equiv% Float2)) rewrite_by reduce
  instance : Sub Float2 := (Sub.ofEquiv (proxy_equiv% Float2)) rewrite_by reduce
  instance : Neg Float2 := (Neg.ofEquiv (proxy_equiv% Float2)) rewrite_by reduce
  instance : Mul Float2 := (Mul.ofEquiv (proxy_equiv% Float2)) rewrite_by reduce
  instance : Div Float2 := (Div.ofEquiv (proxy_equiv% Float2)) rewrite_by reduce
  instance : SMul Float Float2 := (SMul.ofEquiv Float (proxy_equiv% Float2)) rewrite_by reduce
  instance : Zero Float2 := (Zero.ofEquiv (proxy_equiv% Float2)) rewrite_by reduce
  instance : Norm Float2 := (Norm.ofEquiv (proxy_equiv% Float2)) rewrite_by reduce
  instance : Inner Float Float2 := (Inner.ofEquiv (R:=Float) (proxy_equiv% Float2)) rewrite_by reduce

  instance : AddCommGroup Float2 := AddCommGroup.ofEquiv (proxy_equiv% Float2)
  instance : Module Float Float2 := Module.ofEquiv (proxy_equiv% Float2)

  instance : MetricSpace Float2 := MetricSpace.ofEquiv (proxy_equiv% Float2)
  instance : NormedAddCommGroup Float2 := NormedAddCommGroup.ofEquiv (proxy_equiv% Float2)
  instance : NormedSpace Float Float2 := NormedSpace.ofEquiv (proxy_equiv% Float2)
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
      rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ h
      have := congrFun h 0
      have := congrFun h 1
      have := congrFun h 2
      simp_all [getElem]
      sorry_proof

  instance : SetElem' Float3 (Idx 3) Float where
    setElem v i vi _ := if i = 0 then ⟨vi, v.y, v.z⟩ else if i = 1 then ⟨v.x, vi, v.z⟩ else ⟨v.x, v.y, vi⟩
    setElem_valid := by simp

  instance : LawfulSetElem Float3 (Idx 3) where
    getElem_setElem_eq := sorry_proof
    getElem_setElem_neq := sorry_proof

  instance : OfFn Float3 (Idx 3) Float where
    ofFn f := ⟨f 0, f 1, f 2⟩

  instance : LawfulOfFn Float3 (Idx 3) where
    getElem_ofFn := by intro f i; sorry_proof --match i with | ⟨0,_⟩ | ⟨1,_⟩ | ⟨2,_⟩ => rfl

  instance : PlainDataType Float3 where
    btype := {
      bytes := 24
      h_size := sorry_proof
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
    left_inv := sorry_proof
    right_inv := sorry_proof

  instance {I n} [IndexType I n] : HasRnEquiv (Float3^[I]) (I × Idx 3) Float where

  instance : Add Float3 := (Add.ofEquiv (proxy_equiv% Float3)) rewrite_by reduce
  instance : Sub Float3 := (Sub.ofEquiv (proxy_equiv% Float3)) rewrite_by reduce
  instance : Neg Float3 := (Neg.ofEquiv (proxy_equiv% Float3)) rewrite_by reduce
  instance : Mul Float3 := (Mul.ofEquiv (proxy_equiv% Float3)) rewrite_by reduce
  instance : Div Float3 := (Div.ofEquiv (proxy_equiv% Float3)) rewrite_by reduce
  instance : SMul Float Float3 := (SMul.ofEquiv Float (proxy_equiv% Float3)) rewrite_by reduce
  instance : Zero Float3 := (Zero.ofEquiv (proxy_equiv% Float3)) rewrite_by reduce
  instance : Norm Float3 := (Norm.ofEquiv (proxy_equiv% Float3)) rewrite_by reduce
  instance : Inner Float Float3 := (Inner.ofEquiv (R:=Float) (proxy_equiv% Float3)) rewrite_by reduce

  instance : AddCommGroup Float3 := AddCommGroup.ofEquiv (proxy_equiv% Float3)
  instance : Module Float Float3 := Module.ofEquiv (proxy_equiv% Float3)

  instance : MetricSpace Float3 := MetricSpace.ofEquiv (proxy_equiv% Float3)
  instance : NormedAddCommGroup Float3 := NormedAddCommGroup.ofEquiv (proxy_equiv% Float3)
  instance : NormedSpace Float Float3 := NormedSpace.ofEquiv (proxy_equiv% Float3)
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
      rintro ⟨x,y,z,w⟩ ⟨x',y',z',w'⟩ h
      have := congrFun h 0
      have := congrFun h 1
      have := congrFun h 2
      have := congrFun h 3
      simp_all [getElem]
      sorry_proof

  instance : SetElem' Float4 (Idx 4) Float where
    setElem v i vi _ :=
      if i = 0 then ⟨vi, v.y, v.z, v.w⟩
      else if i = 1 then ⟨v.x, vi, v.z, v.w⟩
      else if i = 2 then ⟨v.x, v.y, vi, v.w⟩
      else ⟨v.x, v.y, v.z, vi⟩
    setElem_valid := by simp

  instance : LawfulSetElem Float4 (Idx 4) where
    getElem_setElem_eq := sorry_proof
    getElem_setElem_neq := sorry_proof

  instance : OfFn Float4 (Idx 4) Float where
    ofFn f := ⟨f 0, f 1, f 2, f 3⟩

  instance : LawfulOfFn Float4 (Idx 4) where
    getElem_ofFn := by intro f i; sorry_proof --match i with | ⟨0,_⟩ | ⟨1,_⟩ | ⟨2,_⟩ | ⟨3,_⟩ => rfl

  instance : PlainDataType Float4 where
    btype := {
      bytes := 32
      h_size := sorry_proof
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
    left_inv := sorry_proof
    right_inv := sorry_proof

  instance {I n} [IndexType I n] : HasRnEquiv (Float4^[I]) (I × Idx 4) Float where

  instance : Add Float4 := (Add.ofEquiv (proxy_equiv% Float4)) rewrite_by reduce
  instance : Sub Float4 := (Sub.ofEquiv (proxy_equiv% Float4)) rewrite_by reduce
  instance : Neg Float4 := (Neg.ofEquiv (proxy_equiv% Float4)) rewrite_by reduce
  instance : Mul Float4 := (Mul.ofEquiv (proxy_equiv% Float4)) rewrite_by reduce
  instance : Div Float4 := (Div.ofEquiv (proxy_equiv% Float4)) rewrite_by reduce
