import SciLean.Data.DataArray.DataArray
import SciLean.Data.DataArray.DataArrayEquiv
import SciLean.Data.DataArray.VectorType
import SciLean.Data.DataArray.Float

import SciLean.Data.Instances.Sigma

namespace SciLean

structure Float2 where
  (x y : Float)
  deriving Inhabited

namespace Float2

  instance : ToString Float2 where
    toString v := s!"⊞[{v.x}, {v.y}]"

  instance : Size Float2 where
    size := 2

  instance : GetElem' Float2 (Fin 2) Float where
    getElem v i _ := if i = 0 then v.x else v.y

  instance : DefaultIndex Float2 (Fin 2) where

  instance : InjectiveGetElem Float2 (Fin 2) where
    getElem_injective := by
      rintro ⟨x,y⟩ ⟨x',y'⟩ h
      have := congrFun h 0
      have := congrFun h 1
      simp_all [getElem]

  instance : SetElem' Float2 (Fin 2) Float where
    setElem v i vi _ := if i = 0 then ⟨vi, v.y⟩ else ⟨v.x, vi⟩
    setElem_valid := by simp

  instance : LawfulSetElem Float2 (Fin 2) where
    getElem_setElem_eq := sorry_proof
    getElem_setElem_neq := sorry_proof

  instance : OfFn Float2 (Fin 2) Float where
    ofFn f := ⟨f 0, f 1⟩

  instance : LawfulOfFn Float2 (Fin 2) where
    getElem_ofFn := by
      intro f i
      match i with
      | ⟨0,_⟩ | ⟨1,_⟩ => rfl

  -- todo: this should be derived from `PlainDataType.ofEquiv`
  instance : PlainDataType Float2 where
    btype := .inr {
      bytes := 16
      h_size := sorry_proof
      fromByteArray b i _ :=
        let b := b.toFloatArray sorry_proof
        let x := b.get (i/8).toNat sorry_proof
        let y := b.get (i/8 + 1).toNat sorry_proof
        ⟨x,y⟩
      toByteArray b i _ v :=
        let b := b.toFloatArray sorry_proof
        let b := b.set (i/8).toNat v.x sorry_proof
        let b := b.set (i/8 + 1).toNat v.y sorry_proof
        b.toByteArray
      toByteArray_size := sorry_proof
      fromByteArray_toByteArray := sorry_proof
      fromByteArray_toByteArray_other := sorry_proof
    }

  -- This instance does not immediately provide `VectorType.Base Float2 (Fin 2) Float`
  -- as to derive that we need `DefaultDataArrayEquiv Float2 (Fin 2) Float`.
  instance : DataArrayEquiv Float2 (Fin 2) Float where
    equiv := {
      toFun := fun v => ⊞[v.x, v.y]
      invFun := fun v => ⟨v[0], v[1]⟩,
      left_inv := sorry_proof
      right_inv := sorry_proof
    }

  -- We do not want to have `DefaultDataArrayEquiv Float2 Fin 2 Float`
  -- as this would derive algebraic instances on `Float2` throught `DataArray` which would
  -- yield inefficient code. Instead, we want to derive instances on `Float2` directly.
  instance {I} [IndexType I] : DefaultDataArrayEquiv (Float2^[I]) (I × Fin 2) Float where

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

  instance : GetElem' Float3 (Fin 3) Float where
    getElem v i _ := if i = 0 then v.x else if i = 1 then v.y else v.z

  instance : DefaultIndex Float3 (Fin 3) where

  instance : InjectiveGetElem Float3 (Fin 3) where
    getElem_injective := by
      rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ h
      have := congrFun h 0
      have := congrFun h 1
      have := congrFun h 2
      simp_all [getElem]

  instance : SetElem' Float3 (Fin 3) Float where
    setElem v i vi _ := if i = 0 then ⟨vi, v.y, v.z⟩ else if i = 1 then ⟨v.x, vi, v.z⟩ else ⟨v.x, v.y, vi⟩
    setElem_valid := by simp

  instance : LawfulSetElem Float3 (Fin 3) where
    getElem_setElem_eq := sorry_proof
    getElem_setElem_neq := sorry_proof

  instance : OfFn Float3 (Fin 3) Float where
    ofFn f := ⟨f 0, f 1, f 2⟩

  instance : LawfulOfFn Float3 (Fin 3) where
    getElem_ofFn := by intro f i; match i with | ⟨0,_⟩ | ⟨1,_⟩ | ⟨2,_⟩ => rfl

  instance : PlainDataType Float3 where
    btype := .inr {
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

  instance : DataArrayEquiv Float3 (Fin 3) Float where
    equiv := {
      toFun := fun v => ⊞[v.x, v.y, v.z]
      invFun := fun v => ⟨v[0], v[1], v[2]⟩,
      left_inv := sorry_proof
      right_inv := sorry_proof
    }

  instance {I} [IndexType I] : DefaultDataArrayEquiv (Float3^[I]) (I × Fin 3) Float where

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

  instance : GetElem' Float4 (Fin 4) Float where
    getElem v i _ := if i = 0 then v.x else if i = 1 then v.y else if i = 2 then v.z else v.w

  instance : DefaultIndex Float4 (Fin 4) where

  instance : InjectiveGetElem Float4 (Fin 4) where
    getElem_injective := by
      rintro ⟨x,y,z,w⟩ ⟨x',y',z',w'⟩ h
      have := congrFun h 0
      have := congrFun h 1
      have := congrFun h 2
      have := congrFun h 3
      simp_all [getElem]

  instance : SetElem' Float4 (Fin 4) Float where
    setElem v i vi _ :=
      if i = 0 then ⟨vi, v.y, v.z, v.w⟩
      else if i = 1 then ⟨v.x, vi, v.z, v.w⟩
      else if i = 2 then ⟨v.x, v.y, vi, v.w⟩
      else ⟨v.x, v.y, v.z, vi⟩
    setElem_valid := by simp

  instance : LawfulSetElem Float4 (Fin 4) where
    getElem_setElem_eq := sorry_proof
    getElem_setElem_neq := sorry_proof

  instance : OfFn Float4 (Fin 4) Float where
    ofFn f := ⟨f 0, f 1, f 2, f 3⟩

  instance : LawfulOfFn Float4 (Fin 4) where
    getElem_ofFn := by intro f i; match i with | ⟨0,_⟩ | ⟨1,_⟩ | ⟨2,_⟩ | ⟨3,_⟩ => rfl

  instance : PlainDataType Float4 where
    btype := .inr {
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

  instance : DataArrayEquiv Float4 (Fin 4) Float where
    equiv := {
      toFun := fun v => ⊞[v.x, v.y, v.z, v.w]
      invFun := fun v => ⟨v[0], v[1], v[2], v[3]⟩,
      left_inv := sorry_proof
      right_inv := sorry_proof
    }

  instance {I} [IndexType I] : DefaultDataArrayEquiv (Float4^[I]) (I × Fin 4) Float where

  instance : Add Float4 := (Add.ofEquiv (proxy_equiv% Float4)) rewrite_by reduce
  instance : Sub Float4 := (Sub.ofEquiv (proxy_equiv% Float4)) rewrite_by reduce
  instance : Neg Float4 := (Neg.ofEquiv (proxy_equiv% Float4)) rewrite_by reduce
  instance : Mul Float4 := (Mul.ofEquiv (proxy_equiv% Float4)) rewrite_by reduce
  instance : Div Float4 := (Div.ofEquiv (proxy_equiv% Float4)) rewrite_by reduce
