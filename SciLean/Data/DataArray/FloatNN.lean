import SciLean.Data.DataArray.FloatN

namespace SciLean

-- structure Float22 where
--   (xx xy yx yy : Float)

-- namespace Float22

--   instance : Size Float22 where
--     size := 4

--   instance : GetElem' Float22 (Fin 2 × Fin 2) Float where
--     getElem A i _ :=
--       match i with
--       | (0,0) => A.xx
--       | (0,1) => A.xy
--       | (1,0) => A.yx
--       | (1,1) => A.yy

--   instance : SetElem' Float22 (Fin 2 × Fin 2) Float where
--     setElem A i v _ :=
--       match i with
--       | (0,0) => { A with xx := v }
--       | (0,1) => { A with xy := v }
--       | (1,0) => { A with yx := v }
--       | (1,1) => { A with yy := v }
--     setElem_valid := by simp

--   instance : DefaultIndex Float22 (Fin 2 × Fin 2) where

--   instance : InjectiveGetElem Float22 (Fin 2 × Fin 2) where
--     getElem_injective := by
--       rintro ⟨xx, xy, yx, yy⟩ ⟨xx', xy', yx', yy'⟩ h
--       have := congrFun h (0,0)
--       have := congrFun h (0,1)
--       have := congrFun h (1,0)
--       have := congrFun h (1,1)
--       simp_all [getElem]

--   instance : OfFn Float22 (Fin 2 × Fin 2) Float where
--     ofFn f := ⟨f (0,0), f (0,1), f (1,0), f (1,1)⟩

--   instance : LawfulOfFn Float22 (Fin 2 × Fin 2) where
--     getElem_ofFn := by
--       intro f i
--       match i with
--       | (0,0) => rfl
--       | (0,1) => rfl
--       | (1,0) => rfl
--       | (1,1) => rfl

--   instance : PlainDataType Float22 where
--     btype := .inr {
--       bytes := 32
--       h_size := sorry_proof
--       fromByteArray b i _ :=
--         let b := b.toFloatArray sorry_proof
--         let xx := b.get (i/8).toNat sorry_proof
--         let xy := b.get (i/8 + 1).toNat sorry_proof
--         let yx := b.get (i/8 + 2).toNat sorry_proof
--         let yy := b.get (i/8 + 3).toNat sorry_proof
--         ⟨xx, xy, yx, yy⟩
--       toByteArray b i _ v :=
--         let b := b.toFloatArray sorry_proof
--         let b := b.set (i/8).toNat v.xx sorry_proof
--         let b := b.set (i/8 + 1).toNat v.xy sorry_proof
--         let b := b.set (i/8 + 2).toNat v.yx sorry_proof
--         let b := b.set (i/8 + 3).toNat v.yy sorry_proof
--         b.toByteArray
--       toByteArray_size := sorry_proof
--       fromByteArray_toByteArray := sorry_proof
--       fromByteArray_toByteArray_other := sorry_proof
--     }

--   instance : DataArrayEquiv Float22 (Idx 2 × Idx 2) Float where
--     equiv := {
--       toFun := fun v => ⊞[v.xx, v.xy; v.yx, v.yy]
--       invFun := fun v => ⟨v[0, 0], v[0,1], v[1,0], v[1,1]⟩,
--       left_inv := sorry_proof
--       right_inv := sorry_proof
--     }

--   instance {I} {nI} [IndexType I nI] : DefaultDataArrayEquiv (Float22^[I]) (I × Idx 2 × Idx 2) Float where

--   instance : Add Float22 := (Add.ofEquiv (proxy_equiv% Float22)) rewrite_by reduce
--   instance : Sub Float22 := (Sub.ofEquiv (proxy_equiv% Float22)) rewrite_by reduce
--   instance : Neg Float22 := (Neg.ofEquiv (proxy_equiv% Float22)) rewrite_by reduce
--   instance : Mul Float22 := (Mul.ofEquiv (proxy_equiv% Float22)) rewrite_by reduce
--   instance : Div Float22 := (Div.ofEquiv (proxy_equiv% Float22)) rewrite_by reduce
--   instance : SMul Float Float22 := (SMul.ofEquiv Float (proxy_equiv% Float22)) rewrite_by reduce
--   instance : Zero Float22 := (Zero.ofEquiv (proxy_equiv% Float22)) rewrite_by reduce
--   instance : Norm Float22 := (Norm.ofEquiv (proxy_equiv% Float22)) rewrite_by reduce
--   instance : Inner Float Float22 := (Inner.ofEquiv (R:=Float) (proxy_equiv% Float22)) rewrite_by reduce

--   instance : AddCommGroup Float22 := AddCommGroup.ofEquiv (proxy_equiv% Float22)
--   instance : Module Float Float22 := Module.ofEquiv (proxy_equiv% Float22)

--   instance : MetricSpace Float22 := MetricSpace.ofEquiv (proxy_equiv% Float22)
--   instance : NormedAddCommGroup Float22 := NormedAddCommGroup.ofEquiv (proxy_equiv% Float22)
--   instance : NormedSpace Float Float22 := NormedSpace.ofEquiv (proxy_equiv% Float22)
--   instance : AdjointSpace Float Float22 := AdjointSpace.ofEquiv (proxy_equiv% Float22)

--   def vecMul (A : Float22) (v : Float2) : Float2 :=
--     ⟨A.xx * v.x + A.xy * v.y, A.yx * v.x + A.yy * v.y⟩

--   instance : HMul Float22 Float2 Float2 where
--     hMul := vecMul

-- end Float22

-- structure Float33 where
--   (xx xy xz yx yy yz zx zy zz : Float)

-- namespace Float33

--   instance : Size Float33 where
--     size := 9

--   instance : GetElem' Float33 (Idx 3 × Idx 3) Float where
--     getElem := fun A (i,j) _ =>
--       match i, j with
--       | 0, 0 => A.xx
--       | 0, 1 => A.xy
--       | 0, 2 => A.xz
--       | 1, 0 => A.yx
--       | 1, 1 => A.yy
--       | 1, 2 => A.yz
--       | 2, 0 => A.zx
--       | 2, 1 => A.zy
--       | 2, 2 => A.zz

--   instance : SetElem' Float33 (Idx 3 × Idx 3) Float where
--     setElem A i v _ :=
--       match i with
--       | (0,0) => { A with xx := v }
--       | (0,1) => { A with xy := v }
--       | (0,2) => { A with xz := v }
--       | (1,0) => { A with yx := v }
--       | (1,1) => { A with yy := v }
--       | (1,2) => { A with yz := v }
--       | (2,0) => { A with zx := v }
--       | (2,1) => { A with zy := v }
--       | (2,2) => { A with zz := v }
--     setElem_valid := by simp

--   instance : DefaultIndex Float33 (Idx 3 × Idx 3) where

--   instance : InjectiveGetElem Float33 (Idx 3 × Idx 3) where
--     getElem_injective := by
--       rintro ⟨xx, xy, xz, yx, yy, yz, zx, zy, zz⟩ ⟨xx', xy', xz', yx', yy', yz', zx', zy', zz'⟩ h
--       have := congrFun h (0,0)
--       have := congrFun h (0,1)
--       have := congrFun h (0,2)
--       have := congrFun h (1,0)
--       have := congrFun h (1,1)
--       have := congrFun h (1,2)
--       have := congrFun h (2,0)
--       have := congrFun h (2,1)
--       have := congrFun h (2,2)
--       simp_all [getElem]

--   instance : OfFn Float33 (Idx 3 × Idx 3) Float where
--     ofFn f := ⟨f (0,0), f (0,1), f (0,2), f (1,0), f (1,1), f (1,2), f (2,0), f (2,1), f (2,2)⟩

--   instance : LawfulOfFn Float33 (Idx 3 × Idx 3) where
--     getElem_ofFn := by
--       intro f i;
--       match i with
--       | (0,0) => rfl
--       | (0,1) => rfl
--       | (0,2) => rfl
--       | (1,0) => rfl
--       | (1,1) => rfl
--       | (1,2) => rfl
--       | (2,0) => rfl
--       | (2,1) => rfl
--       | (2,2) => rfl


--   instance : PlainDataType Float33 where
--     btype := .inr {
--       bytes := 72
--       h_size := sorry_proof
--       fromByteArray b i _ :=
--         let b := b.toFloatArray sorry_proof
--         let xx := b.get (i/8).toNat sorry_proof
--         let xy := b.get (i/8 + 1).toNat sorry_proof
--         let xz := b.get (i/8 + 2).toNat sorry_proof
--         let yx := b.get (i/8 + 3).toNat sorry_proof
--         let yy := b.get (i/8 + 4).toNat sorry_proof
--         let yz := b.get (i/8 + 5).toNat sorry_proof
--         let zx := b.get (i/8 + 6).toNat sorry_proof
--         let zy := b.get (i/8 + 7).toNat sorry_proof
--         let zz := b.get (i/8 + 8).toNat sorry_proof
--         ⟨xx, xy, xz, yx, yy, yz, zx, zy, zz⟩
--       toByteArray b i _ v :=
--         let b := b.toFloatArray sorry_proof
--         let b := b.set (i/8).toNat v.xx sorry_proof
--         let b := b.set (i/8 + 1).toNat v.xy sorry_proof
--         let b := b.set (i/8 + 2).toNat v.xz sorry_proof
--         let b := b.set (i/8 + 3).toNat v.yx sorry_proof
--         let b := b.set (i/8 + 4).toNat v.yy sorry_proof
--         let b := b.set (i/8 + 5).toNat v.yz sorry_proof
--         let b := b.set (i/8 + 6).toNat v.zx sorry_proof
--         let b := b.set (i/8 + 7).toNat v.zy sorry_proof
--         let b := b.set (i/8 + 8).toNat v.zz sorry_proof
--         b.toByteArray
--       toByteArray_size := sorry_proof
--       fromByteArray_toByteArray := sorry_proof
--       fromByteArray_toByteArray_other := sorry_proof
--     }

--   instance : DataArrayEquiv Float33 (Idx 3 × Idx 3) Float where
--     equiv := {
--       toFun := fun v => ⊞[v.xx, v.xy, v.xz; v.yx, v.yy, v.yz; v.zx, v.zy, v.zz]
--       invFun := fun v => ⟨v[0, 0], v[0,1], v[0,2], v[1,0], v[1,1], v[1,2], v[2,0], v[2,1], v[2,2]⟩,
--       left_inv := sorry_proof
--       right_inv := sorry_proof
--     }

--   instance {I} {nI} [IndexType I nI] : DefaultDataArrayEquiv (Float33^[I]) (I × Idx 3 × Idx 3) Float where

--   instance : Add Float33 := (Add.ofEquiv (proxy_equiv% Float33)) rewrite_by reduce
--   instance : Sub Float33 := (Sub.ofEquiv (proxy_equiv% Float33)) rewrite_by reduce
--   instance : Neg Float33 := (Neg.ofEquiv (proxy_equiv% Float33)) rewrite_by reduce
--   instance : Mul Float33 := (Mul.ofEquiv (proxy_equiv% Float33)) rewrite_by reduce
--   instance : Div Float33 := (Div.ofEquiv (proxy_equiv% Float33)) rewrite_by reduce
--   instance : SMul Float Float33 := (SMul.ofEquiv Float (proxy_equiv% Float33)) rewrite_by reduce
--   instance : Zero Float33 := (Zero.ofEquiv (proxy_equiv% Float33)) rewrite_by reduce
--   instance : Norm Float33 := (Norm.ofEquiv (proxy_equiv% Float33)) rewrite_by reduce
--   instance : Inner Float Float33 := (Inner.ofEquiv (R:=Float) (proxy_equiv% Float33)) rewrite_by reduce

--   instance : AddCommGroup Float33 := AddCommGroup.ofEquiv (proxy_equiv% Float33)
--   instance : Module Float Float33 := Module.ofEquiv (proxy_equiv% Float33)

--   instance : MetricSpace Float33 := MetricSpace.ofEquiv (proxy_equiv% Float33)
--   instance : NormedAddCommGroup Float33 := NormedAddCommGroup.ofEquiv (proxy_equiv% Float33)
--   instance : NormedSpace Float Float33 := NormedSpace.ofEquiv (proxy_equiv% Float33)
--   instance : AdjointSpace Float Float33 := AdjointSpace.ofEquiv (proxy_equiv% Float33)

--   def vecMul (A : Float33) (v : Float3) : Float3 :=
--     ⟨A.xx * v.x + A.xy * v.y + A.xz * v.z, A.yx * v.x + A.yy * v.y + A.yz * v.z, A.zx * v.x + A.zy * v.y + A.zz * v.z⟩

--   instance : HMul Float33 Float3 Float3 where
--     hMul := vecMul

-- end Float33

-- structure Float44 where
--   (xx xy xz xw yx yy yz yw zx zy zz zw wx wy wz ww : Float)

-- namespace Float44

--   instance : Size Float44 where
--     size := 16

--   instance : GetElem' Float44 (Idx 4 × Idx 4) Float where
--     getElem A i _ :=
--       match i with
--       | (0,0) => A.xx
--       | (0,1) => A.xy
--       | (0,2) => A.xz
--       | (0,3) => A.xw
--       | (1,0) => A.yx
--       | (1,1) => A.yy
--       | (1,2) => A.yz
--       | (1,3) => A.yw
--       | (2,0) => A.zx
--       | (2,1) => A.zy
--       | (2,2) => A.zz
--       | (2,3) => A.zw
--       | (3,0) => A.wx
--       | (3,1) => A.wy
--       | (3,2) => A.wz
--       | (3,3) => A.ww

--   instance : SetElem' Float44 (Idx 4 × Idx 4) Float where
--     setElem A i v _ :=
--       match i with
--       | (0,0) => { A with xx := v }
--       | (0,1) => { A with xy := v }
--       | (0,2) => { A with xz := v }
--       | (0,3) => { A with xw := v }
--       | (1,0) => { A with yx := v }
--       | (1,1) => { A with yy := v }
--       | (1,2) => { A with yz := v }
--       | (1,3) => { A with yw := v }
--       | (2,0) => { A with zx := v }
--       | (2,1) => { A with zy := v }
--       | (2,2) => { A with zz := v }
--       | (2,3) => { A with zw := v }
--       | (3,0) => { A with wx := v }
--       | (3,1) => { A with wy := v }
--       | (3,2) => { A with wz := v }
--       | (3,3) => { A with ww := v }
--     setElem_valid := by simp

--   instance : DefaultIndex Float44 (Idx 4 × Idx 4) where

--   instance : InjectiveGetElem Float44 (Idx 4 × Idx 4) where
--     getElem_injective := by
--       rintro ⟨xx, xy, xz, xw, yx, yy, yz, yw, zx, zy, zz, zw, wx, wy, wz, ww⟩ ⟨xx', xy', xz', xw', yx', yy', yz', yw', zx', zy', zz', zw', wx', wy', wz', ww'⟩ h
--       have := congrFun h (0,0)
--       have := congrFun h (0,1)
--       have := congrFun h (0,2)
--       have := congrFun h (0,3)
--       have := congrFun h (1,0)
--       have := congrFun h (1,1)
--       have := congrFun h (1,2)
--       have := congrFun h (1,3)
--       have := congrFun h (2,0)
--       have := congrFun h (2,1)
--       have := congrFun h (2,2)
--       have := congrFun h (2,3)
--       have := congrFun h (3,0)
--       have := congrFun h (3,1)
--       have := congrFun h (3,2)
--       have := congrFun h (3,3)
--       simp_all [getElem]

--   instance : OfFn Float44 (Idx 4 × Idx 4) Float where
--     ofFn f := ⟨f (0,0), f (0,1), f (0,2), f (0,3), f (1,0), f (1,1), f (1,2), f (1,3), f (2,0), f (2,1), f (2,2), f (2,3), f (3,0), f (3,1), f (3,2), f (3,3)⟩

--   instance : LawfulOfFn Float44 (Idx 4 × Idx 4) where
--     getElem_ofFn := by
--       intro f i
--       match i with
--       | (0,0) => rfl
--       | (0,1) => rfl
--       | (0,2) => rfl
--       | (0,3) => rfl
--       | (1,0) => rfl
--       | (1,1) => rfl
--       | (1,2) => rfl
--       | (1,3) => rfl
--       | (2,0) => rfl
--       | (2,1) => rfl
--       | (2,2) => rfl
--       | (2,3) => rfl
--       | (3,0) => rfl
--       | (3,1) => rfl
--       | (3,2) => rfl
--       | (3,3) => rfl

--   instance : PlainDataType Float44 where
--     btype := .inr {
--       bytes := 128
--       h_size := sorry_proof
--       fromByteArray b i _ :=
--         let b := b.toFloatArray sorry_proof
--         let xx := b.get (i/8).toNat sorry_proof
--         let xy := b.get (i/8 + 1).toNat sorry_proof
--         let xz := b.get (i/8 + 2).toNat sorry_proof
--         let xw := b.get (i/8 + 3).toNat sorry_proof
--         let yx := b.get (i/8 + 4).toNat sorry_proof
--         let yy := b.get (i/8 + 5).toNat sorry_proof
--         let yz := b.get (i/8 + 6).toNat sorry_proof
--         let yw := b.get (i/8 + 7).toNat sorry_proof
--         let zx := b.get (i/8 + 8).toNat sorry_proof
--         let zy := b.get (i/8 + 9).toNat sorry_proof
--         let zz := b.get (i/8 + 10).toNat sorry_proof
--         let zw := b.get (i/8 + 11).toNat sorry_proof
--         let wx := b.get (i/8 + 12).toNat sorry_proof
--         let wy := b.get (i/8 + 13).toNat sorry_proof
--         let wz := b.get (i/8 + 14).toNat sorry_proof
--         let ww := b.get (i/8 + 15).toNat sorry_proof
--         ⟨xx, xy, xz, xw, yx, yy, yz, yw, zx, zy, zz, zw, wx, wy, wz, ww⟩
--       toByteArray b i _ v :=
--         let b := b.toFloatArray sorry_proof
--         let b := b.set (i/8).toNat v.xx sorry_proof
--         let b := b.set (i/8 + 1).toNat v.xy sorry_proof
--         let b := b.set (i/8 + 2).toNat v.xz sorry_proof
--         let b := b.set (i/8 + 3).toNat v.xw sorry_proof
--         let b := b.set (i/8 + 4).toNat v.yx sorry_proof
--         let b := b.set (i/8 + 5).toNat v.yy sorry_proof
--         let b := b.set (i/8 + 6).toNat v.yz sorry_proof
--         let b := b.set (i/8 + 7).toNat v.yw sorry_proof
--         let b := b.set (i/8 + 8).toNat v.zx sorry_proof
--         let b := b.set (i/8 + 9).toNat v.zy sorry_proof
--         let b := b.set (i/8 + 10).toNat v.zz sorry_proof
--         let b := b.set (i/8 + 11).toNat v.zw sorry_proof
--         let b := b.set (i/8 + 12).toNat v.wx sorry_proof
--         let b := b.set (i/8 + 13).toNat v.wy sorry_proof
--         let b := b.set (i/8 + 14).toNat v.wz sorry_proof
--         let b := b.set (i/8 + 15).toNat v.ww sorry_proof
--         b.toByteArray
--       toByteArray_size := sorry_proof
--       fromByteArray_toByteArray := sorry_proof
--       fromByteArray_toByteArray_other := sorry_proof
--     }

--   instance : DataArrayEquiv Float44 (Idx 4 × Idx 4) Float where
--     equiv := {
--       toFun := fun v => ⊞[v.xx, v.xy, v.xz, v.xw; v.yx, v.yy, v.yz, v.yw; v.zx, v.zy, v.zz, v.zw; v.wx, v.wy, v.wz, v.ww]
--       invFun := fun v => ⟨v[0, 0], v[0,1], v[0,2], v[0,3], v[1,0], v[1,1], v[1,2], v[1,3], v[2,0], v[2,1], v[2,2], v[2,3], v[3,0], v[3,1], v[3,2], v[3,3]⟩,
--       left_inv := sorry_proof
--       right_inv := sorry_proof
--     }

--   instance {I n} [IndexType I n] : DefaultDataArrayEquiv (Float44^[I]) (I × Idx 4 × Idx 4) Float where

--   instance : Add Float44 := (Add.ofEquiv (proxy_equiv% Float44)) rewrite_by reduce
--   instance : Sub Float44 := (Sub.ofEquiv (proxy_equiv% Float44)) rewrite_by reduce
--   instance : Neg Float44 := (Neg.ofEquiv (proxy_equiv% Float44)) rewrite_by reduce
--   instance : Mul Float44 := (Mul.ofEquiv (proxy_equiv% Float44)) rewrite_by reduce
--   instance : Div Float44 := (Div.ofEquiv (proxy_equiv% Float44)) rewrite_by reduce
--   instance : SMul Float Float44 := (SMul.ofEquiv Float (proxy_equiv% Float44)) rewrite_by reduce
--   instance : Zero Float44 := (Zero.ofEquiv (proxy_equiv% Float44)) rewrite_by reduce
--   instance : Norm Float44 := (Norm.ofEquiv (proxy_equiv% Float44)) rewrite_by reduce
--   instance : Inner Float Float44 := (Inner.ofEquiv (R:=Float) (proxy_equiv% Float44)) rewrite_by reduce

--   instance : AddCommGroup Float44 := AddCommGroup.ofEquiv (proxy_equiv% Float44)
--   instance : Module Float Float44 := Module.ofEquiv (proxy_equiv% Float44)

--   instance : MetricSpace Float44 := MetricSpace.ofEquiv (proxy_equiv% Float44)
--   instance : NormedAddCommGroup Float44 := NormedAddCommGroup.ofEquiv (proxy_equiv% Float44)
--   instance : NormedSpace Float Float44 := NormedSpace.ofEquiv (proxy_equiv% Float44)
--   instance : AdjointSpace Float Float44 := AdjointSpace.ofEquiv (proxy_equiv% Float44)

--   def vecMul (A : Float44) (v : Float4) : Float4 :=
--     ⟨A.xx * v.x + A.xy * v.y + A.xz * v.z + A.xw * v.w, A.yx * v.x + A.yy * v.y + A.yz * v.z + A.yw * v.w, A.zx * v.x + A.zy * v.y + A.zz * v.z + A.zw * v.w, A.wx * v.x + A.wy * v.y + A.wz * v.z + A.ww * v.w⟩

--   instance : HMul Float44 Float4 Float4 where
--     hMul := vecMul

-- end Float44
