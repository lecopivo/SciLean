import SciLean.Data.DataArray.DataArray

namespace SciLean

structure Vec2 (α : Type) where
  (x y : α)


namespace Vec2

  def get (v : Vec2 α) (i : Idx 2) : α :=
    if i.1 = 0 then
      v.x
    else
      v.y

  def set (v : Vec2 α) (i : Idx 2) (vi : α) : Vec2 α :=
    if i.1 = 0 then
      ⟨vi, v.y⟩
    else
      ⟨v.x, vi⟩

  def intro (f : Idx 2 → α) : Vec2 α := ⟨f 0, f 1⟩

  instance : GetElem (Vec2 α) (Idx 2) α (λ _ _ => True) where
    getElem v i _ := v.get i

  instance : SetElem (Vec2 α) (Idx 2) α where
    setElem v i xi := v.set i xi

  instance : IntroElem (Vec2 α) (Idx 2) α where
    introElem := intro

  instance : StructType (Vec2 α) (Idx 2) (fun _ => α) where
    structProj x i := x[i]
    structMake f := introElem f
    structModify i f x := setElem x i (f x[i])
    left_inv := sorry_proof
    right_inv := sorry_proof
    structProj_structModify  := sorry_proof
    structProj_structModify' := sorry_proof

  instance : ArrayType (Vec2 α) (Idx 2) α where
    getElem_structProj   := by intros; rfl
    setElem_structModify := by intros; rfl
    introElem_structMake := by intros; rfl

  instance [ba : PlainDataType α] : PlainDataType (Vec2 α) where
    btype :=
      match ba.btype with
      | .inl bitType  =>
        if h : 2 * bitType.bits ≤ 8 then
          .inl {
            bits := 2 * bitType.bits
            h_size := h
            fromByte := fun b =>
              let ones : UInt8 := 255
              let mask    := (ones - (ones <<< bitType.bits))   -- 00000111
              {
                x := bitType.fromByte (b &&& mask)
                y := bitType.fromByte ((b >>> bitType.bits) &&& mask)
              }
            toByte := fun v =>
              let x := bitType.toByte v.x
              let y := bitType.toByte v.y <<< bitType.bits
              (x ||| y)
            fromByte_toByte := sorry_proof
          }
        else
          .inr {
            bytes := 2
            h_size := sorry_proof
            fromByteArray := fun b i _ =>
              {
                x := bitType.fromByte (b.uget i sorry_proof)
                y := bitType.fromByte (b.uget (i+1) sorry_proof)
              }
            toByteArray := fun b i _ v => Id.run do
              let mut b := b
              b := b.uset  i    (bitType.toByte v.x) sorry_proof
              b := b.uset (i+1) (bitType.toByte v.y) sorry_proof
              b
            toByteArray_size := sorry_proof
            fromByteArray_toByteArray := sorry_proof
            fromByteArray_toByteArray_other := sorry_proof
                                            }
      | .inr byteType =>
          .inr {
            bytes := 2 * byteType.bytes
            h_size := sorry_proof
            fromByteArray := fun b i _ =>
              {
                x := byteType.fromByteArray b i sorry_proof
                y := byteType.fromByteArray b (i + byteType.bytes) sorry_proof
              }
            toByteArray := fun b i _ v => Id.run do
              let mut b := b
              b := byteType.toByteArray b i sorry_proof v.x
              b := byteType.toByteArray b (i + byteType.bytes) sorry_proof v.y
              b
            toByteArray_size := sorry_proof
            fromByteArray_toByteArray := sorry_proof
            fromByteArray_toByteArray_other := sorry_proof
          }


end Vec2


structure Vec3 (α : Type) where
  (x y z : α)


namespace Vec3
  def ofArray [Inhabited α] (xs : Array α) : Vec3 α where
    x := xs.get! 0
    y := xs.get! 1
    z := xs.get! 2

  def map (f : α → β) (v : Vec3 α) : Vec3 β where
    x := f v.x
    y := f v.y
    z := f v.z

  def get (v : Vec3 α) (i : Idx 3) : α :=
  if i.1 = 0 then
    v.x
  else if i.1 = 1 then
    v.y
  else
    v.z

  def set (v : Vec3 α) (i : Idx 3) (vi : α) : Vec3 α :=
  if i.1 = 0 then
    ⟨vi, v.y, v.z⟩
  else if i.1 = 1 then
    ⟨v.x, vi, v.z⟩
  else
    ⟨v.x, v.y, vi⟩

  def intro (f : Idx 3 → α) : Vec3 α := ⟨f 0, f 1, f 2⟩

  instance : GetElem (Vec3 α) (Idx 3) α (λ _ _ => True) where
    getElem v i _ := v.get i

  instance : SetElem (Vec3 α) (Idx 3) α where
    setElem v i xi := v.set i xi

  instance : IntroElem (Vec3 α) (Idx 3) α where
    introElem := intro

  instance : StructType (Vec3 α) (Idx 3) (fun _ => α) where
    structProj x i := x[i]
    structMake f := introElem f
    structModify i f x := setElem x i (f x[i])
    left_inv := sorry_proof
    right_inv := sorry_proof
    structProj_structModify  := sorry_proof
    structProj_structModify' := sorry_proof

  instance : ArrayType (Vec3 α) (Idx 3) α where
    getElem_structProj   := by intros; rfl
    setElem_structModify := by intros; rfl
    introElem_structMake := by intros; rfl

  instance [ba : PlainDataType α] : PlainDataType (Vec3 α) where
    btype :=
      match ba.btype with
      | .inl bitType  =>
        if h : 3 * bitType.bits ≤ 8 then
          .inl {
            bits := 3 * bitType.bits
            h_size := h
            fromByte := fun b =>
              let ones : UInt8 := 255
              let mask    := (ones - (ones <<< bitType.bits))   -- 00000111
              {
                x := bitType.fromByte (b &&& mask)
                y := bitType.fromByte ((b >>> bitType.bits) &&& mask)
                z := bitType.fromByte ((b >>> (2*bitType.bits) &&& mask))
              }
            toByte := fun v =>
              let x := bitType.toByte v.x
              let y := bitType.toByte v.y <<< bitType.bits
              let z := bitType.toByte v.z <<< (2 * bitType.bits)
              (x ||| y ||| z)
            fromByte_toByte := sorry_proof
          }
        else
          .inr {
            bytes := 3
            h_size := sorry_proof
            fromByteArray := fun b i _ =>
              {
                x := bitType.fromByte (b.uget i sorry_proof)
                y := bitType.fromByte (b.uget (i+1) sorry_proof)
                z := bitType.fromByte (b.uget (i+2) sorry_proof)
              }
            toByteArray := fun b i _ v => Id.run do
              let mut b := b
              b := b.uset  i    (bitType.toByte v.x) sorry_proof
              b := b.uset (i+1) (bitType.toByte v.y) sorry_proof
              b := b.uset (i+2) (bitType.toByte v.z) sorry_proof
              b
            toByteArray_size := sorry_proof
            fromByteArray_toByteArray := sorry_proof
            fromByteArray_toByteArray_other := sorry_proof
                                            }
      | .inr byteType =>
          .inr {
            bytes := 3 * byteType.bytes
            h_size := sorry_proof
            fromByteArray := fun b i _ =>
              {
                x := byteType.fromByteArray b i sorry_proof
                y := byteType.fromByteArray b (i + byteType.bytes) sorry_proof
                z := byteType.fromByteArray b (i + 2 * byteType.bytes) sorry_proof
              }
            toByteArray := fun b i _ v => Id.run do
              let mut b := b
              b := byteType.toByteArray b i sorry_proof v.x
              b := byteType.toByteArray b (i + byteType.bytes) sorry_proof v.y
              b := byteType.toByteArray b (i + 2 * byteType.bytes) sorry_proof v.z
              b
            toByteArray_size := sorry_proof
            fromByteArray_toByteArray := sorry_proof
            fromByteArray_toByteArray_other := sorry_proof
          }

end Vec3


structure Vec4 (α : Type) where
  (x y z w : α)

namespace Vec4

  def get (v : Vec4 α) (i : Idx 4) : α :=
  if i = 0 then
    v.x
  else if i = 1 then
    v.y
  else if i = 2 then
    v.z
  else
    v.w

  def set (v : Vec4 α) (i : Idx 4) (vi : α) : Vec4 α :=
  if i = 0 then
    ⟨vi, v.y, v.z, v.w⟩
  else if i = 1 then
    ⟨v.x, vi, v.z, v.w⟩
  else if i = 2 then
    ⟨v.x, v.y, vi, v.w⟩
  else
    ⟨v.x, v.y, v.z, vi⟩

  def intro (f : Idx 4 → α) : Vec4 α := ⟨f 0, f 1, f 2, f 3⟩

  instance : GetElem (Vec4 α) (Idx 4) α (λ _ _ => True) where
    getElem v i _ := v.get i

  instance : SetElem (Vec4 α) (Idx 4) α where
    setElem v i xi := v.set i xi

  instance : IntroElem (Vec4 α) (Idx 4) α where
    introElem := intro

  instance : StructType (Vec4 α) (Idx 4) (fun _ => α) where
    structProj x i := x[i]
    structMake f := introElem f
    structModify i f x := setElem x i (f x[i])
    left_inv := sorry_proof
    right_inv := sorry_proof
    structProj_structModify  := sorry_proof
    structProj_structModify' := sorry_proof

  instance : ArrayType (Vec4 α) (Idx 4) α where
    getElem_structProj   := by intros; rfl
    setElem_structModify := by intros; rfl
    introElem_structMake := by intros; rfl

  instance [ba : PlainDataType α] : PlainDataType (Vec4 α) where
    btype :=
      match ba.btype with
      | .inl bitType  =>
        if h : 4 * bitType.bits ≤ 8 then
          .inl {
            bits := 4 * bitType.bits
            h_size := h
            fromByte := fun b =>
              let ones : UInt8 := 255
              let mask    := (ones - (ones <<< bitType.bits))   -- 00000111
              {
                x := bitType.fromByte (b &&& mask)
                y := bitType.fromByte ((b >>> bitType.bits) &&& mask)
                z := bitType.fromByte ((b >>> (2*bitType.bits) &&& mask))
                w := bitType.fromByte ((b >>> (3*bitType.bits) &&& mask))
              }
            toByte := fun v =>
              let x := bitType.toByte v.x
              let y := bitType.toByte v.y <<< bitType.bits
              let z := bitType.toByte v.z <<< (2 * bitType.bits)
              let w := bitType.toByte v.w <<< (3 * bitType.bits)
              (x ||| y ||| z ||| w)
            fromByte_toByte := sorry_proof
          }
        else
          .inr {
            bytes := 4
            h_size := sorry_proof
            fromByteArray := fun b i _ =>
              {
                x := bitType.fromByte (b.uget i sorry_proof)
                y := bitType.fromByte (b.uget (i+1) sorry_proof)
                z := bitType.fromByte (b.uget (i+2) sorry_proof)
                w := bitType.fromByte (b.uget (i+3) sorry_proof)
              }
            toByteArray := fun b i _ v => Id.run do
              let mut b := b
              b := b.uset  i    (bitType.toByte v.x) sorry_proof
              b := b.uset (i+1) (bitType.toByte v.y) sorry_proof
              b := b.uset (i+2) (bitType.toByte v.z) sorry_proof
              b := b.uset (i+3) (bitType.toByte v.w) sorry_proof
              b
            toByteArray_size := sorry_proof
            fromByteArray_toByteArray := sorry_proof
            fromByteArray_toByteArray_other := sorry_proof
                                            }
      | .inr byteType =>
          .inr {
            bytes := 3 * byteType.bytes
            h_size := sorry_proof
            fromByteArray := fun b i _ =>
              {
                x := byteType.fromByteArray b i sorry_proof
                y := byteType.fromByteArray b (i + byteType.bytes) sorry_proof
                z := byteType.fromByteArray b (i + 2 * byteType.bytes) sorry_proof
                w := byteType.fromByteArray b (i + 3 * byteType.bytes) sorry_proof
              }
            toByteArray := fun b i _ v => Id.run do
              let mut b := b
              b := byteType.toByteArray b i sorry_proof v.x
              b := byteType.toByteArray b (i + byteType.bytes) sorry_proof v.y
              b := byteType.toByteArray b (i + 2 * byteType.bytes) sorry_proof v.z
              b := byteType.toByteArray b (i + 3 * byteType.bytes) sorry_proof v.w
              b
            toByteArray_size := sorry_proof
            fromByteArray_toByteArray := sorry_proof
            fromByteArray_toByteArray_other := sorry_proof
          }
