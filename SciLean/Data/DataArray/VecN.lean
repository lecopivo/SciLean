import SciLean.Data.DataArray.DataArray

open LeanColls

namespace SciLean


structure Vec2 where
  (x y : Float)
  deriving Inhabited

namespace Vec2

  -- !!!this is evil!!! you can't have arrays named v!
  notation "v[" x ", " y "]" => Vec2.mk x y

  def get (v : Vec2) (i : Fin 2) : Float :=
    if i.1 = 0 then
      v.x
    else
      v.y

  def set (v : Vec2) (i : Fin 2) (vi : Float) : Vec2 :=
    if i.1 = 0 then
      ⟨vi, v.y⟩
    else
      ⟨v.x, vi⟩

  def intro (f : Fin 2 → Float) : Vec2 := ⟨f 0, f 1⟩

  def normalize (v : Vec2) : Vec2 :=
    let r := (v.x*v.x + v.y*v.y).sqrt
    let ir := 1/r
    if r != 0 then
      v[ir*v.x,ir*v.y]
    else
      v[1,0]


  instance : StructType Vec2 (Fin 2) (fun _ => Float) where
    structProj := get
    structMake := intro
    structModify i f x := set x i (f (get x i))
    left_inv := sorry_proof
    right_inv := sorry_proof
    structProj_structModify  := sorry_proof
    structProj_structModify' := sorry_proof

  instance : Indexed Vec2 (Fin 2) Float where
    mem x u := (x = u.x) ∨ (x = u.y)
    toMultiset u := .ofList [u.x,u.y]
    toMultiBagWithIdx := {
      mem := fun (i,x) u => x = get u.1 i
      toMultiset := fun u => .ofList [(0,u.1.x), (1,u.1.y)]
      fold := fun u f init => (f (f init (0,u.1.x)) (1,u.1.y))
      size := 2}
    fold u f init := f (f init u.x) u.y
    ofFn := intro
    get := get
    update u i f := set u i (f (get u i))

  instance : ArrayType Vec2 (Fin 2) Float where
    get_injective := sorry_proof
    get_ofFn := sorry_proof
    get_set_eq := sorry_proof
    get_set_ne := sorry_proof
    get_update_eq := sorry_proof
    get_update_ne := sorry_proof

  instance : PlainDataType Vec2 where
    btype := .inr {
      bytes := 2 * Float.byteType.bytes
      h_size := sorry_proof
      fromByteArray := fun b i _ =>
        {
          x := Float.byteType.fromByteArray b i sorry_proof
          y := Float.byteType.fromByteArray b (i + Float.byteType.bytes) sorry_proof
        }
      toByteArray := fun b i _ v => Id.run do
        let mut b := b
        b := Float.byteType.toByteArray b i sorry_proof v.x
        b := Float.byteType.toByteArray b (i + Float.byteType.bytes) sorry_proof v.y
        b
      toByteArray_size := sorry_proof
      fromByteArray_toByteArray := sorry_proof
      fromByteArray_toByteArray_other := sorry_proof
    }

end Vec2


structure Vec3 where
  (x y z : Float)
  deriving Inhabited

namespace Vec3

  -- !!!this is evil!!! you can't have arrays named v!
  notation "v[" x ", " y ", " z "]" => Vec3.mk x y z

  def get (v : Vec3) (i : Fin 3) : Float :=
    if i.1 = 0 then
      v.x
    else if i.1 = 1 then
      v.y
    else
      v.z

  def set (v : Vec3) (i : Fin 3) (vi : Float) : Vec3 :=
    if i.1 = 0 then
      v[vi, v.y, v.z]
    else if i.1 = 1 then
      v[v.x, vi, v.z]
    else
      v[v.x, v.y, vi]

  def intro (f : Fin 3 → Float) : Vec3 := v[f 0, f 1, f 2]

  def normalize (v : Vec3) : Vec3 :=
    let r := (v.x*v.x + v.y*v.y + v.z*v.z).sqrt
    let ir := 1/r
    if r != 0 then
      v[ir*v.x,ir*v.y,ir*v.z]
    else
      v[1,0,0]

  instance : StructType Vec3 (Fin 3) (fun _ => Float) where
    structProj := get
    structMake := intro
    structModify i f x := set x i (f (get x i))
    left_inv := sorry_proof
    right_inv := sorry_proof
    structProj_structModify  := sorry_proof
    structProj_structModify' := sorry_proof

  instance : Indexed Vec3 (Fin 3) Float where
    mem x u := (x = u.x) ∨ (x = u.y)
    toMultiset u := .ofList [u.x,u.y]
    toMultiBagWithIdx := {
      mem := fun (i,x) u => x = get u.1 i
      toMultiset := fun u => .ofList [(0,u.1.x), (1,u.1.y), (2, u.1.z)]
      fold := fun u f init => f (f (f init (0,u.1.x)) (1,u.1.y)) (2,u.1.z)
      size := 3}
    fold u f init := f (f (f init u.x) u.y) u.z
    ofFn := intro
    get := get
    update u i f := set u i (f (get u i))


  instance : ArrayType Vec3 (Fin 3) Float where
    get_injective := sorry_proof
    get_ofFn := sorry_proof
    get_set_eq := sorry_proof
    get_set_ne := sorry_proof
    get_update_eq := sorry_proof
    get_update_ne := sorry_proof


  instance : PlainDataType Vec3 where
    btype := .inr {
      bytes := 2 * Float.byteType.bytes
      h_size := sorry_proof
      fromByteArray := fun b i _ =>
        {
          x := Float.byteType.fromByteArray b i sorry_proof
          y := Float.byteType.fromByteArray b (i + Float.byteType.bytes) sorry_proof
          z := Float.byteType.fromByteArray b (i + 2*Float.byteType.bytes) sorry_proof
        }
      toByteArray := fun b i _ v => Id.run do
        let mut b := b
        b := Float.byteType.toByteArray b i sorry_proof v.x
        b := Float.byteType.toByteArray b (i + Float.byteType.bytes) sorry_proof v.y
        b := Float.byteType.toByteArray b (i + 2*Float.byteType.bytes) sorry_proof v.z
        b
      toByteArray_size := sorry_proof
      fromByteArray_toByteArray := sorry_proof
      fromByteArray_toByteArray_other := sorry_proof
    }


end Vec3


----------------------------------------------------------------------------------------------------
-- Useful functions involving Vec ------------------------------------------------------------------

def det2 (A : Vec2 → Vec2) : Float :=
  let u := A v[1,0]
  let v := A v[0,1]
  u.x * v.y - u.y * v.x

def det3 (A : Vec3 → Vec3) : Float :=
  let u := A v[1,0,0]
  let v := A v[0,1,0]
  let w := A v[0,0,1]
  u.x * (v.y * w.z - v.z * w.y)
  - u.y * (v.x * w.z - v.z * w.x)
  + u.z * (v.x * w.y - v.y * w.x)
