import SciLean.Data.DataArray.DataArray

namespace SciLean

-- TODO: In the future this will be probably replaced by `α × α` but currently a struct like this has better performance(at least I was told so :)
structure Vec2 (α : Type) where 
  (x y : α)

structure Vec3 (α : Type) where 
  (x y z : α)

structure Vec4 (α : Type) where 
  (x y z w : α)

namespace Vec2 

  def get (v : Vec2 α) : Fin 2 → α 
    | ⟨0, _⟩ => v.x
    | ⟨1, _⟩ => v.y

  def set (v : Vec2 α) : Fin 2 → α → Vec2 α
    | ⟨0, _⟩, a => {v with x := a}
    | ⟨1, _⟩, a => {v with y := a}
    
  def intro (f : Fin 2 → α) : Vec2 α := ⟨f 0, f 1⟩

  instance : GetElem (Vec2 α) (Fin 2) α (λ _ _ => True) where
    getElem v i _ := v.get i

  instance : SetElem (Vec2 α) (Fin 2) α where
    setElem v i xi := v.set i xi

  instance : IntroElem (Vec2 α) (Fin 2) α where
    introElem := intro

end Vec2

namespace Vec3 

  def get (v : Vec3 α) : Fin 3 → α 
    | ⟨0, _⟩ => v.x
    | ⟨1, _⟩ => v.y
    | ⟨2, _⟩ => v.z

  def set (v : Vec3 α) : Fin 3 → α → Vec3 α
    | ⟨0, _⟩, a => {v with x := a}
    | ⟨1, _⟩, a => {v with y := a}
    | ⟨2, _⟩, a => {v with z := a}
    
  def intro (f : Fin 3 → α) : Vec3 α := ⟨f 0, f 1, f 2⟩

  instance : GetElem (Vec3 α) (Fin 3) α (λ _ _ => True) where
    getElem v i _ := v.get i

  instance : SetElem (Vec3 α) (Fin 3) α where
    setElem v i xi := v.set i xi

  instance : IntroElem (Vec3 α) (Fin 3) α where
    introElem := intro

end Vec3

namespace Vec4 

  def get (v : Vec4 α) : Fin 4 → α 
    | ⟨0, _⟩ => v.x
    | ⟨1, _⟩ => v.y
    | ⟨2, _⟩ => v.z
    | ⟨3, _⟩ => v.w

  def set (v : Vec4 α) : Fin 4 → α → Vec4 α
    | ⟨0, _⟩, a => {v with x := a}
    | ⟨1, _⟩, a => {v with y := a}
    | ⟨2, _⟩, a => {v with z := a}
    | ⟨3, _⟩, a => {v with w := a}
    
  def intro (f : Fin 4 → α) : Vec4 α := ⟨f 0, f 1, f 2, f 3⟩

  instance : GetElem (Vec4 α) (Fin 4) α (λ _ _ => True) where
    getElem v i _ := v.get i

  instance : SetElem (Vec4 α) (Fin 4) α where
    setElem v i xi := v.set i xi

  instance : IntroElem (Vec4 α) (Fin 4) α where
    introElem := intro


abbrev ShortOptDataArray (α : Type) [PlainDataType α] (n : Nat) := 
  match n with
  | 0 => Unit
  | 1 => α
  | 2 => Vec2 α
  | 3 => Vec3 α
  | 4 => Vec4 α
  | k+5 => DataArrayN α (Fin (k+5))

namespace ShortOptDataArray

  variable {α : Type} [PlainDataType α] {ι} [Enumtype ι]

  /-- 
  -/
  def get {n : Nat} (v : ShortOptDataArray α n) (i : Fin n) : α :=
  match n with
  | 0 => absurd (a:=True) sorry_proof sorry_proof -- impossible to have `i : Fin 0`
  | 1 => v
  | 2 => 
    match i with 
    | ⟨0, _⟩ => v.x     
    | ⟨1, _⟩ => v.y
  | 3 => 
    match i with 
    | ⟨0, _⟩ => v.x     
    | ⟨1, _⟩ => v.y     
    | ⟨2, _⟩ => v.z     
  | 4 => 
    match i with 
    | ⟨0, _⟩ => v.x     
    | ⟨1, _⟩ => v.y     
    | ⟨2, _⟩ => v.z     
    | ⟨3, _⟩ => v.w
  | _+5 => v.1.get ⟨i, sorry_proof⟩

  @[inline]
  instance : GetElem (ShortOptDataArray α n) (Fin n) α (λ _ _ => True) := 
    match n with
    | 0 => ⟨λ _ _ _ => absurd (a:=True) sorry_proof sorry_proof⟩
    | 1 => ⟨λ x _ _ => x⟩
    | 2 => by infer_instance
    | 3 => by infer_instance
    | 4 => by infer_instance
    | k+5 => by infer_instance

  @[inline]
  instance : GetElem (ShortOptDataArray α (numOf ι)) ι α (λ _ _ => True) where
    getElem v i _ := getElem v (toFin i) True.intro

  def set {n : Nat} (v : ShortOptDataArray α n) (i : Fin n) (xi : α) : ShortOptDataArray α n :=
  match n with
  | 0 => absurd (a:=True) sorry_proof sorry_proof -- impossible to have `i : Fin 0`
  | 1 => xi
  | 2 => 
    match i with 
    | ⟨0, _⟩ => {v with x := xi}
    | ⟨1, _⟩ => {v with y := xi}
  | 3 => 
    match i with 
    | ⟨0, _⟩ => {v with x := xi}
    | ⟨1, _⟩ => {v with y := xi}
    | ⟨2, _⟩ => {v with z := xi}
  | 4 => 
    match i with 
    | ⟨0, _⟩ => {v with x := xi}
    | ⟨1, _⟩ => {v with y := xi}
    | ⟨2, _⟩ => {v with z := xi}
    | ⟨3, _⟩ => {v with w := xi}
  | _+5 => ⟨v.1.set ⟨i, sorry_proof⟩ xi, sorry_proof⟩

  instance : SetElem (ShortOptDataArray α n) (Fin n) α :=
    match n with
    | 0 => ⟨λ _ _ _ => absurd (a:=True) sorry_proof sorry_proof⟩
    | 1 => ⟨λ x _ _ => x⟩
    | 2 => by infer_instance
    | 3 => by infer_instance
    | 4 => by infer_instance
    | k+5 => by infer_instance

  instance : SetElem (ShortOptDataArray α (numOf ι)) ι α where
    setElem v i xi := setElem v (toFin i) xi

  def intro {n : Nat} (f : Fin n → α) : ShortOptDataArray α n := 
    match n with
    | 0 => ()
    | 1 => f 0
    | 2 => 
      ⟨f 0, f 1⟩
    | 3 => 
      ⟨f 0, f 1, f 2⟩
    | 4 => 
      ⟨f 0, f 1, f 2, f 3⟩
    | _+5 => ⟨DataArray.intro f, sorry_proof⟩

  instance : IntroElem (ShortOptDataArray α n) (Fin n) α :=
    match n with
    | 0 => ⟨λ _  => absurd (a:=True) sorry_proof sorry_proof⟩
    | 1 => ⟨λ x => x 0⟩
    | 2 => by infer_instance
    | 3 => by infer_instance
    | 4 => by infer_instance
    | k+5 => by infer_instance

  instance : IntroElem (ShortOptDataArray α (numOf ι)) ι α where
    introElem f := intro (λ i => f (fromFin i))

  def push {n : Nat} (k : Nat) (x : α) (v : ShortOptDataArray α n) : ShortOptDataArray α (n + k) :=
    match n, n + k with
    | _, 0 => ()

    | 0, 1 => x
    | 0, 2 => ⟨x,x⟩
    | 0, 3 => ⟨x,x,x⟩
    | 0, 4 => ⟨x,x,x,x⟩

    | 1, 1 => v
    | 1, 2 => ⟨v,x⟩
    | 1, 3 => ⟨v, x, x⟩
    | 1, 4 => ⟨v, x, x, x⟩

    | 2, 2 => v
    | 2, 3 => ⟨v.x, v.y, x⟩
    | 2, 4 => ⟨v.x, v.y, x, x⟩

    | 3, 3 => v
    | 3, 4 => ⟨v.x, v.y, v.z, x⟩

    | 4, 4 => v

    | _+5, _+5 => ⟨v.1.push k x, sorry_proof⟩

    | _, m+5 => ⟨.intro λ (i : Fin (m + 5)) => if i < n then v.get ⟨i, sorry_proof⟩ else x, sorry_proof⟩

    -- This should be unreachable, how can I write the match statement to cover everything?
    | _, _ => 
      dbg_trace "Error: ShortOptDataArray.push unreachable code!"
      absurd (a := True) sorry_proof sorry_proof 

  instance : PushElem (ShortOptDataArray α) α where
    pushElem := push

  def drop {n : Nat} (k : Nat) (v : ShortOptDataArray α (n+k))  : ShortOptDataArray α n :=
    match n, k with
    | _, 0 => v

    | 0, _ => ()

    | 1, 1 => v.x
    | 1, 2 => v.x
    | 1, 3 => v.x
    | 1, _+4 => v.get ⟨0, sorry_proof⟩

    | 2, 1 => ⟨v.x, v.y⟩
    | 2, 2 => ⟨v.x, v.y⟩
    | 2, _+3 => ⟨v.get ⟨0,sorry_proof⟩, v.get ⟨1, sorry_proof⟩⟩

    | 3, 1 => ⟨v.x, v.y, v.z⟩
    | 3, _+2 => ⟨v.get ⟨0,sorry_proof⟩, v.get ⟨1, sorry_proof⟩, v.get ⟨2, sorry_proof⟩⟩

    | 4, _+1 => ⟨v.get ⟨0,sorry_proof⟩, v.get ⟨1, sorry_proof⟩, v.get ⟨2, sorry_proof⟩, v.get ⟨3, sorry_proof⟩⟩

    | n+5, _ => ⟨.intro λ (i : Fin (n + 5)) => v.get ⟨i,sorry_proof⟩, sorry_proof⟩

  instance : DropElem (ShortOptDataArray α) α where
    dropElem := drop

  def reserve {n : Nat} (k : Nat) (v : ShortOptDataArray α n) : ShortOptDataArray α n :=
    match n with
    | 0 | 1 | 2 | 3 | 4 => v
    | _+5 => ⟨v.1.reserve k, sorry_proof⟩

  instance : ReserveElem (ShortOptDataArray α) α where
    reserveElem := reserve

  -- instance : ArrayType (ShortOptDataArray α n) (Fin n) α  where
  --   ext := sorry_proof
  --   getElem_setElem_eq := sorry_proof
  --   getElem_setElem_neq := sorry_proof
  --   getElem_introElem := sorry_proof

  instance : ArrayType (ShortOptDataArray α (numOf ι)) ι α  where
    ext := sorry_proof
    getElem_setElem_eq := sorry_proof
    getElem_setElem_neq := sorry_proof
    getElem_introElem := sorry_proof

  -- instance : LinearArrayType (ShortOptDataArray α) α where
  --   toGenericArrayType := by infer_instance

  --   pushElem_getElem := sorry_proof
  --   dropElem_getElem := sorry_proof
  --   reserveElem_id := sorry_proof



  -- @[default_instance]
  -- instance {ι} [Enumtype ι] : PowType (ShortOptDataArray α (numOf ι)) ι α := PowType.mk

  -- @[default_instance]
  -- instance : LinearPowType (ShortOptDataArray α) α := LinearPowType.mk

end ShortOptDataArray
