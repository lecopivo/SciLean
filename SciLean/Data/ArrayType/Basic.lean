import SciLean.Util.SorryProof
import SciLean.Data.Index

namespace SciLean

class SetElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
  setElem : (cont : Cont) → (idx : Idx) → (elem : Elem) → Cont

export SetElem (setElem)

-- class ModifyElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
--   modifyElem : (x : Cont) → (i : Idx) → (f : Elem → Elem) → Cont

-- export ModifyElem (modifyElem)

class IntroElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
  introElem : (f : Idx → Elem) → Cont

export IntroElem (introElem)

class PushElem (Cont : USize → Type u) (Elem : outParam (Type w)) where
  pushElem (k : USize) (elem : Elem) : Cont n → Cont (n + k)

export PushElem (pushElem)

class DropElem (Cont : USize → Type u) (Elem : outParam (Type w)) where
  dropElem (k : USize) : Cont (n + k) → Cont n

export DropElem (dropElem)

class ReserveElem (Cont : USize → Type u) (Elem : outParam (Type w)) where
  reserveElem (k : USize) : Cont n → Cont n

export ReserveElem (reserveElem)

/-- This class says that `Cont` behaves like an array with `Elem` values indexed by `Idx`

Examples for `Idx = Fin n` and `Elem = ℝ` are: `ArrayN ℝ n` or `ℝ^{n}`

For `array : Cont` you can:
  1. get values: `getElem array x : Elem` for `x : Idx`
  2. set values: `setElem array x y : Cont` for `x : Idx` and `y : Elem`
  3. make new a array: `introElem f : Cont` for `f : Idx → Elem`

Alternative notation:
  1. `array[x]`
  2. in `do` block: `array[x] := y`, `array[x] += y`, ...
  3. `λ [x] => f x` this notation works only if the type `Cont` can be infered from the context
     Common use: `let array : Cont := λ [x] => f x` where the type asscription `: Cont` is important.
-/
class ArrayType (Cont : Type u) (Idx : Type v |> outParam) (Elem : Type w |> outParam)
  extends GetElem Cont Idx Elem (λ _ _ => True),
          SetElem Cont Idx Elem,
          IntroElem Cont Idx Elem
  where
  ext : ∀ f g : Cont, (∀ x : Idx, f[x] = g[x]) ↔ f = g
  getElem_setElem_eq  : ∀ (x : Idx) (y : Elem) (f : Cont), (setElem f x y)[x] = y
  getElem_setElem_neq : ∀ (i j : Idx) (val : Elem) (arr : Cont), i ≠ j → (setElem arr i val)[j] = arr[j]
  getElem_introElem : ∀ f i, (introElem f)[i] = f i

attribute [simp] ArrayType.getElem_setElem_eq ArrayType.getElem_introElem
attribute [default_instance] ArrayType.toGetElem ArrayType.toSetElem ArrayType.toIntroElem

class LinearArrayType (Cont : USize → Type u) (Elem : Type w |> outParam)
  extends PushElem Cont Elem,
          DropElem Cont Elem,
          ReserveElem Cont Elem
  where
  toArrayType : ∀ n, ArrayType (Cont n) (Idx n) Elem

  pushElem_getElem : ∀ n k val (i : Idx (n+k)) (x : Cont n), n ≤ i.1 → 
    have : ∀ n', GetElem (Cont n') (Idx n') Elem (λ _ _ => True) := λ n' => (toArrayType n').toGetElem
    (pushElem k val x)[i] = val

  dropElem_getElem : ∀ n k (i : Idx n) (x : Cont (n+k)), 
    have : ∀ n', GetElem (Cont n') (Idx n') Elem (λ _ _ => True) := λ n' => (toArrayType n').toGetElem
    (dropElem k x)[i] = x[(⟨i.1, sorry_proof⟩ : Idx (n+k))]

  reserveElem_id : ∀ (x : Cont n) (k), reserveElem k x = x
  

instance {T} {Y : outParam Type} [inst : LinearArrayType T Y] (n) : ArrayType (T n) (Idx n) Y := inst.toArrayType n

namespace ArrayType

variable {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam}

-- TODO: Make an inplace modification
-- Maybe turn this into a class and this is a default implementation
@[inline]
def modifyElem [GetElem Cont Idx Elem λ _ _ => True] [SetElem Cont Idx Elem]
  (arr : Cont) (i : Idx) (f : Elem → Elem) : Cont := 
  setElem arr i (f (arr[i]))

@[simp]
theorem getElem_modifyElem_eq [ArrayType Cont Idx Elem] (cont : Cont) (idx : Idx) (f : Elem → Elem)
  : (modifyElem cont idx f)[idx] = f cont[idx] := by simp[modifyElem]; done

@[simp]
theorem getElem_modifyElem_neq [inst : ArrayType Cont Idx Elem] (arr : Cont) (i j : Idx) (f : Elem → Elem)
  : i ≠ j → (modifyElem arr i f)[j] = arr[j] := by simp[modifyElem]; apply ArrayType.getElem_setElem_neq; done

-- Maybe turn this into a class and this is a default implementation
-- For certain types there might be a faster implementation
def mapIdx [ArrayType Cont Idx Elem] [Index Idx] (f : Idx → Elem → Elem) (arr : Cont) : Cont := Id.run do
  let mut arr := arr
  for i in fullRange Idx do
    arr := modifyElem arr i (f i)
  arr

@[simp]
theorem getElem_mapIdx [ArrayType Cont Idx Elem] [Index Idx] (f : Idx → Elem → Elem) (arr : Cont) (i : Idx)
  : (mapIdx f arr)[i] = f i arr[i] := sorry_proof

def map [ArrayType Cont Idx Elem] [Index Idx] (f : Elem → Elem) (arr : Cont) : Cont := 
  mapIdx (λ _ => f) arr

@[simp]
theorem getElem_map [ArrayType Cont Idx Elem] [Index Idx] (f : Elem → Elem) (arr : Cont) (i : Idx)
  : (map f arr)[i] = f arr[i] := sorry_proof

instance [ArrayType Cont Idx Elem] [ToString Elem] [EnumType Idx] : ToString (Cont) := ⟨λ x => Id.run do
  let mut fst := true
  let mut s := "["
  for i in fullRange Idx do
    if fst then
      s := s ++ toString x[i]
      fst := false
    else
      s := s ++ ", " ++ toString x[i]
  s ++ "]"⟩

section Operations

  variable [ArrayType Cont Idx Elem] [Index Idx] 

  instance [Add Elem] : Add Cont := ⟨λ f g => mapIdx (λ x fx => fx + g[x]) f⟩
  instance [Sub Elem] : Sub Cont := ⟨λ f g => mapIdx (λ x fx => fx - g[x]) f⟩
  instance [Mul Elem] : Mul Cont := ⟨λ f g => mapIdx (λ x fx => fx * g[x]) f⟩
  instance [Div Elem] : Div Cont := ⟨λ f g => mapIdx (λ x fx => fx / g[x]) f⟩

  -- instance {R} [HMul R Elem Elem] : HMul R Cont Cont := ⟨λ r f => map (λ fx => r*(fx : Elem)) f⟩
  instance {R} [SMul R Elem] : SMul R Cont := ⟨λ r f => map (λ fx => r•(fx : Elem)) f⟩

  instance [Neg Elem] : Neg Cont := ⟨λ f => map (λ fx => -(fx : Elem)) f⟩
  instance [Inv Elem] : Inv Cont := ⟨λ f => map (λ fx => (fx : Elem)⁻¹) f⟩

  instance [One Elem]  : One Cont  := ⟨introElem λ _ : Idx => 1⟩
  instance [Zero Elem] : Zero Cont := ⟨introElem λ _ : Idx => 0⟩

  instance [LT Elem] : LT Cont := ⟨λ f g => ∀ x, f[x] < g[x]⟩ 
  instance [LE Elem] : LE Cont := ⟨λ f g => ∀ x, f[x] ≤ g[x]⟩

  instance [DecidableEq Elem] : DecidableEq Cont := 
    λ f g => Id.run do
      let mut eq : Bool := true
      for x in fullRange Idx do
        if f[x] ≠ g[x] then
          eq := false
          break
      if eq then isTrue sorry_proof else isFalse sorry_proof

  instance [LT Elem] [∀ x y : Elem, Decidable (x < y)] (f g : Cont) : Decidable (f < g) := Id.run do
    let mut lt : Bool := true
    for x in fullRange Idx do
      if ¬(f[x] < g[x]) then
        lt := false
        break
    if lt then isTrue sorry_proof else isFalse sorry_proof

  instance [LE Elem] [∀ x y : Elem, Decidable (x ≤ y)] (f g : Cont) : Decidable (f ≤ g) := Id.run do
    let mut le : Bool := true
    for x in fullRange Idx do
      if ¬(f[x] ≤ g[x]) then
        le := false
        break
    if le then isTrue sorry_proof else isFalse sorry_proof

end Operations

end ArrayType


namespace ArrayType

  variable {Cont : USize → Type} {Elem : Type |> outParam}
  variable [LinearArrayType Cont Elem]

  def empty : Cont 0 := introElem λ i => 
    absurd (a := ∃ n : USize, n < 0) 
           (Exists.intro i.1 i.2) 
           (by intro h; have h' := h.choose_spec; cases h'; done)

  def split {n m : USize} (x : Cont (n+m)) : Cont n × Cont m :=
    (introElem λ i => x[⟨i.1,sorry_proof⟩],
     introElem λ i => x[⟨i.1+n,sorry_proof⟩])

  def append {n m : USize} (x : Cont n) (y : Cont m) : Cont (n+m) :=
    introElem λ i =>
      if i.1 < n
      then x[⟨i.1,sorry_proof⟩]
      else y[⟨i.1-n, sorry_proof⟩]

end ArrayType
