import SciLean.Util.SorryProof
import SciLean.Data.Index
import SciLean.Data.ListN 
import SciLean.Data.StructType.Basic
import SciLean.Data.Function

namespace SciLean

class SetElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
  setElem : (cont : Cont) → (idx : Idx) → (elem : Elem) → Cont

export SetElem (setElem)
attribute [irreducible] setElem

-- class ModifyElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
--   modifyElem : (x : Cont) → (i : Idx) → (f : Elem → Elem) → Cont

-- export ModifyElem (modifyElem)

class IntroElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
  introElem : (f : Idx → Elem) → Cont

export IntroElem (introElem)
attribute [irreducible] introElem 

class PushElem (Cont : USize → Type u) (Elem : outParam (Type w)) where
  pushElem (k : USize) (elem : Elem) : Cont n → Cont (n + k)

export PushElem (pushElem)
attribute [irreducible] pushElem

class DropElem (Cont : USize → Type u) (Elem : outParam (Type w)) where
  dropElem (k : USize) : Cont (n + k) → Cont n

export DropElem (dropElem)
attribute [irreducible] dropElem

class ReserveElem (Cont : USize → Type u) (Elem : outParam (Type w)) where
  reserveElem (k : USize) : Cont n → Cont n

export ReserveElem (reserveElem)
attribute [irreducible] reserveElem


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
          IntroElem Cont Idx Elem,
          StructType Cont Idx (fun _ => Elem)
  where
  getElem_structProj   : ∀ (x : Cont) (i : Idx), x[i] = structProj x i
  setElem_structModify : ∀ (x : Cont) (i : Idx) (xi : Elem), setElem x i xi = structModify i (fun _ => xi) x
  introElem_structMake : ∀ (f : Idx → Elem), introElem f = structMake f

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

variable 
  {Cont : Type} {Idx : Type |> outParam} {Elem : Type |> outParam}
  [ArrayType Cont Idx Elem]

@[ext]
theorem ext (x y : Cont) : (∀ i, x[i] = y[i]) → x = y := 
by
  intros h
  apply structExt (I:=Idx)
  simp[getElem_structProj] at h
  exact h

@[simp] 
theorem getElem_setElem_eq (i : Idx) (xi : Elem) (x : Cont)
  : (setElem x i xi)[i] = xi :=
by
  simp[setElem_structModify, getElem_structProj]

@[simp] 
theorem getElem_setElem_neq (i j : Idx) (xi : Elem) (x : Cont)
  : (i≠j) → (setElem x i xi)[j] = x[j] :=
by
  intro h
  simp (discharger:=assumption) [setElem_structModify, getElem_structProj]

@[simp]
theorem getElem_introElem (f : Idx → Elem) (i : Idx)
  : (introElem (Cont:=Cont) f)[i] = f i :=
by
  simp[introElem_structMake, getElem_structProj]

@[simp]
theorem introElem_getElem [ArrayType Cont Idx Elem] (cont : Cont)
  : introElem (Cont:=Cont) (fun i => cont[i]) = cont := by ext; simp

-- TODO: Make an inplace modification
-- Maybe turn this into a class and this is a default implementation
def _root_.SciLean.modifyElem [GetElem Cont Idx Elem λ _ _ => True] [SetElem Cont Idx Elem]
  (arr : Cont) (i : Idx) (f : Elem → Elem) : Cont := 
  let xi := arr[i]
  setElem arr i (f xi)

@[simp]
theorem getElem_modifyElem_eq [ArrayType Cont Idx Elem] (cont : Cont) (idx : Idx) (f : Elem → Elem)
  : (modifyElem cont idx f)[idx] = f cont[idx] := by simp[getElem_structProj,modifyElem,setElem_structModify]; done

@[simp]
theorem getElem_modifyElem_neq [inst : ArrayType Cont Idx Elem] (arr : Cont) (i j : Idx) (f : Elem → Elem)
  : i ≠ j → (modifyElem arr i f)[j] = arr[j] := by intro h; simp [h,modifyElem, getElem_structProj,modifyElem,setElem_structModify]; done


-- Maybe turn this into a class and this is a default implementation
-- For certain types there might be a faster implementation
def mapIdx [ArrayType Cont Idx Elem] [EnumType Idx] (f : Idx → Elem → Elem) (arr : Cont) : Cont := Id.run do
  let mut arr := arr
  for i in fullRange Idx do
    arr := modifyElem arr i (f i)
  arr

@[simp]
theorem getElem_mapIdx [ArrayType Cont Idx Elem] [EnumType Idx] (f : Idx → Elem → Elem) (arr : Cont) (i : Idx)
  : (mapIdx f arr)[i] = f i arr[i] := sorry_proof

def map [ArrayType Cont Idx Elem] [EnumType Idx] (f : Elem → Elem) (arr : Cont) : Cont := 
  mapIdx (λ _ => f) arr

@[simp]
theorem getElem_map [ArrayType Cont Idx Elem] [EnumType Idx] (f : Elem → Elem) (arr : Cont) (i : Idx)
  : (map f arr)[i] = f arr[i] := sorry_proof

instance (priority:=low) [ArrayType Cont Idx Elem] [ToString Elem] [EnumType Idx] : ToString (Cont) := ⟨λ x => Id.run do
  let mut fst := true
  let mut s := "⊞["
  for i in fullRange Idx do
    if fst then
      s := s ++ toString x[i]
      fst := false
    else
      s := s ++ ", " ++ toString x[i]
  s ++ "]"⟩

/-- Converts array to ArrayType

  WARNING: Does not do what expected for arrays of size bigger or equal then USize.size
    For example, array of size USize.size is converted to an array of size zero
  -/
def _root_.Array.toArrayType {n Elem} (Cont : Type u) [ArrayType Cont (SciLean.Idx n) Elem]
  (a : Array Elem) (_h : n = a.size.toUSize) : Cont := 
  introElem fun (i : SciLean.Idx n) => a[i.1]'sorry_proof

/-- Converts ListN to ArrayType

  WARNING: Does not do what expected for lists of size bigger or equal then USize.size
    For example, array of size USize.size is converted to an array of size zero
  -/
def _root_.ListN.toArrayType {n Elem} (Cont : Type) [ArrayType Cont (SciLean.Idx (n.toUSize)) Elem] 
  (l : ListN Elem n) : Cont := 
  introElem fun i => l.toArray[i.1.toNat]'sorry_proof

instance {Cont Idx Elem} [ArrayType Cont Idx Elem] [StructType Elem I ElemI] : StructType Cont (Idx×I) (fun (_,i) => ElemI i) where
  structProj := fun x (i,j) => structProj x[i] j
  structMake := fun f => introElem fun i => structMake fun j => f (i,j)
  structModify := fun (i,j) f x => modifyElem x i (fun xi => structModify j f xi)
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  structProj_structModify := by intro x; simp
  structProj_structModify' := by intro (i,j) (i',j') _ _ h; sorry_proof


section Operations

  variable [ArrayType Cont Idx Elem] [EnumType Idx] 

  instance (priority:=low) [Add Elem] : Add Cont := ⟨λ f g => mapIdx (λ x fx => fx + g[x]) f⟩
  instance (priority:=low) [Sub Elem] : Sub Cont := ⟨λ f g => mapIdx (λ x fx => fx - g[x]) f⟩
  instance (priority:=low) [Mul Elem] : Mul Cont := ⟨λ f g => mapIdx (λ x fx => fx * g[x]) f⟩
  instance (priority:=low) [Div Elem] : Div Cont := ⟨λ f g => mapIdx (λ x fx => fx / g[x]) f⟩

  -- instance (priority:=low) {R} [HMul R Elem Elem] : HMul R Cont Cont := ⟨λ r f => map (λ fx => r*(fx : Elem)) f⟩
  instance (priority:=low) {R} [SMul R Elem] : SMul R Cont := ⟨λ r f => map (λ fx => r•(fx : Elem)) f⟩

  instance (priority:=low) [Neg Elem] : Neg Cont := ⟨λ f => map (λ fx => -(fx : Elem)) f⟩
  instance (priority:=low) [Inv Elem] : Inv Cont := ⟨λ f => map (λ fx => (fx : Elem)⁻¹) f⟩

  instance (priority:=low) [One Elem]  : One Cont  := ⟨introElem λ _ : Idx => 1⟩
  instance (priority:=low) [Zero Elem] : Zero Cont := ⟨introElem λ _ : Idx => 0⟩

  instance (priority:=low) [LT Elem] : LT Cont := ⟨λ f g => ∀ x, f[x] < g[x]⟩ 
  instance (priority:=low) [LE Elem] : LE Cont := ⟨λ f g => ∀ x, f[x] ≤ g[x]⟩

  instance (priority:=low) [DecidableEq Elem] : DecidableEq Cont := 
    λ f g => Id.run do
      let mut eq : Bool := true
      for x in fullRange Idx do
        if f[x] ≠ g[x] then
          eq := false
          break
      if eq then isTrue sorry_proof else isFalse sorry_proof

  instance (priority:=low) [LT Elem] [∀ x y : Elem, Decidable (x < y)] (f g : Cont) : Decidable (f < g) := Id.run do
    let mut lt : Bool := true
    for x in fullRange Idx do
      if ¬(f[x] < g[x]) then
        lt := false
        break
    if lt then isTrue sorry_proof else isFalse sorry_proof

  instance (priority:=low) [LE Elem] [∀ x y : Elem, Decidable (x ≤ y)] (f g : Cont) : Decidable (f ≤ g) := Id.run do
    let mut le : Bool := true
    for x in fullRange Idx do
      if ¬(f[x] ≤ g[x]) then
        le := false
        break
    if le then isTrue sorry_proof else isFalse sorry_proof

  @[simp]
  theorem add_introElem {Cont Idx Elem : Type _} [ArrayType Cont Idx Elem] [Add Elem] [EnumType Idx] (f g: Idx → Elem)
    : introElem (Cont:=Cont) f + introElem (Cont:=Cont) g
      = 
      introElem fun i => f i + g i  := by ext; simp[HAdd.hAdd, Add.add]

  @[simp]
  theorem sub_introElem {Cont Idx Elem : Type _} [ArrayType Cont Idx Elem] [Sub Elem] [EnumType Idx] (f g: Idx → Elem)
    : introElem (Cont:=Cont) f - introElem (Cont:=Cont) g
      = 
      introElem fun i => f i - g i  := by ext; simp[HSub.hSub, Sub.sub]

  @[simp]
  theorem neg_introElem {Cont Idx Elem : Type _} [ArrayType Cont Idx Elem] [Neg Elem] [EnumType Idx] (f: Idx → Elem)
    : - introElem (Cont:=Cont) f 
      = 
      introElem fun i => - f i  := by ext; simp[Neg.neg]

  @[simp]
  theorem smul_introElem {K Cont Idx Elem : Type _} [ArrayType Cont Idx Elem] [SMul K Elem] [EnumType Idx] (f : Idx → Elem) (a : K)
    : a • introElem (Cont:=Cont) f
      = 
      introElem fun i => a • f i := by ext; simp[HSMul.hSMul, SMul.smul]

end Operations

@[simp]
theorem sum_introElem [EnumType Idx] [ArrayType Cont Idx Elem] [AddCommMonoid Elem] {ι} [EnumType ι] (f : ι → Idx → Elem)
  : ∑ j, introElem (Cont:=Cont) (fun i => f j i)
    =
    introElem fun i => ∑ j, f j i
  := sorry_proof


section UsefulFunctions


variable 
  [ArrayType Cont Idx Elem] [Index Idx]
  [LT Elem] [∀ x y : Elem, Decidable (x < y)] [Inhabited Idx] 

def argMaxCore (cont : Cont ) : Idx × Elem :=
  Function.reduceD 
    (fun i => (i,cont[i]))
    (fun (i,e) (i',e') => if e < e' then (i',e') else (i,e))
    (default, cont[default])

def max (cont : Cont) : Elem :=
  Function.reduceD 
    (fun i => cont[i])
    (fun e e' => if e < e' then e' else e)
    (cont[default])

def idxMax (cont : Cont) : Idx := (argMaxCore cont).1


def argMinCore (cont : Cont ) : Idx × Elem :=
  Function.reduceD 
    (fun i => (i,cont[i]))
    (fun (i,e) (i',e') => if e' < e then (i',e') else (i,e))
    (default, cont[default])

def min (cont : Cont) : Elem :=
  Function.reduceD 
    (fun i => cont[i])
    (fun e e' => if e < e' then e' else e)
    (cont[default])

def idxMin (cont : Cont) : Idx := (argMinCore cont).1

end UsefulFunctions


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

